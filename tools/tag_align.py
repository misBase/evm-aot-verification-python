"""EVM pc ↔ x86 地址的权威映射（docs/块级lockstep等价验证方案.md §3.1）。

块级 lock-step 分解的地基：每个 EVM basic block 对应一段 x86 地址区间。本模块用
``compileEVMTag``（``$GOPATH/src/github.com/bcds/go-hpc-evm/evm/aot/impl_amd64.go``）
发射的 12 条固定序言做指纹，与 EVM 块按 pc 升序 / x86 地址升序单调对齐：

    mov  TMP, [r13+gas_remaining]     ; makeStaticUseGas 前缀 ↓
    cmp  TMP, staticGas
    jb   <OutOfGas>
    sub  TMP, staticGas
    mov  [r13+gas_remaining], TMP     ; makeStaticUseGas 前缀 ↑
    mov  TMP, [r13+stack_byte_offset] ; compileEVMTag 栈深检查 ↓
    cmp  TMP, minDepth*32
    jb   <StackUnderflow>
    cmp  TMP, maxDepth*32+1
    jae  <StackReachLimit>
    mov  r14, [r13+stack_base]        ; 重建保留寄存器 ↓
    add  r14, TMP

取三元组 ``(static_gas, min_depth*32, max_depth*32+1)`` 作指纹，实测三合约全覆盖、
逐位一致：ENSRegistry 127/127、CErc20 723/723、Safe 742/742。

**为什么必须是完整 12 条**：前 3 条（``mov/cmp/jb``）只是 ``makeStaticUseGas`` 的
公共前缀，动态 gas 路径（``checkMemoryAndCalcDynamicGas*``）也生成同样三条，过匹配
约 2.1×（CErc20 命中 ~1523 vs 真实 723）。``x86_64/loop_analysis.py`` 的
``is_evm_tag_header`` 用的是收紧后的 8 条跨块判据，够它判"循环头是不是 EVM 块边界"；
本模块要读出**全部三个立即数**才能与 IR 侧比对，所以必须走完 12 条。

**这一层是结构性证据，不是定理**（方案 §2.5）。判别力来自"数量相等 + 逐位一致 +
返回链锚点独立交叉校验 + 区间完全覆盖"这四重记账，而不是任何被证明的性质——注意
指纹三元组在同一合约内**并非两两不同**（实测 ENS 127 块只有 65 个不同三元组，最大
重数 17；CErc20 723/304/55；Safe 742/350/79），单调序才是主要信息来源，这也是为什
么本模块不做"按指纹查表"而只做"按序 zip 再逐位核对"。既然没有定理兜底，唯一的兜底
就是 fail-closed：**任何一位对不上就整体拒绝，不做局部修补**（方案 §2.4 ④(c)）。
"""

import bisect
import hashlib
import re
from dataclasses import dataclass
from typing import (
    Dict,
    List,
    Mapping,
    Optional,
    Sequence,
    Tuple,
)

from evm_ir.models import EVMBlock
from x86_64.aot_profile import GO_HPC_EVM_PROFILE
from x86_64.cfg import identify_basic_blocks
from x86_64.models import X86Block, X86Instruction


__all__ = [
    "TAG_ALIGN_SCHEMA_VERSION",
    "TAG_PROLOGUE_LENGTH",
    "TagFingerprint",
    "TagPrologue",
    "ReturnChainAnchor",
    "AlignmentEvidence",
    "BlockAlignment",
    "BlockAlignmentError",
    "REASON_EMPTY_INPUT",
    "REASON_EVM_PC_NOT_MONOTONIC",
    "REASON_TAG_COUNT_MISMATCH",
    "REASON_FINGERPRINT_MISMATCH",
    "REASON_ANCHOR_DISAGREEMENT",
    "REASON_INTERVAL_NOT_MONOTONIC",
    "REASON_INTERVAL_NOT_BLOCK_ALIGNED",
    "REASON_INSTRUCTION_UNCOVERED",
    "find_tag_prologues",
    "extract_return_chain_anchors",
    "evm_block_fingerprint",
    "build_block_alignment",
]


# 指纹 / 覆盖记账的编码版本。任何影响 ``BlockAlignment.fingerprint`` 语义的改动都要
# 提升它，否则旧证书会在新语义下被误判为仍然有效。
TAG_ALIGN_SCHEMA_VERSION = 1

# compileEVMTag 序言的指令条数（去 nop 后）。
TAG_PROLOGUE_LENGTH = 12

_MASK64 = (1 << 64) - 1
_SIGN64 = 1 << 63

# EVM 栈元素字节宽度；codegen 的 stack_byte_offset 以字节计，IR 的 depth 以元素计。
_STACK_ELEMENT_BYTES = 32

# callEngine 字段偏移按名字取，不在正则里写死——改 profile 时只有一处要跟。
_GAS_OFFSET = GO_HPC_EVM_PROFILE.offsets["gas_remaining"]
_STACK_BYTE_OFFSET = GO_HPC_EVM_PROFILE.offsets["stack_byte_offset"]
_STACK_BASE_OFFSET = GO_HPC_EVM_PROFILE.offsets["stack_base"]

# 同一条 x86 指令在 Capstone 下的别名：JCS 可能印成 jb 或 jc，JCC 印成 jae/jnb/jnc。
_JB_MNEMONICS = frozenset({"jb", "jc", "jnae"})
_JAE_MNEMONICS = frozenset({"jae", "jnb", "jnc"})
_JE_MNEMONICS = frozenset({"je", "jz"})

# `cmp REG, IMM` 形状。立即数允许负号：maxDepth 初值是 Go 的 math.MaxInt64，
# maxDepth*32+1 回绕后 Capstone 可能印成负数或 0xffff... 两种形式，统一到 signed。
_REG_IMM_RE = re.compile(r"^(\w+),\s*(-?(?:0x[0-9a-fA-F]+|\d+))$")
_GAS_LOAD_RE = re.compile(r"^(\w+),\s*qword ptr \[r13 \+ 0x%x\]$" % _GAS_OFFSET)
_GAS_STORE_RE = re.compile(r"^qword ptr \[r13 \+ 0x%x\],\s*(\w+)$" % _GAS_OFFSET)
_DEPTH_LOAD_RE = re.compile(
    r"^(\w+),\s*qword ptr \[r13 \+ 0x%x\]$" % _STACK_BYTE_OFFSET
)
_STACK_BASE_LOAD_RE = re.compile(
    r"^r14,\s*qword ptr \[r13 \+ 0x%x\]$" % _STACK_BASE_OFFSET
)
_ADD_R14_RE = re.compile(r"^r14,\s*(\w+)$")
_ABS_TARGET_RE = re.compile(r"^(0x[0-9a-fA-F]+)$")


# ---------------------------------------------------------------------------
# 失败语义：fail-closed
# ---------------------------------------------------------------------------

REASON_EMPTY_INPUT = "empty_input"
REASON_EVM_PC_NOT_MONOTONIC = "evm_pc_not_monotonic"
REASON_TAG_COUNT_MISMATCH = "tag_count_mismatch"
REASON_FINGERPRINT_MISMATCH = "fingerprint_mismatch"
REASON_ANCHOR_DISAGREEMENT = "anchor_disagreement"
REASON_INTERVAL_NOT_MONOTONIC = "interval_not_monotonic"
REASON_INTERVAL_NOT_BLOCK_ALIGNED = "interval_not_block_aligned"
REASON_INSTRUCTION_UNCOVERED = "instruction_uncovered"


class BlockAlignmentError(Exception):
    """映射构造失败。

    **没有"部分映射"这个返回值。** 上游（三参数专门化、块图编排）会把映射当作
    ``block_pairing`` 分量的前提直接使用，一个静默错位的条目就是一处假绿；而对齐错
    误本身是安全方向的（证不出来 ⇒ 假红）只在"映射整体被拒绝"时才成立。
    """

    def __init__(self, reason: str, message: str) -> None:
        super().__init__("[%s] %s" % (reason, message))
        self.reason = reason
        self.message = message


# ---------------------------------------------------------------------------
# 数据结构
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class TagFingerprint:
    """TAG 序言里的三个立即数，两侧比对的全部内容。

    ``min_depth_bytes`` / ``max_depth_bound`` 已归一到 signed int64，与 codegen 发
    射的立即数编码无关（见 ``_to_signed64``）。
    """

    static_gas: int
    min_depth_bytes: int  # min_depth * 32
    max_depth_bound: int  # max_depth * 32 + 1

    def as_tuple(self) -> Tuple[int, int, int]:
        return (self.static_gas, self.min_depth_bytes, self.max_depth_bound)


@dataclass(frozen=True)
class TagPrologue:
    """x86 侧命中的一处 TAG 序言。"""

    addr: int  # 序言第一条 mov 的地址（label NOP 被汇编器 optimize out，0 字节）
    fingerprint: TagFingerprint
    temp_register: str  # allocateRegisters 分配的临时寄存器，并非恒为 rax


@dataclass(frozen=True)
class ReturnChainAnchor:
    """动态 JUMP 下降链上的一处 ``cmp REG, $pc`` + ``je <addr>``。

    与 TAG 指纹**相互独立**的第二个证据源：立即数是 EVM 目标 pc，je 的 rel32 目标是
    对应的 x86 地址（纯立即数编码、无跳转表）。
    """

    evm_pc: int
    x86_addr: int


@dataclass(frozen=True)
class AlignmentEvidence:
    """构造过程的记账，供证书与回归断言读取（本模块不打印任何东西）。"""

    evm_block_count: int
    tag_count: int
    # 指纹三元组的去重数与最大重数：诚实记录"三元组并非两两不同"这一事实，
    # 说明判别力来自单调序而非指纹唯一性（见模块 docstring）。
    distinct_fingerprints: int
    max_fingerprint_multiplicity: int
    # 落在 TAG 头上、且与指纹映射一致的锚点（去重、按 pc 升序）。
    anchors_on_tag: Tuple[ReturnChainAnchor, ...]
    # 目标不是任何 TAG 头的 cmp/je 对数（普通比较，不参与校验，仅记账）。
    anchors_off_tag: int
    basic_block_total: int
    basic_block_covered: int
    # 跨越"非块区域 → 首个块区间"边界的 basic block 起始地址。入口处恒有一个（保留寄
    # 存器序言与第一个 TAG 的头三条指令同属一个 bb），显式登记而不是静默计入覆盖。
    straddling_basic_blocks: Tuple[int, ...]
    code_range: Tuple[int, int]  # [start, end)

    @property
    def anchor_agreement_count(self) -> int:
        return len(self.anchors_on_tag)


@dataclass(frozen=True)
class BlockAlignment:
    """EVM pc ↔ x86 地址的权威映射，以及它的区间划分。

    构造成功即意味着四条记账全部通过：数量相等、逐位指纹一致、返回链锚点 100% 吻合、
    区间两两不重叠且完全覆盖代码段。
    """

    pc_to_addr: Mapping[int, int]
    addr_to_pc: Mapping[int, int]
    intervals: Mapping[int, Tuple[int, int]]  # pc -> [start, end)
    # 显式登记的非块代码。目前唯一的合法成员是第一个 TAG 之前的保留寄存器序言
    # （compileReservedStackBasePointerInitialization / ...MemoryPointer...，12 字节）。
    # 它必须被登记而不是默默漏掉：④(b) 要求每条指令恰属于一个区间，"落在所有区间外"
    # 与"落在已登记的非块区间内"是两种结论，前者 fail-closed。
    non_block_regions: Tuple[Tuple[int, int], ...]
    fingerprints: Mapping[int, TagFingerprint]  # pc -> 该块的 TAG 指纹
    evidence: AlignmentEvidence
    fingerprint: str  # 进证书 key，codegen 变更后自动失效

    def __len__(self) -> int:
        return len(self.pc_to_addr)

    def interval_of_pc(self, pc: int) -> Tuple[int, int]:
        return self.intervals[pc]

    def pc_at_addr(self, addr: int) -> Optional[int]:
        """``addr`` 若是某个块的入口地址则返回其 pc，否则 None。"""
        return self.addr_to_pc.get(addr)


# ---------------------------------------------------------------------------
# 指纹提取
# ---------------------------------------------------------------------------


def _to_signed64(value: int) -> int:
    value &= _MASK64
    return value - (1 << 64) if value >= _SIGN64 else value


def _match_reg_imm(op_str: str, register: Optional[str] = None) -> Optional[int]:
    match = _REG_IMM_RE.match(op_str)
    if match is None:
        return None
    if register is not None and match.group(1) != register:
        return None
    return int(match.group(2), 0)


def _match_tag_at(
    stream: Sequence[X86Instruction], index: int
) -> Optional[TagPrologue]:
    """在**去 nop** 的指令流上从 ``index`` 起匹配 12 条序言。

    临时寄存器由 ``allocateRegisters`` 分配、并非恒为 rax，因此从第一条 mov 里读出来
    再要求后续 11 条全部用同一个寄存器——这是把"公共前缀"和"完整序言"分开的关键，
    也顺带排除了两处不相关序言在流上恰好相邻的可能。
    """
    if index + TAG_PROLOGUE_LENGTH > len(stream):
        return None
    window = stream[index : index + TAG_PROLOGUE_LENGTH]

    if window[0].mnemonic != "mov":
        return None
    gas_load = _GAS_LOAD_RE.match(window[0].op_str)
    if gas_load is None:
        return None
    temp = gas_load.group(1)

    if window[1].mnemonic != "cmp":
        return None
    static_gas = _match_reg_imm(window[1].op_str, temp)
    if static_gas is None:
        return None

    if window[2].mnemonic not in _JB_MNEMONICS:
        return None

    # 同一次 makeStaticUseGas 调用的 CMPQ 与 SUBQ 用的是同一个常量。
    if window[3].mnemonic != "sub" or _match_reg_imm(window[3].op_str, temp) != static_gas:
        return None

    if window[4].mnemonic != "mov":
        return None
    gas_store = _GAS_STORE_RE.match(window[4].op_str)
    if gas_store is None or gas_store.group(1) != temp:
        return None

    if window[5].mnemonic != "mov":
        return None
    depth_load = _DEPTH_LOAD_RE.match(window[5].op_str)
    if depth_load is None or depth_load.group(1) != temp:
        return None

    if window[6].mnemonic != "cmp":
        return None
    min_imm = _match_reg_imm(window[6].op_str, temp)
    if min_imm is None:
        return None

    if window[7].mnemonic not in _JB_MNEMONICS:
        return None

    if window[8].mnemonic != "cmp":
        return None
    max_imm = _match_reg_imm(window[8].op_str, temp)
    if max_imm is None:
        return None

    if window[9].mnemonic not in _JAE_MNEMONICS:
        return None

    if window[10].mnemonic != "mov" or _STACK_BASE_LOAD_RE.match(window[10].op_str) is None:
        return None

    if window[11].mnemonic != "add":
        return None
    add_match = _ADD_R14_RE.match(window[11].op_str)
    if add_match is None or add_match.group(1) != temp:
        return None

    return TagPrologue(
        addr=window[0].addr,
        fingerprint=TagFingerprint(
            static_gas=static_gas,
            min_depth_bytes=_to_signed64(min_imm),
            max_depth_bound=_to_signed64(max_imm),
        ),
        temp_register=temp,
    )


def _strip_nops(instructions: Sequence[X86Instruction]) -> List[X86Instruction]:
    """滤掉 nop。

    两处来源都必须跳过：``compileEVMTag`` 头上的 label 锚点 nop（汇编器已 optimize
    out 成 0 字节，但保守起见照滤），以及汇编器为规避 Intel JCC erratum 插入的对齐
    padding——后者可能落在序言**内部任意位置**，不跳过就会把 12 条窗口撑破。
    """
    return [insn for insn in instructions if insn.mnemonic != "nop"]


def find_tag_prologues(
    instructions: Sequence[X86Instruction],
) -> Tuple[TagPrologue, ...]:
    """扫出全部 TAG 序言，按地址升序。"""
    stream = _strip_nops(instructions)
    found: List[TagPrologue] = []
    index = 0
    while index < len(stream):
        prologue = _match_tag_at(stream, index)
        if prologue is None:
            index += 1
            continue
        found.append(prologue)
        # 序言内部不可能再嵌套一处序言，整窗跳过即可。
        index += TAG_PROLOGUE_LENGTH
    return tuple(found)


def extract_return_chain_anchors(
    instructions: Sequence[X86Instruction],
) -> Tuple[ReturnChainAnchor, ...]:
    """扫出全部 ``cmp REG, imm`` + ``je <abs>`` 对（含非返回链的普通比较）。

    调用方负责按"目标是否为 TAG 头"过滤：非 TAG 目标的 cmp/je 只是普通条件分支，
    不承载 pc 信息。负立即数直接丢弃——EVM pc 非负。
    """
    stream = _strip_nops(instructions)
    anchors: List[ReturnChainAnchor] = []
    for first, second in zip(stream, stream[1:]):
        if first.mnemonic != "cmp" or second.mnemonic not in _JE_MNEMONICS:
            continue
        imm = _match_reg_imm(first.op_str)
        if imm is None or imm < 0:
            continue
        target = _ABS_TARGET_RE.match(second.op_str.strip())
        if target is None:
            continue
        anchors.append(
            ReturnChainAnchor(evm_pc=imm, x86_addr=int(target.group(1), 0))
        )
    return tuple(anchors)


def evm_block_fingerprint(block: EVMBlock) -> TagFingerprint:
    """IR 侧的同一三元组。

    ``max_depth`` 初值是 Go 的 ``math.MaxInt64``，``*32+1`` 会在 uint64 上回绕；
    codegen 发射的正是回绕后的立即数，所以这里必须做同样的回绕再归一到 signed。
    """
    return TagFingerprint(
        static_gas=block.static_gas,
        min_depth_bytes=_to_signed64(block.min_depth * _STACK_ELEMENT_BYTES),
        max_depth_bound=_to_signed64(block.max_depth * _STACK_ELEMENT_BYTES + 1),
    )


# ---------------------------------------------------------------------------
# 构造
# ---------------------------------------------------------------------------


def _compute_certificate_fingerprint(
    pc_to_addr: Mapping[int, int],
    intervals: Mapping[int, Tuple[int, int]],
    tag_fingerprints: Mapping[int, TagFingerprint],
    non_block_regions: Sequence[Tuple[int, int]],
    code_range: Tuple[int, int],
) -> str:
    """映射的内容散列，进 theorem key。

    codegen 变更 ⇒ 地址/区间/立即数任一变化 ⇒ 指纹变化 ⇒ 旧证书自动失效。
    """
    digest = hashlib.sha256()
    digest.update(b"tag_align/v%d\n" % TAG_ALIGN_SCHEMA_VERSION)
    digest.update(b"code=%d:%d\n" % code_range)
    for start, end in non_block_regions:
        digest.update(b"nonblock=%d:%d\n" % (start, end))
    for pc in sorted(pc_to_addr):
        interval = intervals[pc]
        triple = tag_fingerprints[pc].as_tuple()
        digest.update(
            b"blk=%d:%d:%d:%d:%d:%d:%d\n"
            % (
                pc,
                pc_to_addr[pc],
                interval[0],
                interval[1],
                triple[0],
                triple[1],
                triple[2],
            )
        )
    return "tagalign%d:%s" % (TAG_ALIGN_SCHEMA_VERSION, digest.hexdigest())


def _check_evm_blocks(evm_blocks: Sequence[EVMBlock]) -> None:
    if not evm_blocks:
        raise BlockAlignmentError(REASON_EMPTY_INPUT, "EVM 块序列为空")
    for previous, current in zip(evm_blocks, evm_blocks[1:]):
        if current.pc <= previous.pc:
            raise BlockAlignmentError(
                REASON_EVM_PC_NOT_MONOTONIC,
                "control_frames 必须按 pc 严格升序，实际 pc=%d 之后出现 pc=%d"
                % (previous.pc, current.pc),
            )


def _zip_fingerprints(
    evm_blocks: Sequence[EVMBlock], prologues: Sequence[TagPrologue]
) -> None:
    """单调 zip 后逐位核对。

    数量相等只是必要条件；真正的判别力在"第 i 个 EVM 块的三元组 == 第 i 处序言的三
    元组"这 N 个等式上。改动任何一个块的 static_gas 都会在该位断掉——而不是让整条
    序列错位一格后勉强对上（错位需要 N-1 个等式同时成立）。
    """
    if len(prologues) != len(evm_blocks):
        raise BlockAlignmentError(
            REASON_TAG_COUNT_MISMATCH,
            "x86 侧命中 %d 处 TAG 序言，IR 侧有 %d 个块"
            % (len(prologues), len(evm_blocks)),
        )
    for index, (block, prologue) in enumerate(zip(evm_blocks, prologues)):
        expected = evm_block_fingerprint(block)
        if prologue.fingerprint != expected:
            raise BlockAlignmentError(
                REASON_FINGERPRINT_MISMATCH,
                "第 %d 位错配：evm_pc=%d 期望 %s，x86 0x%x 实为 %s"
                % (
                    index,
                    block.pc,
                    expected.as_tuple(),
                    prologue.addr,
                    prologue.fingerprint.as_tuple(),
                ),
            )


def _cross_check_anchors(
    instructions: Sequence[X86Instruction], addr_to_pc: Mapping[int, int]
) -> Tuple[Tuple[ReturnChainAnchor, ...], int]:
    """返回链锚点交叉校验：与指纹映射必须 100% 吻合。

    这是唯一一个**独立于 TAG 指纹**的证据源，所以一处不吻合就说明两个证据源冲突，
    没有任何理由偏信其一 ⇒ 整体拒绝。
    """
    on_tag: Dict[Tuple[int, int], ReturnChainAnchor] = {}
    off_tag = 0
    for anchor in extract_return_chain_anchors(instructions):
        mapped_pc = addr_to_pc.get(anchor.x86_addr)
        if mapped_pc is None:
            off_tag += 1
            continue
        if mapped_pc != anchor.evm_pc:
            raise BlockAlignmentError(
                REASON_ANCHOR_DISAGREEMENT,
                "返回链锚点 cmp $%d / je 0x%x 与指纹映射冲突：该地址被对齐到 evm_pc=%d"
                % (anchor.evm_pc, anchor.x86_addr, mapped_pc),
            )
        on_tag[(anchor.evm_pc, anchor.x86_addr)] = anchor
    ordered = tuple(
        anchor for _, anchor in sorted(on_tag.items(), key=lambda item: item[0])
    )
    return ordered, off_tag


def _check_interval_coverage(
    intervals: Sequence[Tuple[int, int]],
    non_block_regions: Sequence[Tuple[int, int]],
    basic_blocks: Sequence[X86Block],
    code_range: Tuple[int, int],
) -> Tuple[int, Tuple[int, ...]]:
    """方案 §2.4 ④(b)：区间两两不重叠且完全覆盖代码段。

    区间由相邻 TAG 起始地址切分，因此"不重叠"和"无缝"由严格升序自动保证；真正要查
    的是三件事：(1) 起始地址严格升序且区间非空；(2) 区间与已登记的非块区域合起来正好
    铺满 ``code_range``（指令级覆盖）；(3) 每个 **块区间**的边界都落在
    ``identify_basic_blocks`` 的边界上——否则某个 basic block 会被劈成两半，"每条指
    令恰属于一个块区间"就不再等价于"每个 basic block 恰属于一个块区间"，下游按 bb
    编排会静默取到半个块。

    **一处必须显式登记而不是放行的例外**：入口处的保留寄存器序言与第一个 TAG 的头三
    条指令同属一个 basic block（``identify_basic_blocks`` 只在 jcc 处切，而这段直到
    第一个 ``jb`` 才有分支），所以非块区域的右边界必然劈开入口 bb。这类跨越只允许发生
    在"非块区域 → 块区间"的边界上，且必须被记进 ``straddling_basic_blocks``；块区间之
    间的跨越一律 fail-closed。

    Returns:
        ``(整块落在区间内的 bb 数, 跨越非块边界的 bb 起始地址元组)``。
    """
    if not intervals:
        raise BlockAlignmentError(REASON_EMPTY_INPUT, "区间列表为空")
    for previous, current in zip(intervals, intervals[1:]):
        if previous[1] != current[0] or previous[0] >= previous[1]:
            raise BlockAlignmentError(
                REASON_INTERVAL_NOT_MONOTONIC,
                "区间 [0x%x,0x%x) 与 [0x%x,0x%x) 不构成升序无缝划分"
                % (previous[0], previous[1], current[0], current[1]),
            )
    if intervals[-1][0] >= intervals[-1][1]:
        raise BlockAlignmentError(
            REASON_INTERVAL_NOT_MONOTONIC,
            "末区间 [0x%x,0x%x) 为空" % intervals[-1],
        )

    regions = sorted(list(intervals) + list(non_block_regions))
    covered_start, covered_end = regions[0][0], regions[-1][1]
    if (covered_start, covered_end) != code_range:
        raise BlockAlignmentError(
            REASON_INSTRUCTION_UNCOVERED,
            "区间并集 [0x%x,0x%x) 未铺满代码段 [0x%x,0x%x)"
            % (covered_start, covered_end, code_range[0], code_range[1]),
        )
    for previous, current in zip(regions, regions[1:]):
        if previous[1] != current[0]:
            raise BlockAlignmentError(
                REASON_INSTRUCTION_UNCOVERED,
                "区间 [0x%x,0x%x) 与 [0x%x,0x%x) 之间有未登记的空隙"
                % (previous[0], previous[1], current[0], current[1]),
            )

    # 每个 basic block 用"起点定位 region + 终点越界判定"归属：region 已经证明是无缝
    # 升序划分，所以起点唯一确定 region。
    region_starts = [start for start, _ in regions]
    interval_starts = {start for start, _ in intervals}
    covered = 0
    straddling: List[int] = []
    for block in sorted(basic_blocks, key=lambda b: b.start_addr):
        position = bisect.bisect_right(region_starts, block.start_addr) - 1
        if position < 0:
            raise BlockAlignmentError(
                REASON_INSTRUCTION_UNCOVERED,
                "basic block 0x%x 落在所有区间之前" % block.start_addr,
            )
        region = regions[position]
        in_interval = region[0] in interval_starts
        if block.end_addr <= region[1]:
            if in_interval:
                covered += 1
            continue
        if in_interval:
            raise BlockAlignmentError(
                REASON_INTERVAL_NOT_BLOCK_ALIGNED,
                "basic block [0x%x,0x%x) 跨越块区间边界 0x%x"
                % (block.start_addr, block.end_addr, region[1]),
            )
        straddling.append(block.start_addr)
    return covered, tuple(straddling)


def build_block_alignment(
    evm_blocks: Sequence[EVMBlock],
    x86_instructions: Sequence[X86Instruction],
    basic_blocks: Optional[Sequence[X86Block]] = None,
) -> BlockAlignment:
    """构造权威映射；任何一位对不上即抛 ``BlockAlignmentError``。

    Args:
        evm_blocks: IR 的 ``control_frames``，按 pc 升序（会被校验）。
        x86_instructions: 反汇编出的完整指令流（``X86Program.from_hex(...).instructions``；
            注意 ``X86Program`` 不建 blocks，``.blocks`` 是空的）。
        basic_blocks: 可选的预算 basic block 划分；省略时内部调用
            ``identify_basic_blocks``。传入只为省一次线性扫描，不改变判定。

    Returns:
        通过全部四项记账的 ``BlockAlignment``。

    Raises:
        BlockAlignmentError: 数量、逐位指纹、返回链锚点、区间覆盖任一项不符。
    """
    _check_evm_blocks(evm_blocks)
    if not x86_instructions:
        raise BlockAlignmentError(REASON_EMPTY_INPUT, "x86 指令流为空")

    prologues = find_tag_prologues(x86_instructions)
    _zip_fingerprints(evm_blocks, prologues)

    pc_to_addr: Dict[int, int] = {}
    addr_to_pc: Dict[int, int] = {}
    tag_fingerprints: Dict[int, TagFingerprint] = {}
    for block, prologue in zip(evm_blocks, prologues):
        pc_to_addr[block.pc] = prologue.addr
        addr_to_pc[prologue.addr] = block.pc
        tag_fingerprints[block.pc] = prologue.fingerprint

    anchors_on_tag, anchors_off_tag = _cross_check_anchors(
        x86_instructions, addr_to_pc
    )

    first = x86_instructions[0]
    last = x86_instructions[-1]
    code_range = (first.addr, last.addr + last.size)

    starts = [prologue.addr for prologue in prologues]
    interval_list: List[Tuple[int, int]] = [
        (start, starts[index + 1] if index + 1 < len(starts) else code_range[1])
        for index, start in enumerate(starts)
    ]
    # 第一个 TAG 之前的保留寄存器序言（12 字节）：显式登记为非块代码。空区间不登记，
    # 免得指纹里出现一个恒等于 (x,x) 的伪条目。
    non_block_regions: Tuple[Tuple[int, int], ...] = (
        ((code_range[0], starts[0]),) if starts[0] > code_range[0] else ()
    )
    if starts[0] < code_range[0]:
        raise BlockAlignmentError(
            REASON_INSTRUCTION_UNCOVERED,
            "首个 TAG 地址 0x%x 在代码段起点 0x%x 之前" % (starts[0], code_range[0]),
        )

    blocks = (
        list(basic_blocks)
        if basic_blocks is not None
        else identify_basic_blocks(list(x86_instructions))
    )
    covered, straddling = _check_interval_coverage(
        interval_list, non_block_regions, blocks, code_range
    )

    intervals = {
        block.pc: interval for block, interval in zip(evm_blocks, interval_list)
    }
    multiplicity: Dict[Tuple[int, int, int], int] = {}
    for value in tag_fingerprints.values():
        key = value.as_tuple()
        multiplicity[key] = multiplicity.get(key, 0) + 1

    evidence = AlignmentEvidence(
        evm_block_count=len(evm_blocks),
        tag_count=len(prologues),
        distinct_fingerprints=len(multiplicity),
        max_fingerprint_multiplicity=max(multiplicity.values()),
        anchors_on_tag=anchors_on_tag,
        anchors_off_tag=anchors_off_tag,
        basic_block_total=len(blocks),
        basic_block_covered=covered,
        straddling_basic_blocks=straddling,
        code_range=code_range,
    )
    return BlockAlignment(
        pc_to_addr=pc_to_addr,
        addr_to_pc=addr_to_pc,
        intervals=intervals,
        non_block_regions=non_block_regions,
        fingerprints=tag_fingerprints,
        evidence=evidence,
        fingerprint=_compute_certificate_fingerprint(
            pc_to_addr, intervals, tag_fingerprints, non_block_regions, code_range
        ),
    )
