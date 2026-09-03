"""P3：go-hpc-evm codegen 内生拷贝循环的模板识别。

`impl_amd64.go` 共 7 条 runtime 回边（docs/循环处理增强方案.md §3），
坍缩为 6 种指令形态（byte-tail 在 FromLow/FromHigh 各出现一次）：

```
compileMakeDataCopy         1 条 (CALLDATACOPY/CODECOPY)  → makedata-byte-copy
compileEVMRETURNDATACOPY    1 条                          → returndata-byte-copy
compileEVMMCOPYFromLow      2 条 (字循环 + 尾字节循环)     → mcopy-low-word / mcopy-byte-tail
compileEVMMCOPYFromHigh     3 条 (反向字循环 + SHRStart    → mcopy-high-word / mcopy-shr-align
                                  对齐移位循环 + 尾字节)      / mcopy-byte-tail
```

两层匹配：

- **v1 特征匹配**（`match_copy_loop_template`）：形状特征过滤，仅用于
  配对实验/统计报告，不得用于最终验证结论。
- **v2 逐指令精确匹配**（`match_body_blocks_exact`）：模板 = 逐条
  (mnemonic, operand pattern)，寄存器占位符双射统一、立即数精确相等、
  跳转标签一致（含 codegen NOP 循环头容忍）。fail-closed 守卫与
  P3(ii) 引理证明（verification/tier2_lemmas.py）共用同一张
  `TEMPLATES` 规格表——证明在规格的真实实例字节上完成，匹配命中即
  引理适用（寄存器 α-重命名下语义不变）。
"""

from dataclasses import dataclass
from typing import Dict, List, Optional, Sequence, Tuple

from x86_64.models import X86Block

# ---------------------------------------------------------------------------
# v2：逐指令精确模板（匹配器与引理证明共用的唯一事实来源）
# ---------------------------------------------------------------------------

# 64 位寄存器 → (32 位别名, 低 8 位别名)
_REG_ALIASES: Dict[str, Tuple[str, str]] = {
    "rax": ("eax", "al"), "rbx": ("ebx", "bl"), "rcx": ("ecx", "cl"),
    "rdx": ("edx", "dl"), "rsi": ("esi", "sil"), "rdi": ("edi", "dil"),
    "rbp": ("ebp", "bpl"), "rsp": ("esp", "spl"),
    "r8": ("r8d", "r8b"), "r9": ("r9d", "r9b"), "r10": ("r10d", "r10b"),
    "r11": ("r11d", "r11b"), "r12": ("r12d", "r12b"),
    "r13": ("r13d", "r13b"), "r14": ("r14d", "r14b"), "r15": ("r15d", "r15b"),
}
_REG64_OF_ALIAS: Dict[str, Tuple[str, int]] = {}
for _r64, (_r32, _r8) in _REG_ALIASES.items():
    _REG64_OF_ALIAS[_r64] = (_r64, 64)
    _REG64_OF_ALIAS[_r32] = (_r64, 32)
    _REG64_OF_ALIAS[_r8] = (_r64, 8)


@dataclass(frozen=True)
class LoopTemplate:
    """一条 codegen 循环的逐指令精确形态。

    pattern 每项是 ``(mnemonic, operand_pattern)``；operand_pattern 里
    ``{X}``/``{X:32}``/``{X:8}`` 是寄存器占位符（同名必须绑定同一 64 位
    寄存器，别名宽度按后缀），``{@L}`` 是跳转标签占位符（同名必须绑定
    同一目标地址），``("label", "L")`` 项声明下一条指令的地址为标签 L。
    字面寄存器名（如 r15）必须精确相等。
    """

    name: str
    pattern: Tuple[Tuple[str, str], ...]


# 六种形态（来源：impl_amd64.go 发射序列 + CErc20/CALLDATACOPY core 实证）。
# {@HEADER} 恒指回边目标（循环头），{@EXIT}/{@EXIT2}/{@TAIL} 是环外出口。
TEMPLATES: Dict[str, LoopTemplate] = {
    "returndata-byte-copy": LoopTemplate(
        name="returndata-byte-copy",
        pattern=(
            ("label", "HEADER"),
            ("cmp", "{S}, 1"),
            ("jb", "{@EXIT}"),
            ("sub", "{S}, 1"),
            ("mov", "{T}, {OFF}"),
            ("add", "{T}, {S}"),
            ("movzx", "{B:32}, byte ptr [{INP} + {T}]"),
            ("mov", "{T}, {S}"),
            ("add", "{T}, {DST}"),
            ("mov", "byte ptr [r15 + {T}], {B:8}"),
            ("jmp", "{@HEADER}"),
        ),
    ),
    "makedata-byte-copy": LoopTemplate(
        name="makedata-byte-copy",
        pattern=(
            ("label", "HEADER"),
            ("cmp", "{S}, 1"),
            ("jb", "{@EXIT}"),
            ("sub", "{S}, 1"),
            ("mov", "{T}, {OFF}"),
            ("add", "{T}, {S}"),
            ("cmp", "{T}, {LEN}"),
            ("jae", "{@ZERO}"),
            ("movzx", "{B:32}, byte ptr [{INP} + {T}]"),
            ("jmp", "{@STORE}"),
            ("label", "ZERO"),
            ("mov", "{B}, 0"),
            ("label", "STORE"),
            ("mov", "{T}, {S}"),
            ("add", "{T}, {DST}"),
            ("mov", "byte ptr [r15 + {T}], {B:8}"),
            ("jmp", "{@HEADER}"),
        ),
    ),
    "mcopy-low-word": LoopTemplate(
        name="mcopy-low-word",
        pattern=(
            ("label", "HEADER"),
            ("cmp", "{S}, 0"),
            ("je", "{@EXIT}"),
            ("cmp", "{S}, 8"),
            ("jl", "{@TAIL}"),
            ("mov", "{T}, qword ptr [{SRC}]"),
            ("mov", "qword ptr [{DST}], {T}"),
            ("add", "{SRC}, 8"),
            ("add", "{DST}, 8"),
            ("sub", "{S}, 8"),
            ("jmp", "{@HEADER}"),
        ),
    ),
    "mcopy-high-word": LoopTemplate(
        name="mcopy-high-word",
        pattern=(
            ("label", "HEADER"),
            ("cmp", "{S}, 0"),
            ("je", "{@EXIT}"),
            ("mov", "{T}, qword ptr [{SRC}]"),
            ("mov", "qword ptr [{DST}], {T}"),
            ("sub", "{S}, 8"),
            ("sub", "{SRC}, 8"),
            ("cmp", "{S}, 8"),
            ("jl", "{@EXIT2}"),
            ("sub", "{DST}, 8"),
            ("jmp", "{@HEADER}"),
        ),
    ),
    "mcopy-byte-tail": LoopTemplate(
        name="mcopy-byte-tail",
        pattern=(
            ("label", "HEADER"),
            ("cmp", "{S}, 0"),
            ("je", "{@EXIT}"),
            ("mov", "byte ptr [{DST}], {T:8}"),
            ("shr", "{T}, 8"),
            ("sub", "{S}, 1"),
            ("add", "{DST}, 1"),
            ("jmp", "{@HEADER}"),
        ),
    ),
    "mcopy-shr-align": LoopTemplate(
        name="mcopy-shr-align",
        pattern=(
            ("label", "HEADER"),
            ("cmp", "{C}, 0"),
            ("je", "{@EXIT}"),
            ("shr", "{T}, 8"),
            ("sub", "{C}, 1"),
            ("jmp", "{@HEADER}"),
        ),
    ),
}


def _tokenize_pattern(op_pattern: str) -> List[str]:
    """把 operand pattern 切成字面片段与占位符的交替序列。"""
    tokens: List[str] = []
    rest = op_pattern
    while rest:
        i = rest.find("{")
        if i < 0:
            tokens.append(rest)
            break
        if i > 0:
            tokens.append(rest[:i])
        j = rest.find("}", i)
        tokens.append(rest[i:j + 1])
        rest = rest[j + 1:]
    return tokens


def _match_operands(op_pattern: str, op_str: str, binding: Dict[str, object]) -> bool:
    """按 pattern 匹配 op_str，寄存器/标签占位符统一到 binding（双射）。"""
    pos = 0
    text = op_str.strip()
    tokens = _tokenize_pattern(op_pattern)
    for k, token in enumerate(tokens):
        if not token.startswith("{"):
            if not text.startswith(token, pos):
                return False
            pos += len(token)
            continue
        body = token[1:-1]
        # 提取占位符实参：到下一个字面片段起始为止
        next_literal = tokens[k + 1] if k + 1 < len(tokens) and not tokens[k + 1].startswith("{") else None
        if next_literal is None:
            arg = text[pos:]
            pos = len(text)
        else:
            end = text.find(next_literal, pos)
            if end < 0:
                return False
            arg = text[pos:end]
            pos = end
        arg = arg.strip()
        if body.startswith("@"):
            # 跳转标签：绑定目标地址（十六进制/十进制字面量）
            try:
                addr = int(arg, 0)
            except ValueError:
                return False
            key = "@" + body[1:]
            if key in binding:
                if binding[key] != addr:
                    return False
            else:
                binding[key] = addr
            continue
        # 寄存器占位符（可带宽度后缀）
        name, _, width_s = body.partition(":")
        width = int(width_s) if width_s else 64
        if arg not in _REG64_OF_ALIAS:
            return False
        reg64, actual_width = _REG64_OF_ALIAS[arg]
        if actual_width != width:
            return False
        if name in binding:
            if binding[name] != reg64:
                return False
        else:
            # 双射：同一寄存器不得绑定两个占位符
            if reg64 in {v for k2, v in binding.items() if not k2.startswith("@")}:
                return False
            binding[name] = reg64
    return pos == len(text)


def match_template_exact(
    body_insns: Sequence, template: LoopTemplate, header_addr: int
) -> Optional[Dict[str, object]]:
    """逐指令精确匹配（nop 剥除后）。

    Returns:
        占位符绑定（寄存器名 / '@LABEL'→地址），不匹配返回 None。
        额外校验：@HEADER 必须落在循环头；("label", L) 声明的内部标签
        必须与对应位置指令一致。跳到指令前紧邻 nop（codegen 的
        CompileStandAlone(NOP) 循环头/对齐产物）视为等价入口。
    """
    insns: List = []
    accept_addrs: List[set] = []
    pending_nops: set = set()
    for x in body_insns:
        if x.mnemonic == "nop":
            pending_nops.add(x.addr)
            continue
        insns.append(x)
        accept_addrs.append({x.addr} | pending_nops)
        pending_nops = set()

    binding: Dict[str, object] = {}
    label_pos: Dict[str, int] = {}
    idx = 0
    for item_kind, item_val in template.pattern:
        if item_kind == "label":
            if idx >= len(insns):
                return None
            label_pos[item_val] = idx
            continue
        if idx >= len(insns):
            return None
        insn = insns[idx]
        if insn.mnemonic != item_kind:
            return None
        if not _match_operands(item_val, insn.op_str, binding):
            return None
        idx += 1
    if idx != len(insns):
        return None  # 序列必须整体耗尽（不允许多余指令）

    # 内部标签一致性：分支目标必须落在声明位置（或其前导 nop）
    for name, pos in label_pos.items():
        key = "@" + name
        if key in binding and binding[key] not in accept_addrs[pos]:
            return None
    if "HEADER" not in label_pos:
        return None
    if header_addr not in accept_addrs[label_pos["HEADER"]]:
        return None
    if binding.get("@HEADER") is None:
        return None
    return binding


def match_body_blocks_exact(
    body_blocks: Sequence[X86Block], header_addr: int
) -> Optional[Tuple[str, Dict[str, object]]]:
    """对 natural loop 的 body 块（按地址序展平）尝试全部模板。"""
    ordered = sorted(body_blocks, key=lambda b: b.start_addr)
    insns = [insn for b in ordered for insn in b.instructions]
    for template in TEMPLATES.values():
        binding = match_template_exact(insns, template, header_addr)
        if binding is not None:
            return template.name, binding
    return None


# ---------------------------------------------------------------------------
# MCOPY 复合 summary 的构造级直线段（非 natural-loop，不进 TEMPLATES/
# PROVEN_TIER2_LEMMAS）。FromHigh 四块对应复合引理
# prove_mcopy_high_composition 实跑的 preamble/align/glue 字节。
# ---------------------------------------------------------------------------

MCOPY_HIGH_BLOCK_TEMPLATES: Dict[str, Tuple[Tuple[str, str], ...]] = {
    # 防御分支块：size<8 直落 glue2（分派已保证 size>8，该边不可达）
    "mcopy-high-preamble": (
        ("cmp", "{S}, 8"),
        ("jl", "{@GLUE}"),
    ),
    # 指针对齐块：DST/SRC 推进到区间高端最后一个 qword
    "mcopy-high-align": (
        ("add", "{DST}, {S}"),
        ("add", "{SRC}, {S}"),
        ("sub", "{SRC}, 8"),
        ("sub", "{DST}, 8"),
    ),
    # glue1（word 的 @EXIT2）：DST 回退到区间起点
    "mcopy-high-glue1": (
        ("sub", "{DST}, {S}"),
    ),
    # glue2：跨界 qword 载入 + SRC 寄存器改写为移位计数 8-S'
    "mcopy-high-glue2": (
        ("mov", "{T}, qword ptr [{SRC}]"),
        ("mov", "{SRC}, 8"),
        ("sub", "{SRC}, {S}"),
    ),
}

# FromLow 的 glue（进尾字节循环前的跨界 qword 载入）
MCOPY_LOW_GLUE_TEMPLATE: Tuple[Tuple[str, str], ...] = (
    ("mov", "{T}, qword ptr [{SRC}]"),
)


def match_straightline_exact(
    insns: Sequence,
    pattern: Tuple[Tuple[str, str], ...],
    binding: Dict[str, object],
) -> Optional[Dict[str, object]]:
    """逐指令精确匹配直线段块（nop 剥除；整块指令数必须耗尽）。

    在传入 ``binding`` 基础上增量统一：已绑定的寄存器占位符必须与
    块内寄存器一致（保证直线段与 word 循环的寄存器角色对齐），新出现
    的标签占位符（如 ``{@GLUE}``）绑定进返回的新 binding。不修改入参。
    """
    meaningful = [x for x in insns if x.mnemonic != "nop"]
    if len(meaningful) != len(pattern):
        return None
    out = dict(binding)
    for insn, (mnemonic, op_pattern) in zip(meaningful, pattern):
        if insn.mnemonic != mnemonic:
            return None
        if not _match_operands(op_pattern, insn.op_str, out):
            return None
    return out


# ---------------------------------------------------------------------------

# ---------------------------------------------------------------------------
# v1：形状特征匹配（仅配对实验/统计，不作最终守卫）
# ---------------------------------------------------------------------------

# 拷贝循环家族的形状特征（按 impl_amd64.go 源码）：
# - word 循环：8 字节 mov 搬运 + 指针 ±8 + cmp/jcc 回跳
# - 尾字节循环：mov byte 写 + shr reg,8 + 计数 ±1
# - SHRStart 对齐循环：shr reg,8 + sub reg,1 + cmp reg,0（无内存写）
_MAX_TEMPLATE_BODY_BLOCKS = 6


def _classify_body_instructions(blocks: Sequence[X86Block]) -> Dict[str, bool]:
    has_word_load = False       # mov reg, qword [reg±disp]
    has_word_store = False      # mov qword [reg±disp], reg
    has_byte_load = False       # movzx reg, byte [reg+reg]
    has_byte_store = False      # mov byte [reg], reg8
    has_shr_8 = False           # shr reg, 8
    has_ptr_step_8 = False      # add/sub reg, 8
    has_step_1 = False          # add/sub reg, 1
    has_cmp = False
    has_bridge = False          # lea [rip+...]（host bridge，模板内不该有）
    has_status_write = False    # [r13+0xe0] 状态写（错误 stub / bridge）

    for block in blocks:
        for insn in block.instructions:
            m, ops = insn.mnemonic, insn.op_str
            if m == "lea" and "rip" in ops:
                has_bridge = True
            if "[r13 + 0xe0]" in ops:
                has_status_write = True
            if m == "mov":
                if "qword ptr [" in ops:
                    dst, _, src = ops.partition(",")
                    if dst.strip().startswith("qword ptr ["):
                        has_word_store = True
                    else:
                        has_word_load = True
                elif "byte ptr [" in ops and ops.strip().startswith("byte ptr ["):
                    has_byte_store = True
            elif m == "movzx" and "byte ptr [" in ops:
                has_byte_load = True
            elif m == "shr" and ops.rstrip().endswith(("8", "0x8")):
                has_shr_8 = True
            elif m in ("add", "sub"):
                tail = ops.rsplit(",", 1)[-1].strip()
                if tail in ("8", "0x8"):
                    has_ptr_step_8 = True
                elif tail in ("1", "0x1"):
                    has_step_1 = True
            elif m == "cmp":
                has_cmp = True

    return {
        "word_load": has_word_load,
        "word_store": has_word_store,
        "byte_load": has_byte_load,
        "byte_store": has_byte_store,
        "shr_8": has_shr_8,
        "ptr_step_8": has_ptr_step_8,
        "step_1": has_step_1,
        "cmp": has_cmp,
        "bridge": has_bridge,
        "status_write": has_status_write,
    }


def match_copy_loop_template(
    loop_body_blocks: Sequence[X86Block],
) -> Optional[str]:
    """v1 形状识别（实验/统计用）。

    Returns:
        模板名（'word-copy' / 'byte-copy' / 'byte-tail' / 'shr-align' /
        'data-copy'），不匹配返回 None。
    """
    if not loop_body_blocks or len(loop_body_blocks) > _MAX_TEMPLATE_BODY_BLOCKS:
        return None

    feats = _classify_body_instructions(loop_body_blocks)
    if feats["bridge"] or feats["status_write"]:
        return None  # 含 host bridge/状态写的不是 codegen 拷贝模板
    if not feats["cmp"]:
        return None

    # MCOPY/RETURNDATACOPY 字循环：8 字节搬运 + 指针步进 8
    if feats["word_load"] and feats["word_store"] and feats["ptr_step_8"]:
        return "word-copy"
    # MakeDataCopy/RETURNDATACOPY 逐字节拷贝：movzx byte 载入 + byte 写 + 计数减 1
    if feats["byte_load"] and feats["byte_store"] and feats["step_1"]:
        return "byte-copy"
    # 尾字节循环：byte 写 + shr 8 + 步进 1
    if feats["byte_store"] and feats["shr_8"] and feats["step_1"]:
        return "byte-tail"
    # SHRStart 对齐移位循环：shr 8 + 计数减 1，无内存写
    if (
        feats["shr_8"]
        and feats["step_1"]
        and not feats["word_store"]
        and not feats["byte_store"]
    ):
        return "shr-align"
    # MakeDataCopy 主循环：word 搬运 + 越界写 0 分支（word_store 但源可能是 0 立即数）
    if feats["word_store"] and feats["ptr_step_8"]:
        return "data-copy"
    return None


# ---------------------------------------------------------------------------
# P3(ii)：已证引理注册表
# ---------------------------------------------------------------------------

# 六种形态引理均已离线证明（tests/unit/test_tier2_lemmas.py 固化证明，
# 绑定 impl_amd64.go 当前发射序列；codegen 变更 ⇒ 精确匹配失败 ⇒
# fail-closed）。注册表键 = TEMPLATES 键。
PROVEN_TIER2_LEMMAS: frozenset = frozenset(TEMPLATES)


def make_tier2_matcher(blocks_by_addr: Dict[int, X86Block], *,
                       require_proven_lemma: bool = True):
    """构造 loop_pairing 用的 tier2_matcher。

    Args:
        require_proven_lemma: True（默认，fail-closed）时逐指令精确匹配
            且模板必须有已证引理；False 仅用于配对/统计实验（v1 特征
            匹配），不得用于最终验证结论。
    """
    def _matcher(loop) -> bool:
        body_blocks = [
            blocks_by_addr[addr] for addr in loop.body if addr in blocks_by_addr
        ]
        if require_proven_lemma:
            matched = match_body_blocks_exact(body_blocks, loop.header)
            return matched is not None and matched[0] in PROVEN_TIER2_LEMMAS
        return match_copy_loop_template(body_blocks) is not None

    return _matcher
