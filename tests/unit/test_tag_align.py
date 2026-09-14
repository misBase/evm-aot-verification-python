"""``tools/tag_align.py`` 的回归：三合约全覆盖 + fail-closed 反向用例。

对应 docs/块级lockstep等价验证方案.md §6 阶段 0 的验收：

    tag_align  三合约 127/127、723/723、742/742 全覆盖 + 返回链锚点 100% 吻合

外加方案 §2.4 ④(b) 新增的义务（区间两两不重叠、完全覆盖代码段、非块代码显式登记）
与 §6 阶段 3 的反向用例（人为改动一个块的 static_gas 必须整体拒绝）。

真实合约用例只做静态扫描（无 Z3），三合约合计秒级，因此**不打 slow 标记**——这类
结构性回归的价值正在于日常 ``-m "not slow"`` 也跑得到。
"""

import os
import re
from dataclasses import replace
from typing import Dict, List, NamedTuple, Sequence, Tuple

import pytest

from evm_ir.json_parser import load_ir_from_json
from evm_ir.models import GO_MAX_INT64, EVMBlock
from x86_64.cfg import identify_basic_blocks
from x86_64.models import X86Instruction
from x86_64.program import X86Program
from tools.tag_align import (
    REASON_ANCHOR_DISAGREEMENT,
    REASON_EMPTY_INPUT,
    REASON_EVM_PC_NOT_MONOTONIC,
    REASON_FINGERPRINT_MISMATCH,
    REASON_INTERVAL_NOT_BLOCK_ALIGNED,
    REASON_TAG_COUNT_MISMATCH,
    TAG_PROLOGUE_LENGTH,
    BlockAlignment,
    BlockAlignmentError,
    build_block_alignment,
    evm_block_fingerprint,
    extract_return_chain_anchors,
    find_tag_prologues,
)


_DATA_ROOT = os.path.join(
    os.path.dirname(__file__), "..", "data", "ext_contracts"
)
_BASE_ADDR = 0


class ContractExpectation(NamedTuple):
    """方案 §1.3/§2.4 记录的实测数字，逐项当断言用。"""

    directory: str
    stem: str
    evm_blocks: int
    anchors_on_tag: int  # 去重后落在 TAG 头上的返回链锚点对数
    basic_block_total: int
    basic_block_covered: int
    wide_prefix_hits: int  # 只看 3 条、cmp 第二操作数不限形态时的命中数


CONTRACTS: Dict[str, ContractExpectation] = {
    "ENSRegistry": ContractExpectation(
        "ens_registry", "ENSRegistry", 127, 33, 7060, 7059, 273
    ),
    "CErc20": ContractExpectation(
        "compound_cerc20", "CErc20", 723, 192, 34445, 34444, 1523
    ),
    "Safe": ContractExpectation("safe", "Safe", 742, 166, 30869, 30868, 1265),
}


class LoadedContract(NamedTuple):
    expectation: ContractExpectation
    evm_blocks: List[EVMBlock]
    instructions: List[X86Instruction]
    basic_blocks: list
    alignment: BlockAlignment


# 反汇编 + 扫描每个合约各要几秒，且本文件里每个用例都要用；按名字缓存一次。
_CACHE: Dict[str, LoadedContract] = {}


def _paths(expectation: ContractExpectation) -> Tuple[str, str]:
    base = os.path.join(_DATA_ROOT, expectation.directory, expectation.stem)
    return base + ".json", base + ".hex"


def _load(name: str) -> LoadedContract:
    if name in _CACHE:
        return _CACHE[name]
    expectation = CONTRACTS[name]
    json_path, hex_path = _paths(expectation)
    if not os.path.exists(json_path) or not os.path.exists(hex_path):
        pytest.skip("%s fixture missing" % name)
    evm_blocks = list(load_ir_from_json(json_path).blocks)
    with open(hex_path) as handle:
        instructions = X86Program.from_hex(
            handle.read().strip(), base_addr=_BASE_ADDR
        ).instructions
    basic_blocks = identify_basic_blocks(instructions)
    loaded = LoadedContract(
        expectation=expectation,
        evm_blocks=evm_blocks,
        instructions=instructions,
        basic_blocks=basic_blocks,
        alignment=build_block_alignment(evm_blocks, instructions, basic_blocks),
    )
    _CACHE[name] = loaded
    return loaded


# ---------------------------------------------------------------------------
# 三合约全覆盖回归
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("name", sorted(CONTRACTS))
def test_tag_fingerprints_cover_every_evm_block(name):
    """127/127、723/723、742/742：命中数 == 块数，且逐位指纹一致。"""
    loaded = _load(name)
    expected = loaded.expectation
    evidence = loaded.alignment.evidence

    assert evidence.evm_block_count == expected.evm_blocks
    assert evidence.tag_count == expected.evm_blocks
    assert len(loaded.alignment.pc_to_addr) == expected.evm_blocks

    # 逐位一致：build 成功已蕴含，这里显式复核一遍，免得将来 zip 逻辑被改松。
    for block in loaded.evm_blocks:
        assert loaded.alignment.fingerprints[block.pc] == evm_block_fingerprint(block)


@pytest.mark.parametrize("name", sorted(CONTRACTS))
def test_mapping_is_bijective_and_monotonic(name):
    """pc↔addr 是双射，且两侧同序——单调 zip 的前提，不是副产品。"""
    loaded = _load(name)
    alignment = loaded.alignment
    assert len(alignment.addr_to_pc) == len(alignment.pc_to_addr)
    for pc, addr in alignment.pc_to_addr.items():
        assert alignment.addr_to_pc[addr] == pc
        assert alignment.pc_at_addr(addr) == pc
    ordered = [alignment.pc_to_addr[block.pc] for block in loaded.evm_blocks]
    assert ordered == sorted(ordered)


@pytest.mark.parametrize("name", sorted(CONTRACTS))
def test_return_chain_anchors_agree_completely(name):
    """第二个独立证据源：ENS 33 / CErc20 192 / Safe 166 对，100% 吻合。"""
    loaded = _load(name)
    evidence = loaded.alignment.evidence
    assert evidence.anchor_agreement_count == loaded.expectation.anchors_on_tag

    # build 里的交叉校验是"发现冲突即抛"，所以这里重新独立地算一遍吻合率，
    # 确保断言的是"零冲突"而不是"构造器碰巧没走到那段代码"。
    on_tag = 0
    agree = 0
    for anchor in extract_return_chain_anchors(loaded.instructions):
        mapped = loaded.alignment.addr_to_pc.get(anchor.x86_addr)
        if mapped is None:
            continue
        on_tag += 1
        agree += int(mapped == anchor.evm_pc)
    assert on_tag > 0
    assert agree == on_tag


# ---------------------------------------------------------------------------
# §2.4 ④(b)：区间不重叠 + 完全覆盖 + 非块代码显式登记
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("name", sorted(CONTRACTS))
def test_intervals_are_disjoint_and_cover_the_code_section(name):
    loaded = _load(name)
    alignment = loaded.alignment
    code_start, code_end = alignment.evidence.code_range

    first = loaded.instructions[0]
    last = loaded.instructions[-1]
    assert (code_start, code_end) == (first.addr, last.addr + last.size)

    regions = sorted(
        list(alignment.intervals.values()) + list(alignment.non_block_regions)
    )
    assert len(regions) == len(alignment.intervals) + len(alignment.non_block_regions)
    assert regions[0][0] == code_start
    assert regions[-1][1] == code_end
    for previous, current in zip(regions, regions[1:]):
        assert previous[0] < previous[1]  # 非空
        assert previous[1] == current[0]  # 既不重叠也无空隙

    # 每条指令恰好落在一个 region 里（④(b) 的字面义务）。
    starts = [start for start, _ in regions]
    for insn in loaded.instructions:
        index = max(i for i, start in enumerate(starts) if start <= insn.addr)
        assert regions[index][0] <= insn.addr
        assert insn.addr + insn.size <= regions[index][1]

    # 区间起点必须是块入口地址；末区间延伸到代码段末尾。
    for block in loaded.evm_blocks:
        interval = alignment.intervals[block.pc]
        assert interval[0] == alignment.pc_to_addr[block.pc]


@pytest.mark.parametrize("name", sorted(CONTRACTS))
def test_prologue_registered_as_non_block_code(name):
    """第一个 TAG 之前的 12 字节保留寄存器序言必须被显式登记，不能默默漏掉。"""
    loaded = _load(name)
    alignment = loaded.alignment
    code_start = alignment.evidence.code_range[0]
    first_tag = min(alignment.pc_to_addr.values())

    assert alignment.non_block_regions == ((code_start, first_tag),)
    assert first_tag - code_start == 12

    evidence = alignment.evidence
    assert evidence.basic_block_total == loaded.expectation.basic_block_total
    assert evidence.basic_block_covered == loaded.expectation.basic_block_covered
    # 差值 1 不是"漏了一个块"，而是入口 bb 跨在非块序言与第一个 TAG 之间
    # （identify_basic_blocks 直到第一个 jb 才切）。它被显式登记为 straddling。
    assert evidence.straddling_basic_blocks == (code_start,)
    assert (
        evidence.basic_block_covered + len(evidence.straddling_basic_blocks)
        == evidence.basic_block_total
    )


# ---------------------------------------------------------------------------
# 变异检出（方案 §6 阶段 3 反向用例）：整体拒绝而非局部错位
# ---------------------------------------------------------------------------


def _mutate(blocks: Sequence[EVMBlock], index: int, **changes) -> List[EVMBlock]:
    mutated = list(blocks)
    mutated[index] = replace(mutated[index], **changes)
    return mutated


@pytest.mark.parametrize("name", sorted(CONTRACTS))
def test_mutated_static_gas_is_rejected_wholesale(name):
    """改一个块的 static_gas ⇒ 整体拒绝。

    "整体"是重点：不返回部分映射，也不把该块跳过后让其余 N-1 个块勉强对上。
    """
    loaded = _load(name)
    count = len(loaded.evm_blocks)
    for index in (0, count // 2, count - 1):
        original = loaded.evm_blocks[index]
        mutated = _mutate(
            loaded.evm_blocks, index, static_gas=original.static_gas + 1
        )
        with pytest.raises(BlockAlignmentError) as excinfo:
            build_block_alignment(mutated, loaded.instructions, loaded.basic_blocks)
        assert excinfo.value.reason == REASON_FINGERPRINT_MISMATCH
        assert str(index) in excinfo.value.message


@pytest.mark.parametrize("name", sorted(CONTRACTS))
def test_mutated_depth_bounds_are_rejected(name):
    """min_depth / max_depth 是指纹的另两位，同样必须被检出。"""
    loaded = _load(name)
    index = len(loaded.evm_blocks) // 3
    original = loaded.evm_blocks[index]
    for changes in (
        {"min_depth": original.min_depth + 1},
        {"max_depth": original.max_depth - 1},
    ):
        with pytest.raises(BlockAlignmentError) as excinfo:
            build_block_alignment(
                _mutate(loaded.evm_blocks, index, **changes),
                loaded.instructions,
                loaded.basic_blocks,
            )
        assert excinfo.value.reason == REASON_FINGERPRINT_MISMATCH


def test_dropped_block_is_rejected_on_count():
    """少一个块 ⇒ 数量记账先失败，不给"错位一格勉强对上"任何机会。"""
    loaded = _load("ENSRegistry")
    truncated = loaded.evm_blocks[:-1]
    with pytest.raises(BlockAlignmentError) as excinfo:
        build_block_alignment(truncated, loaded.instructions, loaded.basic_blocks)
    assert excinfo.value.reason == REASON_TAG_COUNT_MISMATCH


def test_unsorted_evm_blocks_are_rejected():
    """单调 zip 的前提被破坏时必须拒绝，而不是按乱序 zip 出一份错映射。"""
    loaded = _load("ENSRegistry")
    swapped = list(loaded.evm_blocks)
    swapped[3], swapped[4] = swapped[4], swapped[3]
    with pytest.raises(BlockAlignmentError) as excinfo:
        build_block_alignment(swapped, loaded.instructions, loaded.basic_blocks)
    assert excinfo.value.reason == REASON_EVM_PC_NOT_MONOTONIC


def test_empty_inputs_are_rejected():
    loaded = _load("ENSRegistry")
    with pytest.raises(BlockAlignmentError) as excinfo:
        build_block_alignment([], loaded.instructions)
    assert excinfo.value.reason == REASON_EMPTY_INPUT
    with pytest.raises(BlockAlignmentError) as excinfo:
        build_block_alignment(loaded.evm_blocks, [])
    assert excinfo.value.reason == REASON_EMPTY_INPUT


# ---------------------------------------------------------------------------
# 过匹配回归
# ---------------------------------------------------------------------------

_WIDE_GAS_LOAD_RE = re.compile(r"^(\w+),\s*qword ptr \[r13 \+ 0x70\]$")
_WIDE_JB = frozenset({"jb", "jc", "jnae"})


def _count_wide_prefix_hits(instructions: Sequence[X86Instruction]) -> int:
    """只看 ``mov TMP,[r13+gas]; cmp TMP, <任意>; jb`` 三条的宽判据。

    这是 ``makeStaticUseGas`` 的公共前缀，动态 gas 路径
    （``checkMemoryAndCalcDynamicGas*``，发射 ``cmp TMP, dynamicCostReg`` 寄存器形式）
    照样生成。故意留在测试里而不是生产代码里：它的唯一用途是把"过匹配"这件事钉成
    可回归的数字。
    """
    stream = [insn for insn in instructions if insn.mnemonic != "nop"]
    hits = 0
    for load, cmp_insn, jcc in zip(stream, stream[1:], stream[2:]):
        if load.mnemonic != "mov" or cmp_insn.mnemonic != "cmp":
            continue
        if jcc.mnemonic not in _WIDE_JB:
            continue
        match = _WIDE_GAS_LOAD_RE.match(load.op_str)
        if match is None:
            continue
        if cmp_insn.op_str.split(",")[0].strip() != match.group(1):
            continue
        hits += 1
    return hits


@pytest.mark.parametrize("name", sorted(CONTRACTS))
def test_full_criterion_does_not_over_match(name):
    """完整判据命中数 == EVM 块数，且显著小于 3 指令宽判据。"""
    loaded = _load(name)
    expected = loaded.expectation
    assert len(find_tag_prologues(loaded.instructions)) == expected.evm_blocks

    wide = _count_wide_prefix_hits(loaded.instructions)
    assert wide == expected.wide_prefix_hits
    # ENS 2.15× / CErc20 2.11× / Safe 1.70×——方案 §2.1 记的 "2.1×" 在此复现。
    assert wide >= int(1.5 * expected.evm_blocks)


# ---------------------------------------------------------------------------
# 合成用例：真实合约打不出来的失败形态
# ---------------------------------------------------------------------------

_TAG_TEMP = "rax"


def _insn(addr: int, mnemonic: str, op_str: str, size: int = 4) -> X86Instruction:
    # bytes 只用来定 size；合成用例不经反汇编，语义由 mnemonic/op_str 给出。
    return X86Instruction(
        addr=addr, mnemonic=mnemonic, op_str=op_str, bytes=b"\x90" * size, size=size
    )


def _emit_tag(addr: int, static_gas: int, min_imm: str, max_imm: str
              ) -> List[X86Instruction]:
    """按 compileEVMTag 的顺序合成 12 条序言；立即数以字符串给，便于测编码形态。"""
    shape = [
        ("mov", "%s, qword ptr [r13 + 0x70]" % _TAG_TEMP),
        ("cmp", "%s, %d" % (_TAG_TEMP, static_gas)),
        ("jb", "0x9000"),
        ("sub", "%s, %d" % (_TAG_TEMP, static_gas)),
        ("mov", "qword ptr [r13 + 0x70], %s" % _TAG_TEMP),
        ("mov", "%s, qword ptr [r13 + 0x30]" % _TAG_TEMP),
        ("cmp", "%s, %s" % (_TAG_TEMP, min_imm)),
        ("jb", "0x9010"),
        ("cmp", "%s, %s" % (_TAG_TEMP, max_imm)),
        ("jae", "0x9020"),
        ("mov", "r14, qword ptr [r13 + 0x38]"),
        ("add", "r14, %s" % _TAG_TEMP),
    ]
    out = []
    cursor = addr
    for mnemonic, op_str in shape:
        out.append(_insn(cursor, mnemonic, op_str))
        cursor += 4
    return out


def _synthetic_block(pc: int, static_gas: int, min_depth: int, max_depth: int
                     ) -> EVMBlock:
    return EVMBlock(
        pc=pc,
        stack_depth=0,
        min_depth=min_depth,
        max_depth=max_depth,
        static_gas=static_gas,
        is_jump_target=True,
        is_inner_block=False,
        is_stop=False,
    )


def _synthetic_program(extra: Sequence[X86Instruction] = (),
                       separate_blocks: bool = True,
                       ) -> Tuple[List[EVMBlock], List[X86Instruction]]:
    """两块的合成程序：12 字节非块序言 + TAG(pc=7) + [extra] + jmp + TAG(pc=21) + ret。

    ``extra`` 用来插入返回链锚点之类的额外指令；它落在第一个块的区间内。
    ``separate_blocks=False`` 去掉两个 TAG 之间的 jmp，用来构造"区间边界劈开一个
    basic block"这一必须 fail-closed 的形态。
    """
    instructions: List[X86Instruction] = [
        _insn(0x00, "mov", "r14, qword ptr [r13 + 0x38]"),
        _insn(0x04, "add", "r14, qword ptr [r13 + 0x30]"),
        _insn(0x08, "mov", "r15, qword ptr [r13 + 0x10]"),
    ]
    instructions += _emit_tag(0x0C, static_gas=5, min_imm="32", max_imm="97")
    cursor = 0x0C + 12 * 4
    # 紧邻下一个 TAG 的必须是无条件跳转，否则 identify_basic_blocks 不在此切块，
    # 区间边界就会劈开一个 basic block（那正是本模块要 fail-closed 的情形）。
    for insn in extra:
        instructions.append(replace(insn, addr=cursor))
        cursor += insn.size
    if separate_blocks:
        instructions.append(_insn(cursor, "jmp", "0x9030"))
        cursor += 4
    instructions += _emit_tag(cursor, static_gas=9, min_imm="64", max_imm="161")
    cursor += 12 * 4
    instructions.append(_insn(cursor, "ret", ""))

    blocks = [
        _synthetic_block(pc=7, static_gas=5, min_depth=1, max_depth=3),
        _synthetic_block(pc=21, static_gas=9, min_depth=2, max_depth=5),
    ]
    return blocks, instructions


def test_synthetic_program_aligns_and_registers_prologue():
    blocks, instructions = _synthetic_program()
    alignment = build_block_alignment(blocks, instructions)
    assert alignment.pc_to_addr == {7: 0x0C, 21: 0x0C + 13 * 4}
    assert alignment.non_block_regions == ((0x00, 0x0C),)
    assert alignment.evidence.anchor_agreement_count == 0
    last = instructions[-1]
    assert alignment.intervals[21][1] == last.addr + last.size


def test_nop_padding_inside_prologue_is_skipped():
    """JCC-erratum padding 会插在序言**内部**；不跳过就会把 12 条窗口撑破。"""
    blocks, instructions = _synthetic_program()
    padded: List[X86Instruction] = []
    for insn in instructions:
        padded.append(insn)
        if insn.addr == 0x0C + 4 * 4:  # 序言中段
            padded.append(_insn(insn.addr + insn.size, "nop", "", size=0))
    alignment = build_block_alignment(blocks, padded)
    assert alignment.pc_to_addr[7] == 0x0C


def test_max_int64_depth_bound_round_trips():
    """max_depth 初值是 Go 的 math.MaxInt64，``*32+1`` 回绕成 -31。"""
    blocks, instructions = _synthetic_program()
    blocks[0] = replace(blocks[0], max_depth=GO_MAX_INT64)
    patched = []
    for insn in instructions:
        if insn.addr == 0x0C + 8 * 4:  # 序言第 9 条：cmp TMP, maxDepth*32+1
            insn = replace(insn, op_str="%s, 0xffffffffffffffe1" % _TAG_TEMP)
        patched.append(insn)
    alignment = build_block_alignment(blocks, patched)
    assert alignment.fingerprints[7].max_depth_bound == -31


def test_return_chain_anchor_conflict_is_rejected():
    """指纹映射与返回链锚点冲突 ⇒ 整体拒绝：两个独立证据源，没有偏信哪个的理由。"""
    # 插入 2 条 extra（8 字节）后第二个 TAG 的地址：序言 12 + 首个 TAG 48 + extra 8 + jmp 4
    second_tag = 0x0C + 12 * 4 + 8 + 4

    good_anchor = [
        _insn(0, "cmp", "rbx, 21"),
        _insn(0, "je", "0x%x" % second_tag),
    ]
    blocks, instructions = _synthetic_program(extra=good_anchor)
    alignment = build_block_alignment(blocks, instructions)
    assert alignment.pc_to_addr[21] == second_tag
    assert alignment.evidence.anchor_agreement_count == 1

    bad_anchor = [
        _insn(0, "cmp", "rbx, 22"),  # 22 不是任何块的 pc
        _insn(0, "je", "0x%x" % second_tag),
    ]
    blocks, instructions = _synthetic_program(extra=bad_anchor)
    with pytest.raises(BlockAlignmentError) as excinfo:
        build_block_alignment(blocks, instructions)
    assert excinfo.value.reason == REASON_ANCHOR_DISAGREEMENT


def test_interval_boundary_splitting_a_basic_block_is_rejected():
    """区间边界劈开 basic block ⇒ 拒绝。

    "每条指令恰属于一个区间"此时仍成立，但"每个 basic block 恰属于一个区间"不再成
    立，下游按 bb 编排就会静默取到半个块——正是 §2.5 说的"必须拒绝、不得局部修补"。
    """
    blocks, instructions = _synthetic_program(separate_blocks=False)
    with pytest.raises(BlockAlignmentError) as excinfo:
        build_block_alignment(blocks, instructions)
    assert excinfo.value.reason == REASON_INTERVAL_NOT_BLOCK_ALIGNED


def test_certificate_fingerprint_is_deterministic_and_address_sensitive():
    """指纹进证书 key：同输入稳定，地址一变就失效。"""
    loaded = _load("ENSRegistry")
    again = build_block_alignment(
        loaded.evm_blocks, loaded.instructions, loaded.basic_blocks
    )
    assert again.fingerprint == loaded.alignment.fingerprint

    json_path, hex_path = _paths(loaded.expectation)
    with open(hex_path) as handle:
        shifted = X86Program.from_hex(
            handle.read().strip(), base_addr=0x10000
        ).instructions
    moved = build_block_alignment(loaded.evm_blocks, shifted)
    assert moved.fingerprint != loaded.alignment.fingerprint
    assert set(moved.pc_to_addr) == set(loaded.alignment.pc_to_addr)


def test_prologue_length_constant_matches_matcher():
    """12 这个数字在 docstring、matcher、跳步三处出现，用常量钉住。"""
    assert TAG_PROLOGUE_LENGTH == 12
    _, instructions = _synthetic_program()
    truncated = instructions[:3] + instructions[3 : 3 + TAG_PROLOGUE_LENGTH - 1]
    assert find_tag_prologues(truncated) == ()
