from pathlib import Path

import pytest
from z3 import (
    And,
    BitVec,
    BitVecSort,
    BitVecVal,
    If,
    K,
    Solver,
    Store,
    ULE,
    ULT,
    Z3_OP_UNINTERPRETED,
    sat,
    unsat,
)

from common.calldata import calldataload_word
from state.smt_state import MemoryDomain, SMTState
from x86_64.cfg import identify_basic_blocks
from x86_64.cfg_executor import X86SymbolicExecutor
from x86_64.disassembler import disassemble_hex
from x86_64.models import Register, X86Block
from x86_64.summaries.base import SummaryDiscoveryContext, X86SummaryPlugin
from x86_64.summaries.calldataload import (
    CALLDATALOAD_SUMMARY_KIND,
    CallDataLoadSummary,
    CallDataLoadSummaryMatchError,
    CallDataLoadSummarySpec,
    ConstLimbLocation,
    RegisterLimbLocation,
    _collect_summary_clobber_registers,
    apply_calldataload_summary,
    discover_calldataload_summaries,
)
from x86_64.summaries.mul import MUL_SUMMARY_KIND
from x86_64.summaries.registry import (
    TRUSTED_SUMMARY_CONFIG,
    X86SummaryConfig,
    build_x86_summary_runtime,
)


def _calldata_array(values):
    arr = K(BitVecSort(64), BitVecVal(0, 8))
    for idx, value in enumerate(values):
        arr = Store(arr, BitVecVal(idx, 64), BitVecVal(value, 8))
    return arr


def _assert_bv_eq(expr, expected, bits):
    solver = Solver()
    solver.add(expr != BitVecVal(expected, bits))
    assert solver.check() == unsat


def _mentions_uninterpreted_const(expr, name):
    seen = set()
    stack = [expr]
    while stack:
        cur = stack.pop()
        try:
            key = cur.hash()
        except Exception:
            continue
        if key in seen:
            continue
        seen.add(key)
        try:
            decl = cur.decl()
            if (
                decl.kind() == Z3_OP_UNINTERPRETED
                and decl.name() == name
                and len(cur.children()) == 0
            ):
                return True
            stack.extend(cur.children())
        except Exception:
            continue
    return False


def test_calldataload_word_reads_full_word():
    data = list(range(32))
    expr = calldataload_word(
        _calldata_array(data),
        BitVecVal(32, 64),
        BitVecVal(0, 256),
    )
    _assert_bv_eq(expr, int.from_bytes(bytes(data), "big"), 256)


def test_calldataload_word_zero_pads_short_read():
    expr = calldataload_word(
        _calldata_array([0x12, 0x34]),
        BitVecVal(2, 64),
        BitVecVal(0, 256),
    )
    expected = (0x12 << 248) | (0x34 << 240)
    _assert_bv_eq(expr, expected, 256)


def test_abstract_calldataload_keeps_selector_word_byte_precise():
    data = [0x12, 0x34, 0x56, 0x78] + [0] * 28
    expr = calldataload_word(
        _calldata_array(data),
        BitVecVal(32, 64),
        BitVecVal(0, 256),
        abstract=True,
    )

    _assert_bv_eq(expr, int.from_bytes(bytes(data), "big"), 256)


def test_abstract_calldataload_abi_word_is_unconstrained_at_end():
    expr = calldataload_word(
        _calldata_array([0x12, 0x34, 0x56, 0x78]),
        BitVecVal(4, 64),
        BitVecVal(4, 256),
        abstract=True,
    )

    solver = Solver()
    solver.add(expr != BitVecVal(0, 256))
    assert solver.check() == sat


def test_abstract_calldataload_concrete_abi_word_ignores_size_symbol():
    size = BitVec("abstract_calldataload_size", 64)
    expr = calldataload_word(
        _calldata_array([0x12, 0x34, 0x56, 0x78]),
        size,
        BitVecVal(4, 256),
        abstract=True,
    )

    assert not _mentions_uninterpreted_const(expr, "abstract_calldataload_size")


def test_abstract_calldataload_abstracts_abi_partial_read():
    expr = calldataload_word(
        _calldata_array([0, 1, 2, 3, 0xAB, 0xCD]),
        BitVecVal(6, 64),
        BitVecVal(4, 256),
        abstract=True,
    )
    expected = (0xAB << 248) | (0xCD << 240)

    solver = Solver()
    solver.add(expr != BitVecVal(expected, 256))
    assert solver.check() == sat


def test_calldataload_word_returns_zero_past_end_and_on_overflow():
    data = _calldata_array([0xAB])
    past_end = calldataload_word(data, BitVecVal(1, 64), BitVecVal(5, 256))
    overflow = calldataload_word(data, BitVecVal(32, 64), BitVecVal(1 << 64, 256))

    _assert_bv_eq(past_end, 0, 256)
    _assert_bv_eq(overflow, 0, 256)


def test_symbolic_calldataload_byte_guard_implies_no_wrap():
    """旧的 compact guard 已经等价于显式 no-wrap + in-bounds guard。"""
    calldatasize = BitVec("calldataload_guard_size", 64)
    offset = BitVec("calldataload_guard_offset", 64)
    uint64_limit = (1 << 64) - 1
    effective_start = If(ULT(calldatasize, offset), calldatasize, offset)
    remaining = calldatasize - effective_start

    for i in range(32):
        i_bv = BitVecVal(i, 64)
        compact_guard = ULT(i_bv, remaining)
        explicit_guard = And(
            ULE(offset, BitVecVal(uint64_limit - i, 64)),
            ULT(offset + i_bv, calldatasize),
        )

        solver = Solver()
        solver.add(compact_guard != explicit_guard)
        assert solver.check() == unsat

        solver = Solver()
        solver.add(compact_guard, effective_start + i_bv != offset + i_bv)
        assert solver.check() == unsat


def test_perf_erc20_calldataload_matcher_discovers_five_summaries():
    hex_code = Path("tests/data/perf_erc20_lite.hex").read_text()
    blocks = identify_basic_blocks(disassemble_hex(hex_code, 0))

    summaries = discover_calldataload_summaries(blocks, strict=True)
    ordered = [summaries[addr] for addr in sorted(summaries)]

    assert [summary.entry_addr for summary in ordered] == [
        0x6B0,
        0x182A,
        0x266A,
        0x36AA,
        0x4067,
    ]
    assert [summary.exit_addr for summary in ordered] == [
        0x9FE,
        0x1B77,
        0x29B7,
        0x39F7,
        0x43BE,
    ]
    assert [summary.result_stack_offset for summary in ordered] == [0, -32, -32, -32, 0]
    assert [summary.entry_instruction_index for summary in ordered] == [0, 0, 0, 0, 3]
    assert [
        summary.offset_limb_locs[0].value
        for summary in ordered
        if isinstance(summary.offset_limb_locs[0], ConstLimbLocation)
    ] == [0, 4, 36, 4, 36]


def test_calldataload_spec_continuation_matches_discovered_exit_addr():
    hex_code = Path("tests/data/perf_erc20_lite.hex").read_text()
    blocks = identify_basic_blocks(disassemble_hex(hex_code, 0))
    blocks_by_addr = {block.start_addr: block for block in blocks}
    block_index = {block.start_addr: index for index, block in enumerate(blocks)}

    discovered = discover_calldataload_summaries(blocks, strict=True)
    ctx = SummaryDiscoveryContext(blocks, blocks_by_addr, block_index)
    generic = list(CallDataLoadSummarySpec().discover(ctx, strict=True))

    assert len(generic) == len(discovered)
    for summary in generic:
        discovered_summary = discovered[summary.entry_addr]
        assert summary.start_key == (
            discovered_summary.entry_addr,
            discovered_summary.entry_instruction_index,
        )
        assert summary.continuation.block_addr == discovered_summary.exit_addr
        assert summary.continuation.instruction_index == 0


def test_calldataload_summary_merge_point_exclusion_matches_discovered_exit_addrs():
    hex_code = Path("tests/data/perf_erc20_lite.hex").read_text()
    blocks = identify_basic_blocks(disassemble_hex(hex_code, 0))

    discovered = discover_calldataload_summaries(blocks, strict=True)
    summary_runtime = build_x86_summary_runtime(
        blocks,
        summary_config=X86SummaryConfig.enabled(calldataload="fallback"),
    )
    executor = X86SymbolicExecutor(
        blocks,
        enable_merge=True,
        summary_runtime=summary_runtime,
    )
    calldataload_summaries = {
        summary.payload.entry_addr: summary.payload
        for summary in summary_runtime.summaries_for_kind(CALLDATALOAD_SUMMARY_KIND)
    }

    assert set(calldataload_summaries) == set(discovered)
    for entry_addr, payload in calldataload_summaries.items():
        assert isinstance(payload, CallDataLoadSummary)
        assert payload.entry_addr == entry_addr
        assert payload.exit_addr == discovered[entry_addr].exit_addr
    for summary in discovered.values():
        assert summary.exit_addr not in executor.merge_points


def test_x86_summary_runtime_defaults_to_no_builtin_summaries():
    hex_code = Path("tests/data/perf_erc20_lite.hex").read_text()
    blocks = identify_basic_blocks(disassemble_hex(hex_code, 0))

    summary_runtime = build_x86_summary_runtime(blocks)

    assert summary_runtime.summaries == []
    assert summary_runtime.summaries_for_kind(CALLDATALOAD_SUMMARY_KIND) == []
    assert summary_runtime.mode_for_kind(CALLDATALOAD_SUMMARY_KIND) is None


def test_trusted_summary_config_is_immutable_and_explicitly_enables_calldataload():
    with pytest.raises(TypeError):
        TRUSTED_SUMMARY_CONFIG.builtin_modes["oops"] = "fallback"

    assert TRUSTED_SUMMARY_CONFIG.builtin_modes[CALLDATALOAD_SUMMARY_KIND] == "fallback"
    assert TRUSTED_SUMMARY_CONFIG.builtin_modes[MUL_SUMMARY_KIND] == "fallback"


def test_x86_summary_runtime_rejects_unknown_builtin_summary_kind():
    with pytest.raises(ValueError, match="unknown builtin x86 summary plugin"):
        build_x86_summary_runtime(
            [],
            summary_config=X86SummaryConfig.enabled(unknown="fallback"),
        )


def test_matcher_flags_dynamic_low_offsets_as_requiring_concrete_offset():
    """discovery 阶段的字段标记；apply 阶段实际拒绝行为见
    test_apply_rejects_dynamic_low_offset_that_cannot_be_proven_safe。"""
    hex_code = Path("tests/data/muti_block_08.hex").read_text()
    blocks = identify_basic_blocks(disassemble_hex(hex_code, 0))

    summaries = discover_calldataload_summaries(blocks)

    assert len(summaries) == 3
    dynamic = [
        summary
        for summary in summaries.values()
        if not isinstance(summary.offset_limb_locs[0], ConstLimbLocation)
    ]
    assert len(dynamic) == 2
    assert all(summary.require_concrete_offset for summary in dynamic)


def test_strict_reports_malformed_calldataload_like_zero_block():
    hex_code = Path("tests/data/perf_erc20_lite.hex").read_text()
    blocks = identify_basic_blocks(disassemble_hex(hex_code, 0))
    mutated_blocks = list(blocks)

    zero_idx = next(
        idx for idx, block in enumerate(mutated_blocks)
        if block.start_addr == 0x9DF
    )
    zero_block = mutated_blocks[zero_idx]
    mutated_blocks[zero_idx] = X86Block(
        start_addr=zero_block.start_addr,
        end_addr=zero_block.end_addr,
        instructions=zero_block.instructions[:3],
        tag_marker=zero_block.tag_marker,
        is_jump_target=zero_block.is_jump_target,
        corresponding_evm_block=zero_block.corresponding_evm_block,
    )

    fallback_summaries = discover_calldataload_summaries(mutated_blocks)
    assert 0x6B0 not in fallback_summaries

    with pytest.raises(CallDataLoadSummaryMatchError, match="0x6b0"):
        discover_calldataload_summaries(mutated_blocks, strict=True)


def test_block_middle_summary_clobbers_ignore_executed_prefix():
    insns = disassemble_hex(
        # prefix: mov r10, 0x1234
        # summary body: mov rax, 0; mov rcx, rax
        "49c7c23412000048c7c0000000004889c1",
        0x100,
    )
    block = X86Block(
        start_addr=0x100,
        end_addr=0x100 + sum(insn.size for insn in insns),
        instructions=insns,
    )

    clobbers = _collect_summary_clobber_registers(
        [block],
        entry_idx=0,
        exit_idx=1,
        entry_instruction_index=1,
    )

    assert Register.R10 not in clobbers
    assert Register.RAX in clobbers
    assert Register.RCX in clobbers


def test_apply_calldataload_summary_writes_x86_stack_word():
    state = SMTState()
    state.calldata = _calldata_array([0xAA, 0xBB])
    state.callengine_input_size_bytes = BitVecVal(2, 64)
    state.x86_registers.set_register(Register.R14, BitVecVal(0x1000, 64))

    summary = CallDataLoadSummary(
        entry_addr=0x10,
        exit_addr=0x20,
        zero_addr=0x30,
        partial_addr=0x40,
        entry_instruction_index=0,
        result_stack_offset=-32,
        offset_limb_locs=(
            ConstLimbLocation(0),
            ConstLimbLocation(0),
            ConstLimbLocation(0),
            ConstLimbLocation(0),
        ),
        clobber_registers=(Register.RAX,),
        internal_block_addrs=(),
    )

    new_state = apply_calldataload_summary(summary, state, fresh_prefix="test_summary")
    loaded = new_state.x86_memory.load_256bit(
        BitVecVal(0x1000 - 32, 64),
        domain=MemoryDomain.STACK,
    )
    expected = (0xAA << 248) | (0xBB << 240)
    _assert_bv_eq(loaded, expected, 256)
    assert new_state.assumptions


def test_apply_calldataload_summary_records_no_overflow_assumption():
    state = SMTState()
    state.callengine_input_size_bytes = BitVecVal(32, 64)
    state.x86_registers.set_register(Register.R14, BitVecVal(0x1000, 64))
    high_limb = BitVec("calldataload_summary_high_limb", 64)
    state.x86_registers.set_register(Register.RAX, high_limb)

    summary = CallDataLoadSummary(
        entry_addr=0x10,
        exit_addr=0x20,
        zero_addr=0x30,
        partial_addr=0x40,
        entry_instruction_index=0,
        result_stack_offset=-32,
        offset_limb_locs=(
            ConstLimbLocation(0),
            ConstLimbLocation(0),
            ConstLimbLocation(0),
            RegisterLimbLocation(Register.RAX),
        ),
        clobber_registers=(),
        internal_block_addrs=(),
    )

    new_state = apply_calldataload_summary(summary, state, fresh_prefix="test_summary")

    assert new_state.assumptions
    solver = Solver()
    solver.add(*new_state.assumptions)
    solver.add(high_limb != BitVecVal(0, 64))
    assert solver.check() == unsat


def test_apply_rejects_dynamic_low_offset_that_cannot_be_proven_safe():
    """require_concrete_offset=True 的 summary 若运行时 offset 无法化简为安全
    的具体值，apply 阶段必须拒绝，否则真实 x64 ``offset+32`` 回绕会走错
    fast/partial path，而 Z3 model 完全不知情（soundness gap）。"""
    state = SMTState()
    state.callengine_input_size_bytes = BitVecVal(32, 64)
    state.x86_registers.set_register(Register.R14, BitVecVal(0x1000, 64))
    symbolic_low_limb = BitVec("calldataload_summary_low_limb", 64)
    state.x86_registers.set_register(Register.RAX, symbolic_low_limb)

    summary = CallDataLoadSummary(
        entry_addr=0x10,
        exit_addr=0x20,
        zero_addr=0x30,
        partial_addr=0x40,
        entry_instruction_index=0,
        result_stack_offset=-32,
        offset_limb_locs=(
            RegisterLimbLocation(Register.RAX),
            ConstLimbLocation(0),
            ConstLimbLocation(0),
            ConstLimbLocation(0),
        ),
        clobber_registers=(),
        internal_block_addrs=(),
        require_concrete_offset=True,
    )

    with pytest.raises(CallDataLoadSummaryMatchError):
        apply_calldataload_summary(summary, state, fresh_prefix="test_summary")


def test_calldataload_summary_plugin_mode_validation():
    plugin = X86SummaryPlugin(CallDataLoadSummarySpec(), mode="fallback")
    assert plugin.mode == "fallback"
    with pytest.raises(ValueError):
        X86SummaryPlugin(CallDataLoadSummarySpec(), mode="always")
