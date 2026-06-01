from pathlib import Path

import pytest
from z3 import (
    BitVecSort,
    BitVecVal,
    K,
    Solver,
    Store,
    unsat,
)

from common.calldata import calldataload_word
from state.smt_state import MemoryDomain, SMTState
from x86_64.calldataload_summary import (
    CallDataLoadSummary,
    CallDataLoadSummaryMatchError,
    ConstLimbLocation,
    _collect_summary_clobber_registers,
    apply_calldataload_summary,
    discover_calldataload_summaries,
    validate_calldataload_summary_mode,
)
from x86_64.cfg import identify_basic_blocks
from x86_64.disassembler import disassemble_hex
from x86_64.models import Register, X86Block


def _calldata_array(values):
    arr = K(BitVecSort(64), BitVecVal(0, 8))
    for idx, value in enumerate(values):
        arr = Store(arr, BitVecVal(idx, 64), BitVecVal(value, 8))
    return arr


def _assert_bv_eq(expr, expected, bits):
    solver = Solver()
    solver.add(expr != BitVecVal(expected, bits))
    assert solver.check() == unsat


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


def test_calldataload_word_returns_zero_past_end_and_on_overflow():
    data = _calldata_array([0xAB])
    past_end = calldataload_word(data, BitVecVal(1, 64), BitVecVal(5, 256))
    overflow = calldataload_word(data, BitVecVal(32, 64), BitVecVal(1 << 64, 256))

    _assert_bv_eq(past_end, 0, 256)
    _assert_bv_eq(overflow, 0, 256)


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


def test_matcher_skips_dynamic_low_offsets_for_wrap_soundness():
    hex_code = Path("tests/data/muti_block_08.hex").read_text()
    blocks = identify_basic_blocks(disassemble_hex(hex_code, 0))

    summaries = discover_calldataload_summaries(blocks)

    assert len(summaries) == 1
    assert all(
        isinstance(summary.offset_limb_locs[0], ConstLimbLocation)
        for summary in summaries.values()
    )
    with pytest.raises(CallDataLoadSummaryMatchError, match="dynamic"):
        discover_calldataload_summaries(blocks, strict=True)


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


def test_calldataload_summary_mode_validation():
    assert validate_calldataload_summary_mode("fallback") == "fallback"
    with pytest.raises(ValueError):
        validate_calldataload_summary_mode("always")
