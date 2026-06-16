from z3 import BitVecVal, Solver, unsat

from common.uint256 import Uint256
from state.smt_state import MemoryDomain, SMTState
from tests.integration.test_single_ins_refinement import X86_MUL_CORE_HEX_SEQUENCE
from x86_64.cfg import identify_basic_blocks
from x86_64.disassembler import disassemble_hex
from x86_64.models import Register
from x86_64.program import X86Program
from x86_64.summaries.mul import (
    MUL_SUMMARY_KIND,
    ConstLimbLocation,
    MulSummaryMatchError,
    RegisterLimbLocation,
    StackLimbLocation,
    apply_mul_summary,
    discover_mul_summaries,
)
from x86_64.summaries.registry import X86SummaryConfig


def _blocks(hex_code: str):
    return identify_basic_blocks(disassemble_hex(hex_code, 0))


def _full_mul_instruction_hex() -> list[str]:
    return [insn.bytes.hex() for insn in disassemble_hex(X86_MUL_CORE_HEX_SEQUENCE, 0)]


def _zero_optimized_mul_hex(
    *,
    q1_load_hex: str | None = None,
    p1_load_hex: str | None = None,
) -> str:
    insns = _full_mul_instruction_hex()
    if q1_load_hex is not None:
        for index in (0, 5, 12, 19):
            insns[index] = q1_load_hex
    if p1_load_hex is not None:
        insns[1] = p1_load_hex

    q2_zero = "4989d9"  # mov r9, rbx
    q3_zero = "4989f2"  # mov r10, rsi
    q4_zero = "4989fb"  # mov r11, rdi
    return "".join(insns[:25] + [q2_zero, q3_zero, q4_zero] + insns[70:74])


def _state_with_stack_words(p_value: int, q_value: int) -> SMTState:
    state = SMTState()
    state.x86_registers.set_register(Register.R14, BitVecVal(0x1000, 64))
    for offset, limb in zip(
        (-64, -56, -48, -40),
        _uint256_limbs(p_value),
        strict=True,
    ):
        _store_stack_limb(state, offset, limb)
    for offset, limb in zip(
        (-32, -24, -16, -8),
        _uint256_limbs(q_value),
        strict=True,
    ):
        _store_stack_limb(state, offset, limb)
    return state


def _uint256_limbs(value: int) -> tuple[int, int, int, int]:
    value %= 1 << 256
    return tuple((value >> (64 * index)) & ((1 << 64) - 1) for index in range(4))


def _store_stack_limb(state: SMTState, offset: int, value: int) -> None:
    base = state.x86_registers.get_register(Register.R14)
    state.x86_memory = state.x86_memory.store_limb(
        base + BitVecVal(offset, 64),
        BitVecVal(value, 64),
        domain=MemoryDomain.STACK,
    )


def _load_stack_word(state: SMTState, offsets: tuple[int, int, int, int]):
    base = state.x86_registers.get_register(Register.R14)
    z0, z1, z2, z3 = (
        state.x86_memory.load_limb(
            base + BitVecVal(offset, 64),
            domain=MemoryDomain.STACK,
        )
        for offset in offsets
    )
    return Uint256(z0, z1, z2, z3).to_bv256()


def _assert_bv_eq(expr, expected: int, bits: int = 256) -> None:
    solver = Solver()
    solver.add(expr != BitVecVal(expected % (1 << bits), bits))
    assert solver.check() == unsat


def test_full_mul_template_discovers_one_summary():
    summaries = discover_mul_summaries(_blocks(X86_MUL_CORE_HEX_SEQUENCE), strict=True)

    assert len(summaries) == 1
    summary = next(iter(summaries.values()))
    assert summary.entry_addr == 0
    assert summary.start_instruction_index == 0
    assert summary.continuation_instruction_index == 74
    assert summary.result_stack_offsets == (-64, -56, -48, -40)
    assert summary.p_limb_locs == (
        StackLimbLocation(-64),
        StackLimbLocation(-56),
        StackLimbLocation(-48),
        StackLimbLocation(-40),
    )
    assert summary.q_limb_locs == (
        StackLimbLocation(-32),
        StackLimbLocation(-24),
        StackLimbLocation(-16),
        StackLimbLocation(-8),
    )
    assert {Register.RAX, Register.RDX, Register.RCX, Register.R8}.issubset(
        set(summary.clobber_registers)
    )


def test_apply_mul_summary_matches_uint256_multiplication():
    summary = next(iter(discover_mul_summaries(_blocks(X86_MUL_CORE_HEX_SEQUENCE)).values()))
    p_value = 0x0123456789ABCDEF_FEDCBA9876543210_1111222233334444_5555666677778888
    q_value = 0xFFEEDDCCBBAA9988_7766554433221100_0123456789ABCDEF_F0E1D2C3B4A59687
    state = _state_with_stack_words(p_value, q_value)

    new_state = apply_mul_summary(summary, state, fresh_prefix="test_mul")
    result = _load_stack_word(new_state, summary.result_stack_offsets)

    _assert_bv_eq(result, p_value * q_value)


def test_zero_optimized_q2_q3_q4_template_discovers_and_applies():
    hex_code = _zero_optimized_mul_hex()
    summary = next(iter(discover_mul_summaries(_blocks(hex_code), strict=True).values()))

    assert summary.q_limb_locs[1:] == (
        ConstLimbLocation(0),
        ConstLimbLocation(0),
        ConstLimbLocation(0),
    )

    p_value = (3 << 192) + (5 << 128) + (7 << 64) + 11
    q_value = 13
    state = _state_with_stack_words(p_value, q_value)
    new_state = apply_mul_summary(summary, state, fresh_prefix="test_mul_zero")

    _assert_bv_eq(_load_stack_word(new_state, summary.result_stack_offsets), p_value * q_value)


def test_mul_template_parses_register_immediate_and_stack_limb_locations():
    # mov rax, r12 for all q1 loads; mov rcx, 7 for p1.
    hex_code = _zero_optimized_mul_hex(
        q1_load_hex="4c89e0",
        p1_load_hex="48c7c107000000",
    )
    summary = next(iter(discover_mul_summaries(_blocks(hex_code), strict=True).values()))

    assert summary.q_limb_locs[0] == RegisterLimbLocation(Register.R12)
    assert summary.p_limb_locs[0] == ConstLimbLocation(7)
    assert summary.p_limb_locs[1:] == (
        StackLimbLocation(-56),
        StackLimbLocation(-48),
        StackLimbLocation(-40),
    )

    p_value = (17 << 192) + (19 << 128) + (23 << 64) + 7
    q_value = 29
    state = _state_with_stack_words(p_value, 0)
    state.x86_registers.set_register(Register.R12, BitVecVal(q_value, 64))
    new_state = apply_mul_summary(summary, state, fresh_prefix="test_mul_locs")

    _assert_bv_eq(_load_stack_word(new_state, summary.result_stack_offsets), p_value * q_value)


def test_mul_summary_does_not_cover_spill_prefix_or_restore_suffix():
    prefix = "4c89e0"  # mov rax, r12
    suffix = "4c89e0"  # mov rax, r12
    blocks = _blocks(prefix + X86_MUL_CORE_HEX_SEQUENCE + suffix)

    summary = next(iter(discover_mul_summaries(blocks, strict=True).values()))

    assert summary.start_instruction_index == 1
    assert summary.continuation_instruction_index == 75


def test_strict_reports_malformed_mul_like_slice():
    insns = _full_mul_instruction_hex()
    malformed = "".join(insns[:-1])

    try:
        discover_mul_summaries(_blocks(malformed), strict=True)
    except MulSummaryMatchError as exc:
        assert "unmatched MUL-like" in str(exc)
    else:
        raise AssertionError("strict discovery should reject malformed MUL-like slice")


def test_mul_summary_runtime_stats_record_discovery_and_hit():
    program = X86Program.from_hex(X86_MUL_CORE_HEX_SEQUENCE, base_addr=0)
    state = SMTState()
    state.x86_registers.set_register(Register.R14, BitVecVal(0x1000, 64))

    program.to_z3(
        state,
        enable_go_bridge=False,
        summary_config=X86SummaryConfig.enabled(mul="fallback"),
    )

    stats = program.last_summary_stats[MUL_SUMMARY_KIND]
    assert stats["discovered"] == 1
    assert stats["hits"] == 1
