"""compileEVMDivWithReg summary: matcher, per-slice lemma (fail-closed) and precondition."""

import pytest
from z3 import BitVec

from state.smt_state import SMTState
from tests.integration.test_single_ins_equivalence import (
    X86_DIV_CORE_HEX_SEQUENCE,
    X86_MOD_CORE_HEX_SEQUENCE,
    X86_SDIV_CORE_HEX_SEQUENCE,
)
from x86_64.cfg import identify_basic_blocks
from x86_64.disassembler import disassemble_hex
from x86_64.models import Register
from x86_64.summaries import X86SummaryConfig, build_x86_summary_runtime
from x86_64.summaries.base import SummaryPreconditionError
from x86_64.summaries.div import discover_div_summaries
from x86_64.summaries.div_proof import DivProofError, clear_proof_cache, prove_div_slice_cached


@pytest.fixture(autouse=True)
def _isolated_proof_cache():
    clear_proof_cache()
    yield
    clear_proof_cache()


def _blocks(hex_code):
    return identify_basic_blocks(disassemble_hex(hex_code, 0))


def test_matcher_recovers_div_slice_layout():
    [summary] = discover_div_summaries(_blocks(X86_DIV_CORE_HEX_SEQUENCE), strict=True)
    p = summary.payload
    assert (p.entry_addr, p.continuation_addr, p.resume_addr) == (0, 0xDF, 0xD3)
    assert p.dividend_offsets == (-0x20, -0x18, -0x10, -0x08)
    assert p.divisor_offsets == (-0x40, -0x38, -0x30, -0x28)
    assert (p.builtin_index, p.builtin_stack_pointer) == (4, 0)
    assert set(p.clobber_registers) == {Register.RAX, Register.RBX, Register.RCX, Register.RDX, Register.RSI}
    assert summary.is_cross_block and summary.continuation.block_addr == 0xDF


def test_matcher_finds_every_div_inside_sdiv_and_nothing_in_mod():
    assert len(discover_div_summaries(_blocks(X86_SDIV_CORE_HEX_SEQUENCE), strict=True)) == 4
    assert discover_div_summaries(_blocks(X86_MOD_CORE_HEX_SEQUENCE)) == []


def test_lemma_proves_every_path_including_builtin_bridge():
    blocks = _blocks(X86_DIV_CORE_HEX_SEQUENCE)
    [summary] = discover_div_summaries(blocks, strict=True)
    lemma, status = prove_div_slice_cached(summary, blocks)
    assert status == "proven" and lemma.complete and lemma.path_count == 4
    assert prove_div_slice_cached(summary, blocks)[1] == "cache_hits"


def test_lemma_rejects_a_slice_whose_builtin_reads_the_wrong_stack_slots():
    # `mov qword [r13+0x28], 0` -> 0x10: the matcher still accepts it, but Go's
    # builtin then pops x/y from other slots, so the raw slice is not DIV.
    hex_code = X86_DIV_CORE_HEX_SEQUENCE.replace("49c7452800000000c3", "49c7452810000000c3", 1)
    assert hex_code != X86_DIV_CORE_HEX_SEQUENCE
    blocks = _blocks(hex_code)
    [summary] = discover_div_summaries(blocks, strict=True)
    with pytest.raises(DivProofError, match="effect_"):
        prove_div_slice_cached(summary, blocks)
    with pytest.raises(DivProofError) as cached:
        prove_div_slice_cached(summary, blocks)
    assert cached.value.from_cache


def test_apply_rejects_unproved_stack_geometry():
    blocks = _blocks(X86_DIV_CORE_HEX_SEQUENCE)
    runtime = build_x86_summary_runtime(blocks, summary_config=X86SummaryConfig.enabled(div="fallback"))
    [summary] = runtime.summaries
    state = SMTState()
    state.x86_registers.set_register(Register.R14, BitVec("r14_unrelated", 64))
    with pytest.raises(SummaryPreconditionError, match="stack geometry"):
        runtime.apply(summary, state)
    assert runtime.should_fallback_on_precondition("div")


def test_block_runtime_instantiates_the_lemma_with_a_complete_certificate():
    from verification.block_summaries import VerifiedSummaryRuntime

    blocks = _blocks(X86_DIV_CORE_HEX_SEQUENCE)
    runtime = VerifiedSummaryRuntime(blocks, X86SummaryConfig.enabled(div="strict"), timeout_ms=30000)
    [summary] = runtime.summaries
    state = SMTState.create_initial_state(num_inputs=2)
    state.x86_registers.set_register(Register.R14, state.callengine_stack_base + state.callengine_stack_byte_offset)
    state.x86_registers.set_register(Register.R15, state.callengine_memory_base)
    runtime.apply(summary, state)
    [certificate] = runtime.certificates
    names = {o.name for o in certificate.obligations}
    assert certificate.complete and certificate.raw_path_count == 4
    assert {"entry", "div_stack_geometry", "coverage", "effect_3"} <= names

    state.x86_registers.set_register(Register.R14, BitVec("r14_unrelated", 64))
    with pytest.raises(SummaryPreconditionError, match="div_stack_geometry"):
        runtime.apply(summary, state)
    assert len(runtime.certificates) == 1
