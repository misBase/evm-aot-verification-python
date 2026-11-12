"""Shift dispatches fold only after complete raw replay, including every exit."""
from dataclasses import replace

import pytest

from state.smt_state import SMTState
from state.x86_state import PointerTag
from tests.integration.test_single_ins_equivalence import (
    X86_SAR_CORE_HEX_SEQUENCE, X86_SHL_CORE_HEX_SEQUENCE, X86_SHR_CORE_HEX_SEQUENCE,
)
from x86_64.cfg import identify_basic_blocks
from x86_64.disassembler import disassemble_hex
from x86_64.models import Register
from x86_64.summaries import X86SummaryConfig, build_x86_summary_runtime
from x86_64.summaries.base import SummaryPreconditionError
from x86_64.summaries.shift import discover_shift_summaries
from x86_64.summaries.shift_proof import (
    ShiftProofError, clear_proof_cache, prove_shift_slice, prove_shift_slice_cached,
)


def _blocks(hex_code):
    return identify_basic_blocks(disassemble_hex(hex_code))


@pytest.fixture(autouse=True)
def _isolated_cache():
    clear_proof_cache()
    yield
    clear_proof_cache()


@pytest.mark.parametrize("code,directions", [
    (X86_SHR_CORE_HEX_SEQUENCE, ["right"]),
    (X86_SHL_CORE_HEX_SEQUENCE, ["left"]),
    (X86_SAR_CORE_HEX_SEQUENCE, ["right", "ones-right"]),
])
def test_shift_matcher(code, directions):
    summaries = discover_shift_summaries(_blocks(code), strict=True)
    assert [s.payload.direction for s in summaries] == directions
    assert all(s.payload.value_offsets == (-64, -56, -48, -40) for s in summaries)


@pytest.mark.parametrize("code", [X86_SHR_CORE_HEX_SEQUENCE, X86_SHL_CORE_HEX_SEQUENCE,
                                  X86_SAR_CORE_HEX_SEQUENCE])
def test_all_raw_shift_paths_prove(code):
    blocks = _blocks(code)
    for summary in discover_shift_summaries(blocks, strict=True):
        lemma, status = prove_shift_slice_cached(summary, blocks)
        assert status == "proven" and lemma.complete and lemma.path_count >= 9
        assert prove_shift_slice_cached(summary, blocks)[1] == "cache_hits"


def test_wrong_shift_direction_cannot_be_certified_or_reused():
    blocks = _blocks(X86_SHR_CORE_HEX_SEQUENCE)
    [summary] = discover_shift_summaries(blocks, strict=True)
    wrong = replace(summary, payload=replace(summary.payload, direction="left"))
    with pytest.raises(ShiftProofError, match="effect_"):
        prove_shift_slice_cached(wrong, blocks)
    with pytest.raises(ShiftProofError) as exc:
        prove_shift_slice_cached(wrong, blocks)
    assert exc.value.from_cache


def test_truncated_raw_replay_cannot_be_certified():
    blocks = _blocks(X86_SHR_CORE_HEX_SEQUENCE)
    [summary] = discover_shift_summaries(blocks, strict=True)
    with pytest.raises(ShiftProofError, match="raw"):
        prove_shift_slice(summary, blocks, max_depth=1)


def test_pointer_metadata_must_instantiate_the_generic_lemma():
    runtime = build_x86_summary_runtime(_blocks(X86_SHR_CORE_HEX_SEQUENCE),
                                       summary_config=X86SummaryConfig.enabled(shift="strict"))
    [summary] = runtime.summaries
    state = SMTState()
    state.x86_registers.set_pointer_tag(Register.RAX, PointerTag.EVM_PTR)
    with pytest.raises(SummaryPreconditionError, match="pointer tag"):
        runtime.apply(summary, state)


def test_verified_runtime_consumes_shift_lemma_obligations():
    from verification.block_summaries import VerifiedSummaryRuntime
    runtime = VerifiedSummaryRuntime(_blocks(X86_SHR_CORE_HEX_SEQUENCE),
                                    X86SummaryConfig.enabled(shift="strict"), timeout_ms=30000)
    state = SMTState.create_initial_state(num_inputs=2)
    state.x86_registers.set_register(Register.R14, state.callengine_stack_base + state.callengine_stack_byte_offset)
    state.x86_registers.set_register(Register.R15, state.callengine_memory_base)
    runtime.apply(runtime.summaries[0], state)
    [certificate] = runtime.certificates
    names = {o.name for o in certificate.obligations}
    assert certificate.complete and certificate.raw_path_count >= 9
    assert {"entry", "div_stack_geometry", "coverage", "effect_0"} <= names
