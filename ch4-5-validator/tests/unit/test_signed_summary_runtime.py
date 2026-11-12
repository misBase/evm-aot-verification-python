"""Signed summary wiring checks; mocked slice lemmas are NOT arithmetic proofs."""
from dataclasses import replace

import pytest
from z3 import BitVec, BitVecVal

from state.smt_state import MemoryDomain
from tests.integration.test_single_ins_equivalence import (
    X86_SDIV_CORE_HEX_SEQUENCE, X86_SMOD_CORE_HEX_SEQUENCE,
)
from verification.block_equivalence import Obligation
from verification.block_summaries import VerifiedSummaryRuntime
from verification.loop_induction import run_x86_segment
from x86_64.cfg import identify_basic_blocks
from x86_64.disassembler import disassemble_hex
from x86_64.models import Register
from x86_64.summaries.base import (
    SummaryContinuation, SummaryMatchError, SummaryPreconditionError, X86SummaryManager,
)
from x86_64.summaries.div_proof import DivLemma, generic_div_state
from x86_64.summaries.registry import X86SummaryConfig, build_x86_summary_runtime
from x86_64.summaries.signed_proof import SignedProofError


CODES = {
    "sdiv": X86_SDIV_CORE_HEX_SEQUENCE,
    "smod": "49c7850001000000000000" + X86_SMOD_CORE_HEX_SEQUENCE,
}


def _blocks(kind="sdiv"):
    return identify_basic_blocks(disassemble_hex(CODES[kind]))


def _runtime(kind, *, verified=False, mode="fallback", nested=False):
    config = X86SummaryConfig.enabled(**({"div": "fallback", kind: mode} if nested else {kind: mode}))
    blocks = _blocks(kind)
    runtime = (VerifiedSummaryRuntime(blocks, config, timeout_ms=500)
               if verified else build_x86_summary_runtime(blocks, summary_config=config))
    return runtime, next(s for s in runtime.summaries if s.kind == kind)


def _routing_lemma():
    # Only the composition/manifest plumbing is under test here.
    records = tuple(Obligation(n, "false", "unsat") for n in (
        "coverage", "assumption_0_0", "effect_0", "effect_1"))
    return DivLemma("mock-for-runtime-routing-only", 2, records, ())


def _install_lemma(monkeypatch, runtime, kind):
    spec = runtime.manager.specs[kind]
    calls = []

    def lemma(summary):
        calls.append(summary.entry_addr)
        return _routing_lemma()

    monkeypatch.setattr(spec, "lemma", lemma)
    return calls


@pytest.mark.parametrize("order", [("sdiv", "div"), ("div", "sdiv")])
def test_only_explicitly_listed_inner_divs_may_overlap_sdiv(order):
    runtime = build_x86_summary_runtime(_blocks(), summary_config=X86SummaryConfig.enabled(
        **dict.fromkeys(order, "fallback")))
    outer = next(s for s in runtime.summaries if s.kind == "sdiv")
    inners = runtime.summaries_for_kind("div")
    assert len(inners) == 4
    assert {s.payload for s in inners} == set(outer.payload.divs)
    assert all(runtime.get(*s.start_key) is s for s in (outer, *inners))

    unlisted = replace(inners[0], payload=replace(inners[0].payload,
                                                builtin_stack_pointer=100))
    summaries = (outer, unlisted) if order[0] == "sdiv" else (unlisted, outer)
    with pytest.raises(SummaryMatchError, match="coverage overlap"):
        X86SummaryManager(runtime.blocks, tuple(runtime.manager.specs.values()), summaries)


@pytest.mark.parametrize("kind", ["sdiv", "div"])
@pytest.mark.parametrize("field", ["entry_addr", "start_block_addr", "start_instruction_index",
    "continuation", "covered_block_addrs", "clobber_registers", "clobber_flags"])
def test_nested_div_overlap_rejects_a_forged_wrapper(kind, field):
    runtime, outer = _runtime("sdiv", nested=True)
    inner = runtime.summaries_for_kind("div")[0]
    original = outer if kind == "sdiv" else inner
    if field == "start_block_addr":
        unrelated = next(b.start_addr for b in runtime.blocks
            if b.start_addr in outer.covered_block_addrs
            and b.start_addr != outer.start_block_addr and b.start_addr not in inner.covered_block_addrs)
        forged = replace(original, start_block_addr=unrelated, start_instruction_index=0,
                         covered_block_addrs=tuple(sorted({unrelated, *original.covered_block_addrs})))
    else:
        replacements = {
            "entry_addr": original.entry_addr + 1,
            "start_instruction_index": original.start_instruction_index + 1,
            "continuation": SummaryContinuation(original.continuation.block_addr, 1),
            "covered_block_addrs": (*original.covered_block_addrs, original.continuation.block_addr),
            "clobber_registers": original.clobber_registers[:-1],
            "clobber_flags": original.clobber_flags[:-1],
        }
        forged = replace(original, **{field: replacements[field]})
    summaries = (forged, inner) if kind == "sdiv" else (outer, forged)
    with pytest.raises(SummaryMatchError, match="overlap"):
        X86SummaryManager(runtime.blocks, tuple(runtime.manager.specs.values()), summaries)


def test_nested_div_overlap_rejects_an_untyped_payload_with_forged_equality():
    runtime, outer = _runtime("sdiv", nested=True)
    inner = runtime.summaries_for_kind("div")[0]

    class EqualToAnything:
        def __eq__(self, other):
            return True

    with pytest.raises(SummaryMatchError, match="coverage overlap"):
        X86SummaryManager(runtime.blocks, tuple(runtime.manager.specs.values()),
                         (outer, replace(inner, payload=EqualToAnything())))


@pytest.mark.parametrize("kind", CODES)
def test_signed_summaries_are_explicit_opt_in(kind):
    blocks = _blocks(kind)
    assert not build_x86_summary_runtime(blocks).summaries
    assert not build_x86_summary_runtime(blocks, summary_config=X86SummaryConfig.disabled()).summaries
    runtime, summary = _runtime(kind)
    assert runtime.get(*summary.start_key) is summary


@pytest.mark.parametrize("kind", CODES)
def test_legacy_div_proof_switch_cannot_bypass_a_signed_lemma(monkeypatch, kind):
    runtime = build_x86_summary_runtime(_blocks(kind), summary_config=X86SummaryConfig.enabled(
        prove_div_hits=False, **{kind: "fallback"}))
    [summary] = runtime.summaries

    def unknown(summary):
        raise SignedProofError(summary.entry_addr, "coverage", "solver=unknown")

    monkeypatch.setattr(runtime.manager.specs[kind], "lemma", unknown)
    with pytest.raises(SummaryPreconditionError, match="solver=unknown"):
        runtime.apply(summary, generic_div_state(summary.payload))
    assert runtime.hit_count(kind) == 0


@pytest.mark.parametrize("kind", CODES)
@pytest.mark.parametrize("verified", [False, True])
def test_unproved_signed_lemma_is_a_rejectable_precondition(monkeypatch, kind, verified):
    runtime, summary = _runtime(kind, verified=verified)
    before = generic_div_state(summary.payload)
    old_memory = before.x86_memory.stack_mem

    def unknown(summary):
        raise SignedProofError(summary.entry_addr, "effect_0", "solver=unknown")

    monkeypatch.setattr(runtime.manager.specs[kind], "lemma", unknown)
    with pytest.raises(SummaryPreconditionError, match="solver=unknown"):
        runtime.apply(summary, before)
    assert runtime.should_fallback_on_precondition(kind)
    assert runtime.hit_count(kind) == 0
    assert not runtime.assumed_premises
    assert before.x86_memory.stack_mem.eq(old_memory)
    if verified:
        assert not runtime.certificates


@pytest.mark.parametrize("kind", CODES)
def test_verified_signed_runtime_keeps_all_slice_obligations(monkeypatch, kind):
    runtime, summary = _runtime(kind, verified=True)
    calls = _install_lemma(monkeypatch, runtime, kind)
    before = generic_div_state(summary.payload)
    runtime.apply(summary, before)
    [certificate] = runtime.certificates
    names = tuple(o.name for o in certificate.obligations)
    assert len(calls) == 2  # composition gate and the spec's own application gate
    assert certificate.complete and certificate.raw_path_count == 2
    assert names == certificate.required
    assert {"entry", "div_stack_geometry", "coverage", "effect_0", "effect_1",
            "assumption_0_0"} <= set(names)
    assert not replace(certificate, required=names[:-1]).complete
    assert not replace(certificate, obligations=certificate.obligations[:-1]).complete
    assert runtime.hit_count(kind) == 1 and not runtime.assumed_premises

    before.x86_registers.set_register(Register.R14, BitVec("signed_unrelated_r14", 64))
    with pytest.raises(SummaryPreconditionError, match="div_stack_geometry"):
        runtime.apply(summary, before)
    assert len(runtime.certificates) == 1
    assert not before.assumptions


def test_rejected_outer_sdiv_replays_raw_then_uses_the_indexed_inner_div(monkeypatch):
    runtime, outer = _runtime("sdiv", verified=True, nested=True)

    def unknown(summary):
        raise SignedProofError(summary.entry_addr, "coverage", "solver=unknown")

    monkeypatch.setattr(runtime.manager.specs["sdiv"], "lemma", unknown)
    _install_lemma(monkeypatch, runtime, "div")
    state = generic_div_state(outer.payload)
    r14 = state.x86_registers.get_register(Register.R14)
    for offsets, value in ((outer.payload.dividend_offsets, 17),
                           (outer.payload.divisor_offsets, 5)):
        state.x86_memory = state.x86_memory.store_256bit(
            r14 + BitVecVal(offsets[0], 64), BitVecVal(value, 256), domain=MemoryDomain.STACK)
    paths, defects, _ = run_x86_segment(runtime.blocks, state, outer.entry_addr,
        {outer.payload.continuation_addr}, max_depth=400, use_reachability_check=True,
        summary_runtime=runtime)
    assert paths and not defects
    assert all(path.location == outer.payload.continuation_addr for path in paths)
    assert runtime.hit_count("sdiv") == 0 and runtime.hit_count("div") == 1
    assert len(runtime.precondition_failures) == 1
    assert runtime.precondition_failures[0].kind == "sdiv"
    assert all(c.complete for c in runtime.certificates)
    assert not runtime.assumed_premises
