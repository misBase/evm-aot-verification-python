"""Mocked cache/control and raw-boundary wiring; these are NOT arithmetic proofs."""
import gc
from types import SimpleNamespace
import weakref

import pytest
from z3 import BoolVal, Solver

from state.smt_state import SMTState
from tests.integration.test_single_ins_equivalence import X86_SDIV_CORE_HEX_SEQUENCE
from verification import block_equivalence as be, loop_induction
from verification.block_equivalence import Obligation, ProofBudgetExceeded
from x86_64.aot_profile import AOT_COMPILER_PROFILE
from x86_64.cfg import identify_basic_blocks
from x86_64.disassembler import disassemble_hex
from x86_64.summaries import div_proof, memgas_proof, mul_proof, shift_proof, signed_proof
from x86_64.summaries.div_proof import DivLemma
from x86_64.summaries.registry import X86SummaryConfig
from x86_64.summaries.sdiv import discover_sdiv_summaries


@pytest.fixture(autouse=True)
def isolated_signed_cache(monkeypatch):
    monkeypatch.setattr(signed_proof, "_SUCCESS", {})
    monkeypatch.setattr(signed_proof, "_FAILURE", {})


def _control_lemma():
    records = tuple(Obligation(name, "false", "unsat") for name in ("coverage", "effect_0"))
    return DivLemma("mock-cache-control-only", 1, records, ())


def test_success_cache_reuses_the_proved_shape_across_budgets(monkeypatch):
    lemma, calls = _control_lemma(), []
    monkeypatch.setattr(signed_proof, "semantic_key", lambda *a: "same-shape")

    def prove(*args, **kwargs):
        calls.append(kwargs["timeout_ms"])
        assert kwargs["profile"] is AOT_COMPILER_PROFILE
        return lemma

    monkeypatch.setattr(signed_proof, "prove_signed_slice", prove)
    first, status = signed_proof.prove_signed_slice_cached(object(), [], profile=AOT_COMPILER_PROFILE,
                                                          timeout_ms=100)
    again, reused = signed_proof.prove_signed_slice_cached(object(), [], profile=AOT_COMPILER_PROFILE,
                                                           timeout_ms=200)
    assert first is again is lemma and lemma.complete
    assert (status, reused, calls) == ("proven", "cache_hits", [100])
    assert not signed_proof._FAILURE


def test_failure_cache_keeps_error_data_and_budget_but_not_execution_frames(monkeypatch):
    refs, calls = [], []
    monkeypatch.setattr(signed_proof, "semantic_key", lambda *a: "same-shape")

    def fail(*args, **kwargs):
        state, solver = SMTState(), Solver()
        refs.extend((weakref.ref(state), weakref.ref(solver)))
        calls.append(kwargs["timeout_ms"])
        raise signed_proof.SignedProofError(0x1234, "effect_2", "solver=unknown")

    monkeypatch.setattr(signed_proof, "prove_signed_slice", fail)
    for budget, cached in ((100, False), (100, True), (200, False)):
        try:
            signed_proof.prove_signed_slice_cached(object(), [], profile=AOT_COMPILER_PROFILE,
                                                    timeout_ms=budget)
        except signed_proof.SignedProofError as error:
            assert (error.entry_addr, error.label, error.reason, error.from_cache) == (
                0x1234, "effect_2", "solver=unknown", cached)
            assert all(error is not stored for stored in signed_proof._FAILURE.values())
        else:
            pytest.fail("an unproved slice was accepted")
        gc.collect()
        assert all(ref() is None for ref in refs), "a failed proof retained a real SMTState or Solver"
        assert all(stored.__traceback__ is stored.__context__ is stored.__cause__ is None
                   for stored in signed_proof._FAILURE.values())
    assert calls == [100, 200]
    assert set(signed_proof._FAILURE) == {("same-shape", 100), ("same-shape", 200)}
    assert not signed_proof._SUCCESS


def test_interrupted_budget_is_not_classified_or_cached_as_a_slice_failure(monkeypatch):
    calls = []
    monkeypatch.setattr(signed_proof, "semantic_key", lambda *a: "same-shape")

    def interrupted(*args, **kwargs):
        calls.append(kwargs["timeout_ms"])
        raise ProofBudgetExceeded("outer deadline")

    monkeypatch.setattr(signed_proof, "prove_signed_slice", interrupted)
    for _ in range(2):
        with pytest.raises(ProofBudgetExceeded, match="outer deadline"):
            signed_proof.prove_signed_slice_cached(object(), [], profile=AOT_COMPILER_PROFILE,
                                                    timeout_ms=100)
    assert calls == [100, 100]
    assert not signed_proof._SUCCESS and not signed_proof._FAILURE


def test_forget_failures_preserves_signed_success_and_retries_signed_failure(monkeypatch):
    from verification.block_parallel import forget_summary_failures

    for module, name in ((div_proof, "_FAILURE"), (memgas_proof, "_FAILURE"),
                         (mul_proof, "_PROOF_FAILURE_CACHE"), (shift_proof, "_FAILURE")):
        monkeypatch.setattr(module, name, {})
    lemma, calls = _control_lemma(), []
    signed_proof._SUCCESS["proved"] = lemma
    signed_proof._FAILURE["failed", 100] = signed_proof.SignedProofError(0, "coverage", "unknown")
    monkeypatch.setattr(signed_proof, "semantic_key", lambda summary, *a: summary)

    def prove(*args, **kwargs):
        calls.append(args[0])
        return lemma

    monkeypatch.setattr(signed_proof, "prove_signed_slice", prove)
    forget_summary_failures()
    assert signed_proof._SUCCESS == {"proved": lemma} and not signed_proof._FAILURE
    assert signed_proof.prove_signed_slice_cached("proved", [], profile=AOT_COMPILER_PROFILE)[1] == "cache_hits"
    assert signed_proof.prove_signed_slice_cached("failed", [], profile=AOT_COMPILER_PROFILE,
                                                  timeout_ms=100)[1] == "proven"
    assert calls == ["failed"]


def test_signed_proof_api_requires_an_explicit_profile():
    with pytest.raises(TypeError, match="profile"):
        signed_proof.prove_signed_slice_cached(object(), [])


@pytest.mark.parametrize("case", ("depth-defect", "empty", "wrong-join", "terminal"))
def test_mock_raw_boundary_rejects_incomplete_execution_before_any_solver(monkeypatch, case):
    blocks = identify_basic_blocks(disassemble_hex(X86_SDIV_CORE_HEX_SEQUENCE))
    [summary] = discover_sdiv_summaries(blocks, strict=True)
    join, calls = summary.payload.continuation_addr, []
    path = SimpleNamespace(kind="exit", location=join, condition=BoolVal(True), state=SMTState())
    paths, defects = [path], []
    if case == "depth-defect":
        defects = ["mock coverage incomplete: depth pruned"]
    elif case == "empty":
        paths = []
    elif case == "wrong-join":
        path.location = join + 1
    else:
        path.kind = "terminal"

    def raw(*args, **kwargs):
        calls.append((args, kwargs))
        return paths, defects, []

    def no_solver(*args, **kwargs):
        pytest.fail("an invalid raw boundary reached the solver")

    monkeypatch.setattr(loop_induction, "run_x86_segment", raw)
    monkeypatch.setattr(be, "solve_query", no_solver)
    with pytest.raises(signed_proof.SignedProofError) as error:
        signed_proof.prove_signed_slice(summary, blocks, profile=AOT_COMPILER_PROFILE,
                                        timeout_ms=1, max_depth=3)
    assert error.value.label == "raw" and len(calls) == 1
    args, kwargs = calls[0]
    assert args[2:] == (summary.entry_addr, {join})
    assert kwargs["max_depth"] == 3 and kwargs["use_reachability_check"]
    assert kwargs["summary_config"] == X86SummaryConfig.disabled()
    assert not signed_proof._SUCCESS and not signed_proof._FAILURE
