"""A cached proof failure retains error data, never failed solvers or execution frames."""
import gc
import weakref

import pytest
from z3 import Solver

from state.smt_state import SMTState
from x86_64.summaries import div_proof, memgas_proof, mul_proof, shift_proof


@pytest.mark.parametrize("module,uncached,cached,error", [
    (div_proof, "prove_div_slice", "prove_div_slice_cached", div_proof.DivProofError),
    (memgas_proof, "prove_memgas_slice", "prove_memgas_slice_cached", memgas_proof.MemGasProofError),
    (mul_proof, "prove_mul_slice_refines_summary", "prove_mul_slice_cached", mul_proof.MulProofError),
    (shift_proof, "prove_shift_slice", "prove_shift_slice_cached", shift_proof.ShiftProofError),
])
def test_failure_keeps_fields_and_budget_key_but_drops_the_traceback(monkeypatch, module, uncached, cached, error):
    mul = module is mul_proof
    key_name = "_semantic_cache_key" if mul else "semantic_key"
    failure_name = "_PROOF_FAILURE_CACHE" if mul else "_FAILURE"
    success_name = "_PROOF_SUCCESS_CACHE" if mul else "_SUCCESS"
    failures, refs, calls = {}, [], []
    monkeypatch.setattr(module, key_name, lambda *a, **kw: ("same-shape",))
    monkeypatch.setattr(module, failure_name, failures)
    monkeypatch.setattr(module, success_name, set() if mul else {})

    def fail(*a, **kw):
        state, solver = SMTState.create_initial_state(num_inputs=0), Solver()
        refs.extend((weakref.ref(state), weakref.ref(solver)))
        calls.append(kw["timeout_ms"])
        raise error(0x1234, "effect_2", "query undecided", *(('unknown',) if mul else ()))

    monkeypatch.setattr(module, uncached, fail)
    prove = getattr(module, cached)
    for budget, from_cache in ((100, False), (100, True), (200, False)):
        try:
            prove(object(), [], timeout_ms=budget)
        except error as exc:
            assert (exc.entry_addr, exc.label, exc.reason, exc.from_cache) == (
                0x1234, "effect_2", "query undecided", from_cache)
            if mul:
                assert exc.solver_result == "unknown"
            assert all(exc is not stored for stored in failures.values())
        else:
            pytest.fail("an unproved slice was accepted")
        gc.collect()
        assert all(ref() is None for ref in refs), "failure cache kept a real SMTState or Solver alive"
        assert all(stored.__traceback__ is stored.__context__ is stored.__cause__ is None
                   for stored in failures.values())
    assert calls == [100, 200], "a new budget must retry; the same failed budget must reuse its classification"
    assert len(failures) == 2
