"""High-cost proof queries use the same formula/tactic with OS isolation, never cache resource unknowns."""
import sys

import pytest
from z3 import And, BitVecs, Bool, BoolVal, Not, URem

import common.isolated_sat as isolated
import verification.block_equivalence as be


def expensive():
    a, b, c = BitVecs("proof_isolation_a proof_isolation_b proof_isolation_c", 512)
    return URem(a*b, c) == 1


@pytest.mark.parametrize("api", ["solve_query", "solve_pure_bv"])
@pytest.mark.parametrize("answer", ["sat", "unsat", "unknown"])
def test_expensive_queries_keep_formula_tactic_and_only_cache_decisions(monkeypatch, api, answer):
    calls, stored = [], []
    monkeypatch.setattr(be.proof_cache, "enabled", lambda: True)
    monkeypatch.setattr(be.proof_cache, "query_key", lambda *a: "isolated-key")
    monkeypatch.setattr(be.proof_cache, "cached_answer", lambda *a: None)
    monkeypatch.setattr(be.proof_cache, "record_answer", lambda *a: stored.append(a))
    def solve(formula, timeout_ms, **kw):
        calls.append((formula, timeout_ms, kw))
        return answer
    monkeypatch.setattr(isolated, "isolated_sat", solve)
    monkeypatch.setattr(be, "_solver", lambda *a, **k: pytest.fail("expensive query reached native parent solver"))
    monkeypatch.setattr(be, "Then", lambda *a: pytest.fail("expensive query reached parent tactic"))
    query = expensive()
    assert getattr(be, api)(query, 1234) == answer
    assert len(calls) == 1 and calls[0][0].eq(query) and calls[0][1] == 1234
    assert calls[0][2] == ({"pure_bv": True} if api == "solve_pure_bv" else {})
    assert stored == ([] if answer == "unknown" else [("isolated-key", answer, 1234)])


@pytest.mark.parametrize("api", ["solve_query", "solve_pure_bv"])
@pytest.mark.parametrize("expected", ["sat", "unsat"])
def test_low_cost_queries_keep_the_original_parent_route(monkeypatch, api, expected):
    monkeypatch.setattr(be.proof_cache, "enabled", lambda: False)
    monkeypatch.setattr(isolated, "isolated_sat", lambda *a, **k: pytest.fail("low-cost query isolated"))
    x = Bool("low_cost_proof")
    query = x if expected == "sat" else And(x, Not(x))
    assert getattr(be, api)(query, 3000) == expected


@pytest.mark.skipif(sys.platform != "linux", reason="hard AS limit uses Linux /proc")
@pytest.mark.parametrize("expected", ["sat", "unsat"])
def test_actual_pure_bv_child_keeps_sat_and_unsat(expected):
    x = Bool("pure_child_answer")
    query = x if expected == "sat" else And(x, Not(x))
    assert isolated.isolated_sat(query, 5000, pure_bv=True) == expected


@pytest.mark.skipif(sys.platform != "linux", reason="hard AS limit uses Linux /proc")
def test_actual_pure_bv_budget_failure_is_unknown_and_parent_survives(monkeypatch):
    import common.node_monitor as monitor
    monkeypatch.setattr(monitor, "memory_headroom_mb", lambda: 2)
    assert isolated.isolated_sat(expensive(), 5000, pure_bv=True) == "unknown"
    monkeypatch.setattr(monitor, "memory_headroom_mb", lambda: None)
    assert be.solve_query(BoolVal(True), 3000) == "sat"
