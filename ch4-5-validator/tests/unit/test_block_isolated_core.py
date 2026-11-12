"""An expensive original core query is isolated before native add/check."""
import subprocess
import sys
from types import SimpleNamespace

import pytest
import z3 as z

import common.isolated_sat as isolated
import verification.block_equivalence as be


def expensive(goal_unsat=True):
    a, b = z.BitVecs("isolated_core_a isolated_core_b", 1024)
    return [a == 1, b == 2], a*b != 2 if goal_unsat else a*b == 2


@pytest.mark.parametrize("answer", ["sat", "unknown", "unsat"])
def test_exact_high_cost_input_uses_original_budget_before_any_native_solver(monkeypatch, answer):
    assertions, goal = expensive(answer == "unsat")
    calls, outcome = [], {}
    def child(formula, timeout_ms):
        calls.append((formula, timeout_ms))
        assert formula.eq(z.And(*assertions, goal))
        return answer
    monkeypatch.setattr(isolated, "isolated_sat", child)
    monkeypatch.setattr(be, "_solver", lambda *a, **kw: pytest.fail("native solver constructed for expensive core"))
    core = be._unsat_core(assertions, goal, 1234, outcome)
    assert core == ([0, 1] if answer == "unsat" else None)
    assert outcome == {"answer": answer} and len(calls) == 1 and calls[0][1] == 1234


def test_unsat_goal_with_no_assertions_has_valid_empty_core(monkeypatch):
    a, b = z.BitVecs("empty_core_a empty_core_b", 1024)
    monkeypatch.setattr(isolated, "isolated_sat", lambda *a: "unsat")
    assert be._unsat_core([], a*b != a*b, 1234) == []


def test_low_cost_keeps_original_tracked_core(monkeypatch):
    monkeypatch.setattr(isolated, "isolated_sat", lambda *a: pytest.fail("cheap tracked core isolated"))
    a = z.BitVec("native_core_a", 8)
    assertions, outcome = [a == 1, a == 2, a != 3], {}
    goal = z.BoolVal(True)
    indices = be._unsat_core(assertions, goal, 1000, outcome)
    assert indices is not None and outcome == {"answer": "unsat"}
    check = z.Solver(); check.add(*(assertions[i] for i in indices), goal)
    assert check.check() == z.unsat


@pytest.mark.parametrize("failure", ["timeout", "signal", "garbage"])
def test_child_failure_is_unknown_without_parent_retry(monkeypatch, failure):
    def run(command, **kw):
        if failure == "timeout": raise subprocess.TimeoutExpired(command, kw["timeout"])
        return SimpleNamespace(returncode=-6 if failure == "signal" else 0, stdout="unsat" if failure == "signal" else "garbage")
    monkeypatch.setattr(isolated.subprocess, "run", run)
    monkeypatch.setattr(be, "_solver", lambda *a, **kw: pytest.fail("unsafe parent retry"))
    assertions, goal = expensive(); outcome = {}
    assert be._unsat_core(assertions, goal, 1000, outcome) is None
    assert outcome == {"answer": "unknown"}


def test_existing_cache_accepts_full_valid_core_and_reuses_it(monkeypatch):
    assertions, goal = expensive(); saved = {}
    monkeypatch.setattr(be.proof_cache, "enabled", lambda: True)
    monkeypatch.setattr(be.proof_cache, "query_key", lambda *a: "exact-core-key")
    monkeypatch.setattr(be.proof_cache, "lookup", lambda key: saved.get(key))
    monkeypatch.setattr(be.proof_cache, "store", lambda key, value: saved.update({key: value}))
    monkeypatch.setattr(isolated, "isolated_sat", lambda *a: "unsat")
    assert be.unsat_core(assertions, goal, 1000) == [0, 1]
    monkeypatch.setattr(be, "_unsat_core", lambda *a: pytest.fail("decided cache not reused"))
    outcome = {}
    assert be.unsat_core(assertions, goal, 1, outcome) == [0, 1]
    assert outcome == {"answer": "unsat"}


def test_abort_propagates_before_cost_classification_or_child(monkeypatch):
    import common.node_monitor as monitor
    monkeypatch.setattr(monitor, "_ABORT", ["over budget"])
    monkeypatch.setattr(isolated, "expensive_bitblast", lambda *a: pytest.fail("abort was ignored"))
    assertions, goal = expensive()
    with pytest.raises(monitor.NodeMemoryExceeded): be._unsat_core(assertions, goal, 1000)


def test_public_abort_precedes_even_an_available_cached_core(monkeypatch):
    import common.node_monitor as monitor
    assertions, goal = expensive()
    lookups = []
    monkeypatch.setattr(monitor, "_ABORT", [None])
    monkeypatch.setattr(be.proof_cache, "enabled", lambda: True)
    monkeypatch.setattr(be.proof_cache, "query_key", lambda *a: "available-core")
    monkeypatch.setattr(be.proof_cache, "lookup", lambda key: lookups.append(key) or [0, 1])
    assert be.unsat_core(assertions, goal, 1000) == [0, 1]
    monitor._ABORT[0] = "over budget"
    with pytest.raises(monitor.NodeMemoryExceeded): be.unsat_core(assertions, goal, 1000)
    assert lookups == ["available-core"]


@pytest.mark.skipif(sys.platform != "linux", reason="hard AS child requires Linux /proc")
def test_actual_original_unsat_returns_the_full_valid_set_and_sat_never_does(monkeypatch):
    monkeypatch.setattr(be, "_solver", lambda *a, **kw: pytest.fail("high-cost query reached parent solver"))
    a, b = z.BitVecs("exact_child_core_a exact_child_core_b", 1024)
    assertions, outcome = [a == 1, b == 2], {}
    assert be._unsat_core(assertions, a*b != a*b, 5000, outcome) == [0, 1]
    assert outcome == {"answer": "unsat"}
    outcome = {}
    assert be._unsat_core(assertions, a*b == 2, 5000, outcome) is None
    assert outcome["answer"] in ("sat", "unknown")
