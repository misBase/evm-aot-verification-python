"""A costly expected-SAT check may fail in its child, never kill the proof worker."""
from types import SimpleNamespace
import subprocess
import sys

import pytest
from z3 import And, BitVecs, Bool, BoolVal, Function, URem

import common.isolated_sat as isolated
import verification.block_summaries as summaries


def _expensive():
    x, y, z = BitVecs("isolated_x isolated_y isolated_z", 512)
    return URem(x * y, z) == 1


def test_cost_counts_the_dag_once_and_only_builtin_bv_operations():
    x, y, z = BitVecs("cost_x cost_y cost_z", 512)
    product = x * y
    assert not isolated.expensive_bitblast(And(*(product == z + i for i in range(6))))
    assert isolated.expensive_bitblast(_expensive())
    a, b = Bool("fake_a"), Bool("fake_b")
    assert not isolated.expensive_bitblast(Function("bvmul", a.sort(), b.sort(), a.sort())(a, b))


@pytest.mark.parametrize("blast", [False, True])
@pytest.mark.skipif(sys.platform != "linux", reason="hard AS limit uses Linux /proc")
def test_child_solves_the_exact_query(blast):
    x, y = BitVecs("child_x child_y", 8)
    assert isolated.isolated_sat(And(x == 3, y == 5, x * y == 15), 5000, blast=blast) == "sat"
    assert isolated.isolated_sat(And(x == 3, y == 5, x * y != 15), 5000, blast=blast) == "unsat"


@pytest.mark.skipif(sys.platform != "linux", reason="hard AS limit uses Linux /proc")
def test_real_memory_limit_and_wall_timeout_leave_the_parent_usable(monkeypatch):
    import common.node_monitor as monitor
    from z3 import Solver, sat
    monkeypatch.setattr(monitor, "memory_headroom_mb", lambda: 2)
    assert isolated.isolated_sat(_expensive(), 5000) == "unknown"
    monkeypatch.setattr(monitor, "memory_headroom_mb", lambda: None)
    assert isolated.isolated_sat(_expensive(), 1) == "unknown"
    solver = Solver()
    solver.add(Bool("parent_alive"))
    assert solver.check() == sat


def test_timeout_or_abnormal_child_never_returns_a_conclusion(monkeypatch):
    def timeout(*args, **kwargs):
        raise subprocess.TimeoutExpired(args[0], kwargs["timeout"])
    monkeypatch.setattr(isolated.subprocess, "run", timeout)
    assert isolated.isolated_sat(BoolVal(True), 100) == "unknown"
    monkeypatch.setattr(isolated.subprocess, "run", lambda *a, **k: SimpleNamespace(returncode=-6, stdout="sat"))
    assert isolated.isolated_sat(BoolVal(True), 100) == "unknown"
    monkeypatch.setattr(isolated.subprocess, "run", lambda *a, **k: SimpleNamespace(returncode=0, stdout="nonsense"))
    assert isolated.isolated_sat(BoolVal(True), 100) == "unknown"


def test_node_abort_is_not_swallowed(monkeypatch):
    import common.node_monitor as monitor
    monkeypatch.setattr(monitor, "_ABORT", ["already over budget"])
    with pytest.raises(monitor.NodeMemoryExceeded):
        isolated.isolated_sat(BoolVal(True), 100)


def test_both_sat_routes_isolate_before_blasting_and_do_not_invent_a_model(monkeypatch):
    calls = []
    monkeypatch.setattr(isolated, "isolated_sat", lambda query, ms, **kw: calls.append((query, kw)) or "unknown")
    query = _expensive()
    assert summaries._sat_model(query, 10) == ("unknown", None)
    assert summaries.VerifiedSummaryRuntime._blasted_sat(query, 10) == ("unknown", None)
    assert len(calls) == 2 and calls[0][0].eq(query) and calls[1][0].eq(query)
    assert calls[1][1] == {"blast": True}


def test_undecided_entry_does_not_remove_the_effect_or_coverage_checks(monkeypatch):
    from tests.unit.test_block_summary_certificates import copy_case
    runtime, summary, state = copy_case(7)
    monkeypatch.setattr(summaries, "_sat_model", lambda *a, **k: ("unknown", None))
    runtime.apply(summary, state)
    certificate = runtime.certificates[-1]
    assert certificate.complete
    assert any(o.name == "entry" and o.answer == o.expected == "unknown" for o in certificate.obligations)
    assert any(o.name == "coverage" and o.answer == "unsat" for o in certificate.obligations)
    assert any(o.name.startswith("effect_") and o.answer == "unsat" for o in certificate.obligations)
