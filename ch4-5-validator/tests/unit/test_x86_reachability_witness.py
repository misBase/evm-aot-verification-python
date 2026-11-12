"""Reachability witness reuse: a model inherited from the parent path skips the
solver only for a branch it satisfies; pruning still needs an explicit UNSAT."""
from copy import copy

from z3 import And, BitVec, UGT, ULT

import x86_64.cfg_state as cfg_state
from x86_64.cfg_state import X86Constraints


def test_witness_skips_solver_only_for_satisfied_branch(monkeypatch):
    x = BitVec("x", 64)
    parent = X86Constraints()
    parent.add(UGT(x, 5))
    assert parent.is_possible()
    value = parent._witness.eval(x, model_completion=True)

    taken, other, dead = copy(parent), copy(parent), copy(parent)
    taken.add(x == value)
    other.add(x != value)
    dead.add(ULT(x, 3))

    real = cfg_state.SolverFor
    calls = []
    monkeypatch.setattr(cfg_state, "SolverFor", lambda logic: calls.append(logic) or real(logic))
    assert taken.is_possible() and calls == []
    assert other.is_possible() and len(calls) == 1
    assert not dead.is_possible() and len(calls) == 2
    assert dead._witness is None


def test_nonlinear_mul_refuted_by_abstraction_and_sat_kept():
    x, y = BitVec("x", 64), BitVec("y", 64)
    contradictory = X86Constraints()
    contradictory.add(x * y == 5)
    contradictory.add(x * y == 6)  # UNSAT already with bvmul as a UF
    assert not contradictory.is_possible()
    # Abstraction is SAT here (f(0, y) == 5); exact semantics must still decide.
    exact_only = X86Constraints()
    exact_only.add(x * y == 5)
    exact_only.add(x == 0)
    assert not exact_only.is_possible()
    feasible = X86Constraints()
    feasible.add(x * y == 6)
    assert feasible.is_possible() and feasible._witness is not None


def test_rlimit_budget_unknown_keeps_path(monkeypatch):
    # UNSAT (7 * 1000003 has no factor in (7, 1000) below 1000) but needs search.
    x, y = BitVec("x", 64), BitVec("y", 64)
    hard = X86Constraints()
    hard.add(x * y == 7 * 1000003)
    hard.add(And(UGT(x, 7), ULT(x, 1000), ULT(y, 1000)))
    assert not copy(hard).is_possible()  # default budget refutes it
    # Starved deterministic budget -> unknown -> kept, however slow the wall clock.
    monkeypatch.setattr(cfg_state, "REACHABILITY_RLIMIT_PER_MS", 1)
    monkeypatch.setattr(cfg_state, "REACHABILITY_WALL_SAFETY_FACTOR", 10**6)
    assert copy(hard).is_possible(solver_timeout=10)
