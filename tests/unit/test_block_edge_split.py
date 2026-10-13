"""H0/H2 edge closure one target at a time, conjunct by conjunct (block_parallel.close_edge)."""
from z3 import And, BitVec, BoolVal, ULT

import verification.block_equivalence as be
from verification.block_parallel import close_edge
from verification.cutpoint_relation import RelationGoal

x, y = BitVec("edge_x", 64), BitVec("edge_y", 64)


def prover():
    return be.BlockEquivalenceProver([], [], {}, timeout_ms=3000)


def test_closes_through_the_one_target_that_holds_with_a_proof_per_conjunct():
    base = And(x == 5, ULT(y, 10))
    wrong = [RelationGoal("stack_geometry", x == 6), RelationGoal("memory", BoolVal(True))]
    right = [RelationGoal("stack_geometry", x == 5), RelationGoal("memory", And(ULT(y, 11), y * x == x * y))]
    record = close_edge(prover(), "H2_0_0", base, [("t0", wrong), ("t1", right)])
    assert record.proved and "t1" in record.formula
    assert len(record.lemmas) == 3 and all(part.proved for part in record.lemmas)  # x==5, y<11, y*x==x*y


def test_an_edge_no_target_closes_is_not_proved():
    base = And(x == 5, ULT(y, 10))
    goals = [("t0", [RelationGoal("stack_geometry", x == 6)]),
             ("t1", [RelationGoal("stack_geometry", x == 5), RelationGoal("memory", ULT(y, 9))])]
    record = close_edge(prover(), "H2_0_1", base, goals)
    assert not record.proved  # y = 9 satisfies the base and breaks t1's memory goal


def test_a_wrong_target_is_skipped_when_only_its_refutation_is_cheap(monkeypatch):
    # CErc20 14263 H2: showing base ∧ ¬g sat needs a model of the whole premise
    # (unknown), while base ∧ g is refuted at once; the wrong target must not
    # reach the full per-conjunct routes.
    base = And(x == 5, ULT(y, 10))
    goals = [("t0", [RelationGoal("stack_geometry", x == 6), RelationGoal("memory", ULT(y, 9))]),
             ("t1", [RelationGoal("stack_geometry", x == 5), RelationGoal("memory", ULT(y, 11))])]
    real = be.solve_query
    monkeypatch.setattr(be, "solve_query", lambda q, ms: "unknown" if "Not" in str(q) else real(q, ms))
    p, checked = prover(), []
    check = p._check
    monkeypatch.setattr(p, "_check", lambda name, *a, **k: checked.append(name) or check(name, *a, **k))
    record = close_edge(p, "H2_0_2", base, goals)
    assert record.proved and "t1" in record.formula
    assert not any("_t0_" in name for name in checked), checked
