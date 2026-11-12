"""Shared H2 records retain their proof and bypass repeated screens and rewrites."""
from z3 import And, BitVec

import verification.block_equivalence as be
from verification.block_parallel import close_edge, shared_bases
from verification.cutpoint_relation import RelationGoal


def test_proved_shared_target_is_reused_before_any_solver_or_rewrite(monkeypatch):
    x, branch = BitVec("h2_reuse_x", 64), BitVec("h2_reuse_branch", 64)
    bases = [And(x == 7, branch == 0), And(x == 7, branch != 0)]
    targets = [("target", (RelationGoal("stack_constant_predicate", x == 7),))]
    shared = dict(bases=shared_bases(bases, [targets, targets]), done={})
    prover = be.BlockEquivalenceProver([], [], {}, timeout_ms=1000)
    first = close_edge(prover, "H2_first", bases[0], targets, shared)
    assert first.proved and shared["done"]
    assert all(record.formula.startswith("sha256:") for records in shared["done"].values()
               for record in records)

    def unexpected(*args, **kwargs):
        raise AssertionError("a proved shared target must not run another query or rewrite")

    monkeypatch.setattr(be, "solve_query", unexpected)
    monkeypatch.setattr(be, "refute_over_bv_abstraction", unexpected)
    second = close_edge(prover, "H2_second", bases[1], targets, shared)
    assert second.proved and second.lemmas and second.name == "H2_second"
    assert second.lemmas == tuple(r for records in shared["done"].values() for r in records)


def test_a_true_edge_does_not_cache_a_false_claim_for_its_sibling():
    x, branch = BitVec("h2_false_x", 64), BitVec("h2_false_branch", 64)
    bases = [And(x == 7, branch == 0), And(x == 8, branch != 0)]
    targets = [("target", (RelationGoal("gas", x == 7),))]
    shared = dict(bases=shared_bases(bases, [targets, targets]), done={})
    prover = be.BlockEquivalenceProver([], [], {}, timeout_ms=1000)
    assert close_edge(prover, "H2_true", bases[0], targets, shared).proved
    assert not close_edge(prover, "H2_false", bases[1], targets, shared).proved


def test_failed_shared_lemma_cannot_make_a_cached_target_proved():
    from verification.block_equivalence import Obligation

    x = BitVec("h2_failed_shared", 64)
    goal = x == 7
    targets = [("target", (RelationGoal("gas", goal),))]
    shared = dict(bases={goal.get_id(): And()}, done={goal.get_id(): [Obligation("bad", "false", "sat")]})
    record = close_edge(be.BlockEquivalenceProver([], [], {}, timeout_ms=1000), "H2_bad", And(), targets, shared)
    assert not record.proved


def test_node_memory_stop_drops_shift_slice_failures(monkeypatch):
    from verification.block_parallel import forget_summary_failures
    from x86_64.summaries import shift_proof

    failures = {("interrupted-slice",): "memory limit"}
    monkeypatch.setattr(shift_proof, "_FAILURE", failures)
    forget_summary_failures()
    assert failures == {}
