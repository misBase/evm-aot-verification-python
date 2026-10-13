"""Prefix-shared x86_maps discharge and sibling proposals (Safe 5377)."""
from time import monotonic
from types import SimpleNamespace

import pytest
from z3 import And, BitVec, BoolVal, Not, ULT, UGE, UGT

import verification.block_equivalence as be
from verification.block_equivalence import (BlockEquivalenceProver, BlockTheorem, Obligation, discharge_maps_by_prefix,
                                             pair_obligation_names, propose_from_siblings)

x, y = BitVec("x", 64), BitVec("y", 64)


def test_shared_prefix_discharges_group_with_one_query():
    # Both paths start with x < 10; the EVM conjunct x < 100 follows from that prefix alone.
    paths = {0: And(ULT(x, 10), y == 1), 1: And(ULT(x, 10), y == 2)}
    c = ULT(x, 100)
    done = discharge_maps_by_prefix(BoolVal(True), paths, [(c, [(0, 0), (1, 0)])], 2000)
    assert set(done) == {(0, 0), (1, 0)} and all(o.proved for o in done.values())
    assert done[(0, 0)].formula == done[(1, 0)].formula  # one shared refutation


def test_descends_past_weak_prefix_and_never_discharges_false_map():
    # Prefix (x < 10) is too weak for y == 1; path 0 implies it, path 1 does not.
    paths = {0: And(ULT(x, 10), y == 1), 1: And(ULT(x, 10), y == 2)}
    done = discharge_maps_by_prefix(BoolVal(True), paths, [(y == 1, [(0, 3), (1, 3)])], 2000)
    assert set(done) == {(0, 3)}
    assert "x86_maps_0_3" == done[(0, 3)].name


def test_single_path_counterexample_is_left_to_the_routes():
    paths = {0: And(UGT(x, 5), ULT(x, 10))}
    assert discharge_maps_by_prefix(BoolVal(True), paths, [(ULT(x, 7), [(0, 0)])], 2000) == {}


def test_sibling_proposal_only_replaces_all_on_unanimous_siblings():
    p = lambda kind, loc: SimpleNamespace(kind=kind, location=loc)
    x86 = [p("exit", 1), p("exit", 1), p("exit", 1), p("terminal", 2), p("terminal", 2), p("terminal", 2)]
    found = (0, "all", 0, 1, "all", 2)
    assert propose_from_siblings(found, x86) == [0, 0, 0, 1, "all", 2]


def test_unknown_groups_are_reported_and_proved_once_by_full_routes(monkeypatch):
    paths = {0: And(ULT(x, 10), y == 1), 1: And(ULT(x, 10), y == 2), 2: And(UGT(x, 5), y == 3)}
    stuck = []
    monkeypatch.setattr(be, "solve_query", lambda q, ms: "unknown")
    assert discharge_maps_by_prefix(BoolVal(True), paths, [(ULT(x, 100), [(0, 0), (1, 0)]),
                                                           (ULT(x, 7), [(2, 1)])], 2000, stuck=stuck) == {}
    assert sorted(len(entries) for _, entries in stuck) == [1, 2]
    monkeypatch.undo()
    done = {}
    BlockEquivalenceProver([], [], {}, timeout_ms=2000)._prove_stuck_groups(stuck, done, monotonic() + 60, 30)
    # The shared-prefix group is refuted once and proves both members; x > 5 does not imply x < 7.
    assert set(done) == {(0, 0), (1, 0)} and done[(1, 0)].name == "x86_maps_1_0"
    assert all(o.proved for o in done.values()) and done[(0, 0)].formula == done[(1, 0)].formula


# --- _pair_phase: keep sibling proposals, degrade only the failing row ----------------------

_BASE = ["entry_nonempty", "havoc_relation", "model_domain_nonempty", "evm_coverage", "x86_coverage",
         "evm_disjoint_0_1"]


def _node(row1, bad=()):
    """EVM 0: x < 10 ∧ x != 7 (two conjuncts), EVM 1: x >= 10. x86 rows 0 and 1 share
    (exit, A), so row 1 (found "all") is proposed EVM 0; row 2 is mapped to 1."""
    v = BitVec("pp_x", 8)
    p = lambda c, kind, loc: SimpleNamespace(condition=c, kind=kind, location=loc)
    evm = [p(And(ULT(v, 10), v != 7), "exit", 0), p(UGE(v, 10), "terminal", None)]
    x86 = [p(ULT(v, 3), "exit", "A"), p(row1(v), "exit", "A"), p(UGE(v, 10), "terminal", None)]

    def pair(i, j):  # goal False for the `bad` pairs: they fail exactly when their joint is satisfiable
        goal = BoolVal((i, j) not in bad)
        return f"pair_{i}_{j}", And(evm[i].condition, x86[j].condition, Not(goal)), f"{i}/{j}"
    return evm, x86, pair


def _run(evm, x86, pair, found=(0, "all", 1)):
    prover = BlockEquivalenceProver([], [], {}, timeout_ms=3000)
    records = [Obligation(name, "f", "unsat") for name in _BASE]
    corr = prover._pair_phase(evm, x86, BoolVal(True), pair, found, records)
    required = tuple(_BASE[:5]) + tuple(pair_obligation_names(len(evm), len(x86), corr, be.map_arity(evm, corr)))
    theorem = BlockTheorem("id", None, tuple(records), required, "d", len(evm), len(x86), True,
                           correspondence=corr, arity=be.map_arity(evm, corr))
    return corr, records, theorem


def test_proposal_kept_when_its_leftover_maps_prove_in_the_pair_phase(monkeypatch):
    real, checked = be.discharge_maps_by_prefix, []
    # The prefix pass leaves proposed row 1's map 1 (x != 7) undischarged: it used to revert the row.
    monkeypatch.setattr(be, "discharge_maps_by_prefix",
                        lambda *a, **k: {key: r for key, r in real(*a, **k).items() if key != (1, 1)})
    evm, x86, pair = _node(lambda v: And(UGE(v, 3), ULT(v, 7)))
    real_check = BlockEquivalenceProver._check
    monkeypatch.setattr(BlockEquivalenceProver, "_check",
                        lambda self, name, *a, **k: checked.append(name) or real_check(self, name, *a, **k))
    corr, records, theorem = _run(evm, x86, pair)
    assert corr == (0, 0, 1)
    assert "x86_maps_1_1" in checked and "x86_maps_1_0" not in checked  # only the leftover map is checked
    assert theorem.complete


def test_failing_proposal_degrades_only_its_row_and_the_node_still_proves():
    # Siblings say EVM 0, but row 1 lies in EVM 1: its map x < 10 is SAT-refuted.
    evm, x86, pair = _node(lambda v: And(UGE(v, 10), ULT(v, 20)))
    corr, records, theorem = _run(evm, x86, pair)
    assert corr == (0, "all", 1)
    names = [r.name for r in records]
    assert not any(n.startswith("x86_maps_1_") for n in names)  # the discarded mapping leaves no records
    assert {"pair_0_1", "pair_1_1"} <= set(names) and theorem.complete


def test_genuinely_failing_pair_still_fails_the_node():
    # Degraded row 1 really mismatches EVM 1: the second round fails the node.
    evm, x86, pair = _node(lambda v: And(UGE(v, 10), ULT(v, 20)), bad={(1, 1)})
    with pytest.raises(ValueError, match="pair_1_1"):
        _run(evm, x86, pair)
    # A failure outside a proposed row fails at once, as before.
    evm, x86, pair = _node(lambda v: And(UGE(v, 3), ULT(v, 7)), bad={(1, 2)})
    with pytest.raises(ValueError, match="pair_1_2"):
        _run(evm, x86, pair)
