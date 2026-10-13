"""Speedups that must not change any answer: incremental reachability (P1),
witness-answered summary entry (P2), evm_disjoint by divergence (P3), mapping
proposals from executor witnesses + one incremental solver (P4), coverage via
bvmul->UF first (P5), complementary-conjunct refutation (P6)."""
import random
from copy import copy

import pytest
from z3 import And, BitVec, BoolVal, Not, Or, Solver, SolverFor, ULT, ULE, UGT, sat, unknown, unsat

from state.smt_state import SMTState
from verification.block_equivalence import (BlockEquivalenceProver, Obligation, disjoint_groups, pair_obligation_names,
                                            solve_query)
from verification.loop_induction import SegmentPath
from x86_64.cfg_state import PrefixSolver, X86Constraints
from x86_64.summaries.base import refuted_by_complement

x, y = BitVec("x", 8), BitVec("y", 8)


# P1 ---------------------------------------------------------------------------

def test_prefix_solver_matches_fresh_solver_across_pops():
    a, b, c, d = ULT(x, 10), UGT(x, 3), x == 5, x == 7
    queries = [[a], [a, b], [a, b, c], [a, b, d],      # sibling: pop one scope
               [a, b, c, d], [a, Not(b)], [a],         # pop back to a shorter prefix
               [UGT(x, 20), a], [a, b, c]]             # nothing shared, then re-push
    prefix = PrefixSolver()
    for conjuncts in queries:
        fresh = Solver()
        fresh.add(*conjuncts)
        assert prefix.check(conjuncts, 1000) == fresh.check()
        assert [t.get_id() for t in prefix.stack] == [t.get_id() for t in conjuncts]
        assert len(prefix.solver.assertions()) == len(conjuncts)


def test_is_possible_with_prefix_solver_agrees_and_keeps_witness():
    prefix = PrefixSolver()
    parent = X86Constraints()
    parent.add(ULT(x, 10))
    assert parent.is_possible(prefix_solver=prefix) and parent._witness is not None
    dead, live = copy(parent), copy(parent)
    dead.add(UGT(x, 20))
    live.add(UGT(x, 8))
    assert not dead.is_possible(prefix_solver=prefix) and dead._witness is None
    assert live.is_possible(prefix_solver=prefix)
    assert live._witness.eval(x).as_long() == 9
    # bvmul: the exact query decides (no probe needed) with or without prefix.
    contradictory = X86Constraints()
    contradictory.add(x * y == 5)
    contradictory.add(x * y == 6)
    assert not contradictory.is_possible(prefix_solver=prefix)


def test_prefix_unknown_keeps_path_unless_probe_refutes(monkeypatch):
    import x86_64.cfg_state as cfg_state
    w, z = BitVec("w", 64), BitVec("z", 64)
    hard = X86Constraints()
    hard.add(w * z == 7 * 1000003)
    hard.add(And(UGT(w, 7), ULT(w, 1000), ULT(z, 1000)))
    monkeypatch.setattr(cfg_state, "REACHABILITY_RLIMIT_PER_MS", 1)
    monkeypatch.setattr(cfg_state, "REACHABILITY_WALL_SAFETY_FACTOR", 10**6)
    assert copy(hard).is_possible(solver_timeout=10, prefix_solver=PrefixSolver())  # unknown -> kept


def test_prefix_unknown_pruned_only_by_probe_unsat(monkeypatch):
    # The exact answer is forced to unknown; only the bvmul->UF probe decides.
    monkeypatch.setattr(PrefixSolver, "check", lambda self, conjuncts, *a: unknown)
    refuted = X86Constraints()          # x*y == 5 ∧ x*y == 6: UNSAT with x*y a UF
    refuted.add(x * y == 5)
    refuted.add(x * y == 6)
    assert not refuted.is_possible(prefix_solver=PrefixSolver()) and refuted._witness is None
    abstract_sat = X86Constraints()     # x*x == 6 has no 8-bit root, but UF(x, x) == 6 is SAT
    abstract_sat.add(x * x == 6)
    assert abstract_sat.is_possible(prefix_solver=PrefixSolver())
    no_mul = X86Constraints()           # no bvmul: no probe, unknown keeps the path
    no_mul.add(And(UGT(x, 3), ULT(x, 3)))
    assert no_mul.is_possible(prefix_solver=PrefixSolver())


def test_prefix_solver_matches_fresh_solver_on_random_dfs():
    # Executor-like order: random walks over one branch tree, so queries pop
    # to every depth of the previous one, including back to the empty prefix.
    rng = random.Random(5377)
    atoms = [ULT(x, 40), UGT(y, 3), x + y == 50, ULE(x, y), x == 2 * y, UGT(x ^ y, 9), y != 7]
    edges = atoms + [Not(a) for a in atoms]
    prefix, depths = PrefixSolver(), set()
    for _ in range(150):
        conjuncts = [rng.choice(edges) for _ in range(rng.randint(0, 6))]
        if prefix.stack and rng.random() < 0.7:  # extend or branch off the previous path
            conjuncts = prefix.stack[:rng.randint(0, len(prefix.stack))] + conjuncts
        common = next((n for n, (a, b) in enumerate(zip(prefix.stack, conjuncts)) if not a.eq(b)),
                      min(len(prefix.stack), len(conjuncts)))
        depths.add(common)
        fresh = Solver()
        fresh.add(*conjuncts)
        assert prefix.check(conjuncts, 1000) == fresh.check()
        assert prefix.solver.num_scopes() == len(conjuncts) == len(prefix.solver.assertions())
    assert {0, 1, 2, 3} <= depths


def test_prefix_solver_recovers_from_failure_mid_sync(monkeypatch):
    prefix = PrefixSolver()
    assert prefix.check([ULT(x, 10), UGT(x, 3)], 1000) == sat
    real_add, calls = prefix.solver.add, []

    def flaky_add(*args):
        calls.append(args)
        if len(calls) == 2:
            raise KeyboardInterrupt
        real_add(*args)
    monkeypatch.setattr(prefix.solver, "add", flaky_add)
    with pytest.raises(KeyboardInterrupt):
        prefix.check([ULT(x, 10), x == 5, x == 6], 1000)
    monkeypatch.setattr(prefix.solver, "add", real_add)
    # x == 5 must not survive into a query that does not contain it.
    assert prefix.stack == [] and prefix.solver.num_scopes() == 0
    assert prefix.check([ULT(x, 10), x == 6], 1000) == sat
    # A scope pushed behind its back is detected before the check.
    prefix.solver.push()
    prefix.solver.add(x == 7)
    assert prefix.check([ULT(x, 10), x == 6], 1000) == sat
    assert len(prefix.solver.assertions()) == 2


# P2 ---------------------------------------------------------------------------

def _entry_case(monkeypatch):
    from tests.unit.test_block_summary_certificates import copy_case
    runtime, summary, state = copy_case(7)
    solved = []
    real = runtime._solve
    monkeypatch.setattr(runtime, "_solve", lambda name, *a, **k: solved.append(name) or real(name, *a, **k))
    return runtime, summary, state, solved


def test_summary_entry_answered_by_path_witness(monkeypatch):
    runtime, summary, state, solved = _entry_case(monkeypatch)
    path = ULT(x, 10)
    model = SolverFor("QF_AUFBV")
    model.add(path, *(state.assumptions or []))
    assert model.check() == sat
    runtime.apply(summary, state, path_condition=path, witness=model.model())
    assert "entry" not in solved and runtime.certificates[0].complete
    entry = next(r for r in runtime.certificates[0].obligations if r.name == "entry")
    assert entry.answer == entry.expected == "sat"


def test_summary_entry_solved_when_witness_misses(monkeypatch):
    runtime, summary, state, solved = _entry_case(monkeypatch)
    model = SolverFor("QF_AUFBV")
    model.add(x == 50)
    assert model.check() == sat
    runtime.apply(summary, state, path_condition=ULT(x, 10), witness=model.model())
    assert solved[0] == "entry" and runtime.certificates[0].complete


# P3 / P4 ----------------------------------------------------------------------

def _path(condition, witness=None):
    return SegmentPath("terminal", None, condition, SMTState.create_initial_state(num_inputs=0), witness)


EVM = [And(ULT(x, 10), ULT(x, 5)), And(ULT(x, 10), Not(ULT(x, 5))),
       And(Not(ULT(x, 10)), x == 20), And(Not(ULT(x, 10)), Not(x == 20))]


def test_disjoint_groups_cover_every_pair_once_and_weaken_it():
    groups = disjoint_groups(BoolVal(True), EVM)
    pairs = [p for members, _ in groups for p in members]
    assert sorted(pairs) == [(i, k) for i in range(4) for k in range(i + 1, 4)]
    assert len(groups) == 3   # (0,1) | (0..1, 2..3) | (2,3)
    for members, formula in groups:
        assert solve_query(formula, 1000) == "unsat"
        for i, k in members:  # the group query is implied by each member's full query
            assert solve_query(And(EVM[i], EVM[k], Not(formula)), 1000) == "unsat"
    # One condition a prefix of the other: the full query is kept.
    (only,) = disjoint_groups(BoolVal(True), [ULT(x, 10), And(ULT(x, 10), x == 3)])
    assert only[0] == [(0, 1)] and solve_query(only[1], 1000) == "sat"


def test_correspondence_records_and_mapping(monkeypatch):
    prover = BlockEquivalenceProver([], [], {}, timeout_ms=2000)
    calls = []

    def check_all(obligations, records):
        for name, formula, _ in obligations:
            calls.append(name)
            answer = solve_query(formula, 2000)
            records.append(Obligation(name, formula.sexpr(), answer))
            yield answer == "unsat"
    monkeypatch.setattr(prover, "_check_all", check_all)

    def model(*facts):
        s = Solver()
        s.add(*facts)
        assert s.check() == sat
        return s.model()
    x86 = [_path(ULT(x, 3), model(x == 1)),            # witness hits e0
           _path(And(UGT(x, 5), ULT(x, 8)), model(x == 99)),  # stale witness: solver
           _path(x == 20),                              # no witness: solver
           _path(And(UGT(x, 30), ULT(x, 40)), model(x == 35)),
           _path(And(x == 3, x == 4))]                  # empty
    records = []
    corr = prover._correspondence([_path(c) for c in EVM], x86, BoolVal(True), records)
    assert corr == (0, 1, 2, 3, None)
    assert len(calls) == 3
    assert [r.name for r in records] == [f"evm_disjoint_{i}_{k}" for i in range(4) for k in range(i + 1, 4)]
    assert all(r.proved for r in records)


def _sequential_check_all(prover, monkeypatch):
    calls = []

    def check_all(obligations, records):
        for name, formula, _ in obligations:
            calls.append((name, formula))
            answer = solve_query(formula, 2000)
            records.append(Obligation(name, formula.sexpr(), answer))
            yield answer == "unsat"
    monkeypatch.setattr(prover, "_check_all", check_all)
    return calls


def test_disjoint_dedup_keeps_names_and_coverage(monkeypatch):
    # Grouped or not, the evm_disjoint records are exactly the manifest's,
    # in its order, each proved, and each group query is a sub-conjunction
    # of the full pair query of every name it is recorded under.
    prover = BlockEquivalenceProver([], [], {}, timeout_ms=2000)
    calls = _sequential_check_all(prover, monkeypatch)
    evm = [_path(c) for c in EVM]
    x86 = [_path(And(ULT(x, 3), y == i)) for i in range(4)]
    records = []
    corr = prover._correspondence(evm, x86, BoolVal(True), records)
    assert corr == (0, 0, 0, 0)
    expected = [n for n in pair_obligation_names(len(evm), len(x86), corr, (2,) * 4) if n.startswith("evm_disjoint_")]
    assert [r.name for r in records] == expected and all(r.proved for r in records)
    assert len(calls) == len(disjoint_groups(BoolVal(True), EVM)) < len(expected)
    queries = {name: formula for name, formula in calls}
    for members, formula in disjoint_groups(BoolVal(True), EVM):
        group = queries["evm_disjoint_%d_%d" % members[0]]
        assert group.eq(formula)
        for i, k in members:
            record = next(r for r in records if r.name == f"evm_disjoint_{i}_{k}")
            assert record.formula == group.sexpr()
            assert solve_query(And(EVM[i], EVM[k], Not(group)), 1000) == "unsat"


def test_disjoint_group_failure_falls_back_to_full_pair_queries(monkeypatch):
    # e0, e1 diverge at ULT(x, 10) vs ULT(y, 10), which do not exclude each
    # other; their later conjuncts do. The full query decides the pair.
    prover = BlockEquivalenceProver([], [], {}, timeout_ms=2000)
    calls = _sequential_check_all(prover, monkeypatch)
    evm = [_path(And(ULT(x, 10), x == 1)), _path(And(ULT(y, 10), x == 2)), _path(And(UGT(x, 200), UGT(y, 200)))]
    x86 = [_path(And(x == 1, y == i)) for i in range(4)]
    records = []
    corr = prover._correspondence(evm, x86, BoolVal(True), records)
    assert corr == (0, 0, 0, 0)
    assert [r.name for r in records] == ["evm_disjoint_0_1", "evm_disjoint_0_2", "evm_disjoint_1_2"]
    assert all(r.proved for r in records)
    full_0_1 = And(BoolVal(True), evm[0].condition, evm[1].condition)
    assert [n for n, _ in calls].count("evm_disjoint_0_1") == 2  # group, then the full query
    assert records[0].formula == full_0_1.sexpr()


def test_disjoint_overlap_gives_full_product(monkeypatch):
    prover = BlockEquivalenceProver([], [], {}, timeout_ms=2000)
    _sequential_check_all(prover, monkeypatch)
    evm = [_path(And(ULT(x, 10), x == 1)), _path(And(ULT(y, 10), x == 1)), _path(UGT(x, 200))]
    x86 = [_path(And(x == 1, y == i)) for i in range(4)]
    records = []
    assert prover._correspondence(evm, x86, BoolVal(True), records) == ()
    assert records == []


# P5 ---------------------------------------------------------------------------

def test_coverage_refuted_over_mul_abstraction_first(monkeypatch):
    prover = BlockEquivalenceProver([], [], {}, timeout_ms=5000)
    w, z = BitVec("w", 64), BitVec("z", 64)
    paths = [_path(ULT(w * z, 10)), _path(UGT(w * z, 4))]
    for p in paths:
        p.state.assumptions = []
    monkeypatch.setattr(prover, "_check", lambda *a, **k: pytest.fail("cascade not needed"))
    records = []
    initial = SMTState.create_initial_state(num_inputs=0)
    initial.assumptions = []
    prover.check_paths(paths, paths, BoolVal(True), initial, records)
    assert [r.name for r in records] == ["evm_coverage", "x86_coverage"] and all(r.proved for r in records)


# P6 ---------------------------------------------------------------------------

def test_complement_refutation_hit_and_miss():
    guard = UGT(x * y, 40)
    path = And(BoolVal(True), ULT(y, 9), Not(guard), ULE(x, 200))
    assert refuted_by_complement(path, guard)                 # Not(guard) is a path conjunct
    assert refuted_by_complement(path, And(ULT(y, 9), ULT(x, 0)))  # simplify -> false
    assert not refuted_by_complement(path, UGT(x * y, 41))    # implied, but not syntactically: solver's job
    assert not refuted_by_complement(And(Not(guard), *[x != i for i in range(16)]), guard)  # outside the window
    assert not refuted_by_complement(path, Not(guard))        # consistent with the path: never a refutation
    assert refuted_by_complement(And(ULT(x, 3), And(ULT(y, 9), guard)), Not(guard))  # nested And is flattened


def test_summary_solve_skips_solver_on_complement(monkeypatch):
    from verification import block_summaries
    from tests.unit.test_block_summary_certificates import copy_case
    runtime, _, _ = copy_case(7)
    guard = Or(x == 3, UGT(y, 7))
    monkeypatch.setattr(block_summaries, "solve_query", lambda *a: pytest.fail("solver called"))
    record = runtime._solve("memgas_exit_guard_excluded", And(And(ULT(x, 9), Not(guard)), guard))
    assert record.proved
