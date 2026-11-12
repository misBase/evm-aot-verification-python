"""Review of batch 3B (P1-P6 + light premise): the "could this be a false UNSAT?"
suspects that turned out sound, each pinned down by a randomized check against
an unbounded solver. (The one real bug, recycled ids in _prove_equal's lemma
cache, is test_block_lemma_cache_ids.py.)
"""
import random

import pytest
from z3 import (And, Array, BitVec, BitVecSort, BitVecVal, BoolVal, Exists, Extract, ForAll, Function, If, Lambda,
                Not, Or, Select, Solver, SolverFor, Store, UDiv, UGE, ULT, URem, ZeroExt, is_true, sat, unsat)

import verification.block_equivalence as be
from x86_64.cfg_state import PrefixSolver
from x86_64.summaries.base import refuted_by_complement

BV64, BV8 = BitVecSort(64), BitVecSort(8)


@pytest.fixture(autouse=True)
def _no_cache_no_pool(monkeypatch):
    monkeypatch.delenv("BLOCK_PROOF_CACHE", raising=False)
    monkeypatch.delenv("BLOCK_PAIR_WORKERS", raising=False)


def _unsat(*formulas):
    s = Solver()
    s.set("timeout", 20000)
    s.add(*formulas)
    return s.check() == unsat


# Light premise (the cache fix: test_block_lemma_cache_ids.py) ------------------

def test_light_premise_proofs_are_sound_on_random_conjunctions():
    # Whatever _heavy drops (including a heavy negated goal, as in
    # _retry_with_uf_unification's goal=True call), a proof means the full
    # conjunction is UNSAT.
    rng = random.Random(7)
    xs = [BitVec(f"rv_l{i}", 8) for i in range(4)]
    h = Function("rv_h", BV8, BV8)
    hits = 0
    for _ in range(120):
        parts = []
        for _ in range(rng.randrange(2, 6)):
            u, v = rng.sample(xs, 2)
            kind = rng.randrange(5)
            parts.append([u == v + rng.randrange(4), ULT(u, v), u * v == rng.randrange(8), h(u) != h(v),
                          Not(u == v)][kind])
        found = be._refute_over_light_premise(parts, BoolVal(True), 2000)
        if found is not None:
            hits += 1
            assert _unsat(*parts)
            assert found[1] <= {c.get_id() for c in parts}
    assert hits > 0


# P1 PrefixSolver -----------------------------------------------------------------

def _random_term(rng, xs, memory, depth=0):
    if depth > 2 or rng.random() < 0.3:
        return rng.choice(xs) if rng.random() < 0.7 else BitVecVal(rng.getrandbits(rng.choice((4, 16, 64))), 64)
    op = rng.randrange(6)
    u, v = _random_term(rng, xs, memory, depth + 1), _random_term(rng, xs, memory, depth + 1)
    if op == 5:
        return ZeroExt(56, Select(Store(memory, u, Extract(7, 0, v)), _random_term(rng, xs, memory, depth + 1)))
    return [u + v, u * v, u - v, u & v, u << (v & 7)][op]


def test_prefix_solver_never_wrong_unsat_with_budgets_that_cancel_checks():
    # Budgets of 1-50 ms (rlimit) cancel many checks mid-search; the incremental
    # solver must still answer UNSAT only for UNSAT conjunctions, and every SAT
    # model must satisfy every conjunct (it becomes the executor's witness).
    rng = random.Random(1)
    xs = [BitVec(f"rv_s{i}", 64) for i in range(5)]
    memory = Array("rv_M", BV64, BV8)
    prefix, path, seen = PrefixSolver(), [], set()
    for _ in range(120):
        if path and rng.random() < 0.4:
            del path[rng.randrange(0, len(path)):]
        if path and rng.random() < 0.3:
            path.append(Not(path[-1]))
        for _ in range(rng.randrange(1, 3)):
            u, v = _random_term(rng, xs, memory), _random_term(rng, xs, memory)
            atom = [u == v, ULT(u, v), UGE(u, v)][rng.randrange(3)]
            path.append(Not(atom) if rng.random() < 0.3 else atom)
        answer = prefix.check(list(path), rng.choice((1, 1, 2, 5, 50)))
        seen.add(str(answer))
        if answer == unsat:
            fresh = SolverFor("QF_AUFBV")
            fresh.set("timeout", 20000)
            fresh.add(*path)
            assert fresh.check() != sat
        elif answer == sat:
            model = prefix.solver.model()
            assert all(is_true(model.eval(c, model_completion=True)) for c in path)
        assert prefix.solver.num_scopes() == len(prefix.stack) == len(path)
    assert seen == {"sat", "unsat", "unknown"}


def test_prefix_solver_rlimit_is_per_check_and_witness_outlives_pops():
    u = BitVec("rv_u", 64)
    prefix = PrefixSolver()
    assert prefix.check([ULT(u, 10), UGE(u, 9)], 50) == sat
    witness = prefix.solver.model()
    for k in range(200):  # spend far more than one check's rlimit in total
        prefix.check([ULT(u, 10), u == k], 1)
    assert prefix.check([u == 1, u == 2], 1) == unsat  # a small budget still decides: not cumulative
    assert is_true(witness.eval(And(ULT(u, 10), UGE(u, 9)), model_completion=True))


# P2 model eval as SAT certificate ------------------------------------------------

def test_model_eval_is_never_literally_true_for_unsat_premises():
    x, y, n = BitVec("rv_ex", 8), BitVec("rv_ey", 8), BitVec("rv_en", 8)
    f = Function("rv_ef", BV8, BV8)
    A, B = Array("rv_eA", BV8, BV8), Array("rv_eB", BV8, BV8)
    s = Solver()
    s.add(f(BitVecVal(1, 8)) == 5, x == 3, Select(A, 7) == 9)
    assert s.check() == sat
    model = s.model()
    premises = [
        Exists([y], y * 0 == 1),
        ForAll([y], ULT(y, x)),
        Select(B, 0) != Select(B, 0),  # B is not in the model: completion
        B == Store(B, 0, Select(B, 0) + 1),
        UDiv(x, BitVecVal(0, 8)) != BitVecVal(255, 8),
        URem(x, BitVecVal(0, 8)) != x,
        And(y == 1, y == 2),
        Select(Lambda([y], If(ULT(y, n), Select(A, y), BitVecVal(0, 8))), 7) == 9,  # n completed to 0
    ]
    for premise in premises:
        value = model.eval(premise, model_completion=True)
        assert not is_true(value) or not _unsat(premise, f(BitVecVal(1, 8)) == 5, x == 3, Select(A, 7) == 9), premise


# P3 disjoint groups ---------------------------------------------------------------

def test_disjoint_groups_formulas_are_sub_conjunctions_on_random_trees():
    rng = random.Random(3)
    u = BitVec("rv_g8", 8)
    atoms = [ULT(u, k) for k in range(1, 9)] + [u == k for k in range(4)]
    premise = UGE(u, 1)
    shared = refuted = 0
    for _ in range(40):
        paths = [[]]
        for _ in range(rng.randrange(2, 7)):  # grow a DFS-like tree: copy a prefix, add edges
            base = list(rng.choice(paths))[:rng.randrange(0, 4)]
            edge = rng.choice(atoms)
            paths.append(base + [edge] + [rng.choice(atoms) for _ in range(rng.randrange(0, 3))])
            if rng.random() < 0.5:
                paths.append(base + [Not(edge)])
        conditions = [And(*c) if len(c) > 1 else (c[0] if c else BoolVal(True)) for c in paths]
        groups = be.disjoint_groups(premise, conditions)
        covered = [pair for pairs, _ in groups for pair in pairs]
        n = len(conditions)
        assert sorted(covered) == [(i, k) for i in range(n) for k in range(i + 1, n)]
        for pairs, formula in groups:
            shared += len(pairs) > 1
            parts = {c.get_id() for c in be._conjuncts(formula)}
            for i, k in pairs:
                full = {c.get_id() for c in be._conjuncts(And(premise, conditions[i], conditions[k]))}
                assert parts <= full
                if _unsat(formula):
                    refuted += 1
                    assert _unsat(premise, conditions[i], conditions[k])
    assert shared and refuted


# P6 complement refutation -------------------------------------------------------

def test_complement_refutation_agrees_with_the_solver_on_random_terms():
    rng = random.Random(5)
    xs = [BitVec(f"rv_c{i}", 8) for i in range(3)]
    def term(d=0):
        if d > 2 or rng.random() < 0.3:
            return rng.choice(xs) if rng.random() < 0.7 else BitVecVal(rng.randrange(256), 8)
        u, v = term(d + 1), term(d + 1)
        return [u + v, u * v, u - v, u & v, u | v, UDiv(u, v), URem(u, v), u >> (v & 7), If(ULT(u, v), u, v)][
            rng.randrange(9)]
    hits = 0
    for _ in range(150):
        cs = [[term() == term(), ULT(term(), term()), Not(term() == term())][rng.randrange(3)]
              for _ in range(rng.randrange(1, 4))]
        c = rng.choice(cs)
        goal = rng.choice([Not(c), Or(Not(c), BoolVal(False)), Not(And(c, BoolVal(True))), c, term() == term()])
        if refuted_by_complement(And(*cs), goal):
            hits += 1
            assert _unsat(*cs, goal)
    assert hits > 0
