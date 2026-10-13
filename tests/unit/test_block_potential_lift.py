"""potential route: the lift runs to a fixpoint (Safe 5377 H2 memory_gas_0 needs ~12 levels),
and literal P arguments are not merge candidates."""
from functools import partial

import pytest
from z3 import And, BitVec, BitVecVal, Bool, If, ULT, is_bv_value, simplify

import verification.block_equivalence as be
from verification.block_equivalence import BlockEquivalenceProver


@pytest.fixture(autouse=True)
def _no_cache_no_pool(monkeypatch):
    monkeypatch.delenv("BLOCK_PROOF_CACHE", raising=False)
    monkeypatch.delenv("BLOCK_PAIR_WORKERS", raising=False)


def _deep_cost_pair(levels):
    """EVM pushes C into every branch (C(w) at one leaf, C(k) literals elsewhere); x86 applies
    C once to the branch chain of word counts. Equal for every model; True means differ."""
    w = BitVec("pl_w", 64)
    conds = [Bool(f"pl_c{i}") for i in range(levels)]
    words = [BitVecVal(5 + i, 64) for i in range(levels)]
    evm, x86_words = be._memory_cost(w), w
    for c, k in zip(conds, words):
        evm = If(c, simplify(be._memory_cost(k)), evm)  # literal leaves, as the EVM side folds them
        x86_words = If(c, k, x86_words)
    return And(ULT(w, 2 ** 20), evm != be._memory_cost(x86_words))


def test_lift_reaches_the_fixpoint_past_four_levels(monkeypatch):
    formula = _deep_cost_pair(8)
    proved, answer, lemmas = BlockEquivalenceProver([], [], {}, timeout_ms=10000)._retry_over_potential(formula)
    assert answer == "unsat" and all(lemma.answer == "unsat" for lemma in lemmas)
    # The old cap (4 rounds) lifts half the chain: the abstraction stays satisfiable.
    monkeypatch.setattr(be, "telescope_potential", partial(be.telescope_potential, rounds=4))
    _, capped, _ = BlockEquivalenceProver([], [], {}, timeout_ms=10000)._retry_over_potential(_deep_cost_pair(8))
    assert capped != "unsat"


def test_lift_soundness_a_differing_leaf_stays_unproved():
    w, c = BitVec("pl_w", 64), Bool("pl_bad")
    evm = If(c, simplify(be._memory_cost(BitVecVal(6, 64))), be._memory_cost(w))
    x86 = be._memory_cost(If(c, BitVecVal(7, 64), w))  # differs whenever c holds
    formula = And(ULT(w, 2 ** 20), evm != x86)
    _, answer, _ = BlockEquivalenceProver([], [], {}, timeout_ms=10000)._retry_over_potential(formula)
    assert answer != "unsat"


def test_literal_potential_arguments_are_not_merge_candidates(monkeypatch):
    # A full lift adds axioms P(w0) == k; their literal w0 must not become merge candidates.
    p = be._potential(64)
    a, b = BitVec("pl_a", 64), BitVec("pl_b", 64)
    seen = []
    real = be._random_leaf_values
    monkeypatch.setattr(be, "_random_leaf_values", lambda terms, seeds: (seen.extend(terms) or real(terms, seeds)))
    formula = And(a == b, p(a) != p(b), p(BitVecVal(3, 64)) == 9, p(BitVecVal(4, 64)) == 12)
    be.unify_potential_arguments(formula, 3000)
    assert seen and not any(is_bv_value(t) for t in seen)
