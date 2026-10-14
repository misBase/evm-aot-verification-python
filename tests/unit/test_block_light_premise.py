"""Safe 5377 d30 pair_58_13/pair_68_9: refute over the light premise first.

Binder-free conjuncts with a non-literal product or a UF application (gas sums
over symbolic msize) are dropped; dropping conjuncts only adds models, so only
UNSAT of the rest transfers back.
"""
import pytest
from z3 import (And, Array, ArraySort, BitVec, BitVecSort, BitVecVal, Function, If, Lambda, Select, Store, ULT,
                simplify)

import verification.block_equivalence as be

BV64, BV8 = BitVecSort(64), BitVecSort(8)
a, b, x, y, w = (BitVec(f"lp_{s}", 64) for s in "abxyw")
g = Function("lp_g", BV64, BV64)
M = Array("lp_M", BV64, BV8)
i, k, n = BitVec("lp_i", 64), BitVec("lp_k", 64), BitVec("lp_n", 64)
v = BitVec("lp_v", 8)
sha3 = Function("lp_sha3_slice", ArraySort(BV64, BV8), BV64, BV64)
L_store = Lambda([i], If(ULT(i, n), Select(Store(M, k, v), i), BitVecVal(0, 8)))
L_plain = Lambda([i], If(ULT(i, n), Select(M, i), BitVecVal(0, 8)))
L_shift = Lambda([i], If(ULT(i, n), Select(M, i + 1), BitVecVal(0, 8)))


@pytest.fixture(autouse=True)
def _no_cache_no_pool(monkeypatch):
    monkeypatch.delenv("BLOCK_PROOF_CACHE", raising=False)
    monkeypatch.delenv("BLOCK_PAIR_WORKERS", raising=False)


def test_heavy_marks_products_and_uf_applications_only():
    assert be._heavy(x * y == w)
    assert be._heavy(g(a) == 0)
    assert not be._heavy(And(a == b + 1, 3 * a == w))  # literal coefficients stay light


def test_light_premise_refutes_without_the_heavy_conjuncts():
    parts = [a == b, x * y == w, g(x) == 7]
    proofs, kept = be._refute_over_light_premise(parts, a != b, 2000)
    assert kept == frozenset({parts[0].get_id()})
    assert be.solve_query(proofs[0][0], 2000) == "unsat"


def test_light_premise_misses_when_nothing_is_dropped_or_the_proof_needs_a_heavy_conjunct():
    assert be._refute_over_light_premise([a == b, a != 3], a != b, 2000) is None  # nothing heavy
    # a = b holds only through the products: the light premise is SAT, no proof.
    assert be._refute_over_light_premise([x * y == a, x * y == b], a != b, 2000) is None
    assert be._refute_over_light_premise([a == b, x * y == w], a != b, 0) is None  # no budget


def test_light_premise_keeps_conjuncts_under_a_binder():
    # A UF application over a lambda (memory argument) is heavy but has a binder: it stays.
    memory, slice_hash = Select(L_plain, k) == 1, sha3(L_plain, n) == 9
    parts = [memory, slice_hash, x * y == w]
    kept = be._refute_over_light_premise(parts, Select(L_plain, k) != 1, 2000)[1]
    assert kept == frozenset({memory.get_id(), slice_hash.get_id()})


def test_prove_equal_light_proof_transfers_to_premises_with_other_heavy_conjuncts():
    cache = {}
    assert be._prove_equal(And(a == b, x * y == w), a, b, 2000, None, cache) is not None
    (used, _, _), = cache[tuple(sorted((a.get_id(), b.get_id())))]
    assert used == frozenset({(a == b).get_id()})
    assert be._prove_equal(And(a == b, x * y == w + 1), a, b, 2000, None, cache) is not None
    # Soundness: equal only through the products, so the light route finds nothing.
    assert be._prove_equal(And(x * y == a, x * y == b + 1), a, b, 2000, None) is None


def _prover():
    return be.BlockEquivalenceProver([], [], {}, timeout_ms=3000)


def test_opaque_array_uf_light_after_unification():
    # The merged sha3 applications refute alone; the product is dead weight.
    F = And(v == Select(M, k), ULT(sha3(L_store, n), 5), ULT(5, sha3(L_plain, n)), x * y == w)
    proved, answer, lemmas = _prover()._retry_with_uf_unification(F, "unknown")
    assert answer == "unsat"
    names = [l.name for l in lemmas]
    assert "opaque_array_uf_light" in names and "opaque_array_uf" not in names, names
    assert all(l.answer == "unsat" for l in lemmas)
    assert be.solve_query(simplify(proved), 3000) == "unsat"


def test_opaque_array_uf_light_soundness_satisfiable_formula_is_not_refuted():
    # Different slices (sha3 may map them to 0 and 9): SAT with or without the product.
    n2 = BitVec("lp_n2", 64)
    F = And(n2 == n, ULT(sha3(L_plain, n), 5), ULT(5, sha3(L_shift, n2)), x * y == w)
    _, answer, _ = _prover()._retry_with_uf_unification(F, "unknown")
    assert answer != "unsat"
