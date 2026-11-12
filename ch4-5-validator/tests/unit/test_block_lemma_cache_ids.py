"""_prove_equal's lemma cache is keyed by AST ids and outlives the formulas the
ids came from. Without references, Z3 recycles a dead term's id for the next
term allocated, so a cached proof could answer for a premise that does not
imply x = y (a false merge, hence a false UNSAT). Proof entries now hold x, y
and their conjuncts (review-3b).
"""
import gc

import pytest
from z3 import And, BitVec, BitVecSort, BitVecVal, Function, Solver, unsat

import verification.block_equivalence as be

BV64 = BitVecSort(64)
a, b, z, p, q, w = (BitVec(f"lc_{s}", 64) for s in ("a", "b", "z", "p", "q", "w"))
g = Function("lc_g", BV64, BV64)


@pytest.fixture(autouse=True)
def _no_cache_no_pool(monkeypatch):
    monkeypatch.delenv("BLOCK_PROOF_CACHE", raising=False)
    monkeypatch.delenv("BLOCK_PAIR_WORKERS", raising=False)


def _shape(route, link):
    if route == "light":  # a dropped product: the light route proves it
        return And(link, p * q == w)
    return And(link, a != BitVecVal(0, 64))  # nothing heavy: the unsat_core route proves it


def _first_round(route, cache):
    head = g(a) if route == "core_uf" else a  # an opaque UF application: x is not in the stored proof
    x, y = head + BitVecVal(11, 64), b + BitVecVal(22, 64)
    assert be._prove_equal(_shape(route, x == y), x, y, 2000, None, cache) is not None


@pytest.mark.parametrize("route", ["light", "core", "core_uf"])
def test_prove_equal_cache_survives_id_recycling(route):
    cache = {}
    _first_round(route, cache)  # every term of round 1 is dead after this call
    gc.collect()
    head = g(a) if route == "core_uf" else a
    x2, y2 = head + BitVecVal(33, 64), b + BitVecVal(44, 64)  # same allocation order as round 1
    premise2 = _shape(route, x2 == z)
    s = Solver()
    s.add(premise2, x2 != y2)
    assert s.check() != unsat  # premise2 does not imply x2 = y2
    # Unfixed (light): round 1's entry matched on recycled ids and returned [(False, t)].
    assert be._prove_equal(premise2, x2, y2, 2000, None, cache) is None


@pytest.mark.parametrize("route", ["light", "core", "cases"])
def test_prove_equal_cache_entries_keep_their_ids_alive(route, monkeypatch):
    cache = {}
    x, y = a + BitVecVal(1, 64), b + BitVecVal(2, 64)
    premise = And(x == y, p * q == w) if route == "light" else And(x == y, a != BitVecVal(0, 64))
    if route == "cases":  # unsat_core misses: _refute_by_cases proves it, its entry holds every conjunct
        monkeypatch.setattr(be, "unsat_core", lambda *args: None)
    assert be._prove_equal(premise, x, y, 2000, None, cache) is not None
    (key, entries), = cache.items()
    for used, proofs, alive in entries:
        assert proofs is not None
        held = {t.get_id() for t in alive}
        premise_ctx, x_ctx, y_ctx, pair = key
        assert set(pair) <= held and used <= held
        assert {premise_ctx, x_ctx, y_ctx} <= {id(t.ctx) for t in alive}
