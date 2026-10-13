import pytest
"""F (CErc20 10233) join_extracts identities, F1 memoized _subtract_base_term,
R1 id-keyed caches keep their keys alive (no foreign result for a recycled id)."""

from z3 import (Array, BitVec, BitVecSort, BitVecVal, Concat, Extract, Not, Select, Store, Z3Exception, ZeroExt, is_false,
                simplify)

import common.store_forwarding as sf
import verification.block_equivalence as be

v, w = BitVec("sf_v", 64), BitVec("sf_w", 64)
V = ZeroExt(0, (v >> 5) * (v >> 5)) + w  # carries a product, like gas_remaining


@pytest.fixture(autouse=True)
def _no_cache_no_pool(monkeypatch):
    # Answers must come from the solver, not a proof cache from earlier runs; serial _check_all
    # (with a pair pool, _check runs in worker processes where test patches do not apply).
    monkeypatch.delenv("BLOCK_PROOF_CACHE", raising=False)
    monkeypatch.delenv("BLOCK_PAIR_WORKERS", raising=False)


def _valid(claim):
    return be.solve_query(Not(claim), 3000) == "unsat"


def _bytes(x):
    return Concat(*[Extract(8 * i + 7, 8 * i, x) for i in reversed(range(8))])


def test_join_extracts_rejoins_byte_splits_exactly():
    assert sf.join_extracts(_bytes(V)).eq(V)
    part = Concat(Extract(63, 32, V), Extract(31, 16, V), Extract(7, 0, w))
    assert sf.join_extracts(part).eq(Concat(Extract(63, 16, V), Extract(7, 0, w)))


def test_join_extracts_soundness_never_joins_across_sources_or_gaps():
    gap = Concat(Extract(63, 40, V), Extract(31, 0, V))  # bits 39..32 missing
    other = Concat(Extract(63, 32, v), Extract(31, 0, w))  # adjacent ranges, different sources
    swapped = Concat(Extract(31, 0, V), Extract(63, 32, V))  # wrong order
    for e in (gap, other, swapped):
        assert sf.join_extracts(e).eq(e), e
    for e in (_bytes(V), gap, other, swapped, Concat(Extract(63, 32, V), Extract(31, 16, V), Extract(7, 0, w))):
        assert _valid(sf.join_extracts(e) == e)


def _limb_through_byte_stores(overwrite):
    """[r13+0x70..0x77] := bytes of V, later stores elsewhere (and optionally into the field)."""
    r13 = BitVec("sf_r13", 64)
    m = Array("sf_m", BitVecSort(64), BitVecSort(8))
    for i in range(8):
        m = Store(m, r13 + 0x70 + i, Extract(8 * i + 7, 8 * i, V))
    for i in range(8):
        m = Store(m, r13 + 0x30 + i, Extract(8 * i + 7, 8 * i, w))
    if overwrite:
        m = Store(m, r13 + 0x73, BitVecVal(0xAB, 8))
    return Concat(*[Select(m, r13 + 0x70 + i) for i in reversed(range(8))])


def test_forward_then_join_makes_the_mirror_goal_trivial():
    goal = _limb_through_byte_stores(False) == V
    assert is_false(simplify(Not(sf.join_extracts(sf.forward_selects(goal)))))


def test_forward_then_join_soundness_overwritten_byte_is_not_trivial():
    goal = _limb_through_byte_stores(True) == V
    rewritten = sf.join_extracts(sf.forward_selects(goal))
    assert not is_false(simplify(Not(rewritten)))
    assert be.solve_query(Not(rewritten), 3000) == "sat"


def test_subtract_base_term_memoized_equals_unmemoized():
    base = BitVec("sf_base", 64)
    addr = base + v + 0x40
    first = sf._subtract_base_term(addr, base)
    assert ("subtract", addr.get_id(), base.get_id()) in sf._MEMO
    again = sf._subtract_base_term(addr, base)
    raw = sf._subtract_base_term_raw(addr, base)
    assert first.eq(raw) and again.eq(raw)
    assert _valid(first + base == addr)


def test_subtract_base_term_memo_soundness_keys_on_both_terms():
    base, other = BitVec("sf_base2", 64), BitVec("sf_other", 64)
    addr = base + 8
    assert sf._subtract_base_term(addr, base) is not None
    assert sf._subtract_base_term(addr, other) is None  # a different base: not the cached hit
    assert sf._subtract_base_term(addr, other) is None
    assert _valid(sf._subtract_base_term(addr, base) + base == addr)


def _recycled_ids_poison(rewrite, build, rounds=100):
    """Count rounds where a shared cache disagrees with a fresh one after the inputs were freed."""
    shared, bad = {}, 0
    for i in range(rounds):
        t = build(i)
        try:
            got = rewrite(t, shared)
        except Z3Exception:  # a foreign cached subterm of another sort (old forward_selects)
            bad += 1
            continue
        bad += not got.eq(rewrite(t, {}))
        del t, got
    return bad


def test_join_extracts_shared_cache_survives_id_recycling():
    def build(i):
        y = BitVec("sf_rv", 64) + BitVecVal(i, 64)
        return Concat(Extract(63, 32, y), Extract(31, 0, y))
    assert _recycled_ids_poison(sf.join_extracts, build) == 0


def test_forward_selects_shared_cache_survives_id_recycling():
    def build(i):
        a, k = Array("sf_ra", BitVecSort(64), BitVecSort(8)), BitVec("sf_rk", 64)
        return Select(Store(a, k, BitVecVal(i % 256, 8)), k) + BitVecVal(i, 8)
    assert _recycled_ids_poison(sf.forward_selects, build) == 0
