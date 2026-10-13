"""Normalisation that joins byte-split zero tests and decides ite guards, and the
blast route (reads through store chains blasted into ites) in _check."""
from z3 import (And, Array, BitVec, BitVecSort, Concat, Extract, Function, If, Not, Select, Store, is_false,
                is_store)

import verification.block_equivalence as be
from verification.block_equivalence import BlockEquivalenceProver

S = BitVecSort(64)
h = Function("zj_h", S, S)


def test_split_zero_test_decides_word_guard():
    # x86 tests len = z - f byte-split; EVM guards on z == f as a word (CErc20 10233, Safe 4626).
    z, f = BitVec("zj_z", 64), BitVec("zj_f", 64)
    split = And(Extract(7, 0, z) == Extract(7, 0, f), Extract(63, 8, z - f) == 0)
    formula = And(Not(split), h(If(z == f, 0, z)) != h(z))
    out, lemmas = be.normalize_word_arith(formula)
    assert is_false(out) and lemmas and all(lemma.proved for lemma in lemmas)


def test_a_top_level_literal_decides_its_guard_elsewhere():
    c = BitVec("zj_c", 64)
    out, _ = be.normalize_word_arith(And(c == 7, h(If(c == 7, c, 0)) != h(c)))
    assert is_false(out)


def _has_store(term):
    work, seen = [term], set()
    while work:
        t = work.pop()
        if t.get_id() in seen:
            continue
        seen.add(t.get_id())
        if is_store(t):
            return True
        work.extend(t.children())
    return False


def test_blast_route_refutes_a_read_through_a_store_chain(monkeypatch):
    # CErc20 4571: the solver stalls on x86 reads through symbolic-address store chains;
    # the same formula blasted into ites (as EVM memory is built) is refuted at once.
    mem, fmp = Array("zj_mem", S, BitVecSort(8)), Array("zj_fmp", S, BitVecSort(8))
    v, w = BitVec("zj_v", 8), BitVec("zj_w", 8)
    # x86 byte-split store base with a memory-read low byte, read at a constant slot:
    # neither alias (non-substitutable base) nor forwarding applies (CErc20 4571 / 10727).
    p = Concat(Extract(63, 8, BitVec("zj_f", 64)), Select(fmp, 0x5f))
    chain = Store(Store(mem, p, v), p + 1, w)
    read = Concat(Select(chain, 0x59), Select(chain, 0x58))

    def byte(a):
        return If(p + 1 == a, w, If(p == a, v, Select(mem, a)))
    word = Concat(byte(0x59), byte(0x58))
    real = be.solve_query
    monkeypatch.setattr(be, "solve_query", lambda query, ms: "unknown" if _has_store(query) else real(query, ms))
    monkeypatch.setattr(be, "solve_pure_bv", lambda query, ms: "unknown")
    records = []
    assert BlockEquivalenceProver([], [], {}, timeout_ms=3000)._check("pair_0_1", read != word, records)
    assert records[-1].proved
