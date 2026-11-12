import pytest
"""J (multi-word zero-test join, proved per instance on its generalisation) and
N (2^k * Extract rule, normalisation to a fixpoint past the old 6-round cap)."""
from z3 import And, BitVec, BitVecVal, Bool, Concat, Extract, Not, Or, is_false, simplify

import verification.block_equivalence as be

REAL_SOLVE = be.solve_query


@pytest.fixture(autouse=True)
def _no_cache_no_pool(monkeypatch):
    # Answers must come from the solver, not a proof cache from earlier runs; serial _check_all
    # (with a pair pool, _check runs in worker processes where test patches do not apply).
    monkeypatch.delenv("BLOCK_PROOF_CACHE", raising=False)
    monkeypatch.delenv("BLOCK_PAIR_WORKERS", raising=False)


def _valid(claim):
    return REAL_SOLVE(Not(claim), 5000) == "unsat"


def _sub_lemmas(lemmas):
    return [m for l in lemmas for m in l.lemmas]


# ---- J -----------------------------------------------------------------------------------------

s1, s2, s3, s4 = (BitVec(f"j_s{i}", 256) for i in range(1, 5))


def _split_or_zero(words, k=8):
    """x86's or/or/jnz over a word's high and low parts: (OR_t s_t[n-1:k] == 0, OR_t s_t[k-1:0] == 0)."""
    hi, lo = Extract(255, k, words[0]), Extract(k - 1, 0, words[0])
    for w in words[1:]:
        hi, lo = hi | Extract(255, k, w), lo | Extract(k - 1, 0, w)
    return hi == 0, lo == 0


def test_j_join_fires_on_the_split_or_shape_with_a_per_instance_proof():
    hi, lo = _split_or_zero([s1, s2])
    joins = be._zero_test_joins([hi, lo])
    assert len(joins) == 1
    i, j, eq, lemma = joins[0]
    assert (i, j) == (0, 1) and _valid(eq == And(s1 == 0, s2 == 0))
    assert lemma.name == "or_zero_join" and lemma.proved
    assert "j_s1" not in lemma.formula and "zj" in lemma.formula  # checked on the generalisation


def test_j_normalisation_records_one_proof_per_instance_and_preserves_meaning():
    (h1, l1), (h2, l2) = _split_or_zero([s1, s2]), _split_or_zero([s3, s4])
    F = And(h1, l1, h2, l2, Bool("j_p"))
    out, lemmas = be.normalize_word_arith(F)
    joins = [m for m in _sub_lemmas(lemmas) if m.name == "or_zero_join"]
    assert len(joins) == 2 and all(m.proved for m in joins)
    assert _valid(out == F)
    assert _valid(F == And(out, s1 == 0, s2 == 0, s3 == 0, s4 == 0))


def test_j_wrong_shapes_are_not_joined():
    t = BitVec("j_t", 255)  # 255 bits: t[254:7] has the width of s[255:8], but k = 7 != 8
    mixed_k = Extract(255, 8, s1) | Extract(254, 7, t)
    plain = Extract(255, 8, s1) | Extract(247, 0, s2)  # not a high part
    for hi, lo in ((mixed_k == 0, Extract(7, 0, s1) == 0),
                   (plain == 0, (Extract(7, 0, s1) | Extract(7, 0, s2)) == 0)):
        assert be._zero_test_joins([hi, lo]) == []
    hi, _ = _split_or_zero([s1, s2])
    _, lo_other = _split_or_zero([s1, s3])  # the low test is about other words
    assert be._zero_test_joins([hi, lo_other]) == []


def test_j_soundness_satisfiable_formula_stays_satisfiable():
    hi, _ = _split_or_zero([s1, s2])
    _, lo_other = _split_or_zero([s1, s3])
    F = And(hi, lo_other, Or(s1 != 0, s2 != 0))  # SAT: s2 = 1
    out, _ = be.normalize_word_arith(F)
    assert REAL_SOLVE(out, 5000) == "sat"
    records = []
    assert not be.BlockEquivalenceProver([], [], {}, timeout_ms=3000)._check("j_sat", F, records)


def test_j_fail_closed_when_the_generalised_lemma_is_not_proved(monkeypatch):
    monkeypatch.setattr(be, "solve_query", lambda q, ms: "unknown" if "zj" in q.sexpr() else REAL_SOLVE(q, ms))
    hi, lo = _split_or_zero([s1, s2])
    F = And(hi, lo, Bool("j_p"))
    out, lemmas = be.normalize_word_arith(F)
    assert not [m for m in _sub_lemmas(lemmas) if m.name == "or_zero_join"]
    assert out.eq(simplify(F, bv_sort_ac=True))  # unchanged: no s1 == 0 ∧ s2 == 0 was added


# ---- N -----------------------------------------------------------------------------------------

w = BitVec("n_w", 64)


def test_n_rule_rewrites_power_of_two_times_extract():
    t = 32 * Extract(6, 0, w)
    new = be._word_rewrite(t)
    assert new is not None and _valid(new == Concat(Extract(1, 0, w), BitVecVal(0, 5)))


def test_n_rule_soundness_every_width_and_shift():
    v = BitVec("n_v", 16)
    for n in range(2, 9):
        for lo in (0, 3):
            x = Extract(lo + n - 1, lo, v)
            for k in range(1, n):
                new = be._word_rewrite((1 << k) * x)
                if new is not None:
                    assert _valid(new == (1 << k) * x), (n, lo, k, new)
            assert be._word_rewrite(3 * x) is None or _valid(be._word_rewrite(3 * x) == 3 * x)


def test_n_normalisation_proves_the_x86_vs_evm_shift_shapes_equal():
    F = Not(32 * Extract(6, 0, w) == Concat(Extract(1, 0, w), BitVecVal(0, 5)))  # (32*w)[6:0] vs (w<<5)[6:0]
    out, lemmas = be.normalize_word_arith(F)
    assert is_false(out) and lemmas and all(l.proved for l in lemmas)


def test_n_soundness_wrong_bits_are_not_identified():
    F = Not(32 * Extract(6, 0, w) == Concat(Extract(2, 1, w), BitVecVal(0, 5)))  # SAT
    out, _ = be.normalize_word_arith(F)
    assert not is_false(out) and REAL_SOLVE(out, 5000) == "sat"


def _byte_split_chain(depth, wrong_level=None):
    """x_{i+1} = x_i + c_i written as Concat((x_i + c_i)[63:8], x_i[7:0] + c_i[7:0]): one
    Concat rewrite per level, each built on the previous one (a round per level)."""
    x, total = w, w
    cs = [BitVec(f"n_c{i}", 64) for i in range(depth)]
    for i, c in enumerate(cs):
        low = Extract(7, 0, x) + Extract(7, 0, c if i != wrong_level else c + 1)
        x = Concat(Extract(63, 8, x + c), low)
        total = total + c
    return Not(x == total)


def test_n_normalisation_runs_past_six_rounds_to_a_fixpoint(monkeypatch):
    rounds, real = [], be._join_and_decide
    monkeypatch.setattr(be, "_join_and_decide", lambda f, l: rounds.append(1) or real(f, l))
    out, lemmas = be.normalize_word_arith(_byte_split_chain(8))
    assert is_false(out) and len(rounds) > 6
    assert all(l.proved for l in lemmas)
    assert be.normalize_word_arith(out)[1] == ()  # fixpoint: nothing left to rewrite


def test_n_soundness_deep_chain_with_one_wrong_level_is_not_refuted():
    F = _byte_split_chain(8, wrong_level=5)  # SAT: the low byte at level 5 adds c + 1
    out, _ = be.normalize_word_arith(F)
    assert not is_false(out) and REAL_SOLVE(out, 5000) == "sat"
