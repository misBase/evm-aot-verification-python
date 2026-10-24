"""Task N2 (remaining-blocks-2): generic fixes found on the frozen-compiler hex.

- Memoized identity proofs (_identity_proof): whether old == new is valid depends on the
  two terms only, so a proof found for one obligation proves the identity for its
  siblings; normalize_word_arith on Permit2 1327 x86_maps siblings repeated 191-192 of
  199 identity proofs. Failures are never cached across calls (a timeout can succeed on
  a retry), only within one normalize_word_arith call (the same query again).
"""
from pathlib import Path

import pytest
from z3 import And, BitVec, parse_smt2_file

import verification.block_equivalence as be
from common.store_forwarding import clear_memo

N2_SMT2 = Path(__file__).resolve().parents[2] / "cloud-inputs" / "n2" / "smt2"
x, y = BitVec("n2_x", 64), BitVec("n2_y", 64)


@pytest.fixture(autouse=True)
def _fresh_memo(monkeypatch):
    monkeypatch.delenv("BLOCK_PROOF_CACHE", raising=False)
    monkeypatch.delenv("BLOCK_PAIR_WORKERS", raising=False)
    clear_memo()
    yield
    clear_memo()


def _counting_solver(monkeypatch, answers=None):
    """Count be.solve_query calls; answers (a list) replaces the first results in order."""
    calls, real = [], be.solve_query

    def solve(query, ms):
        calls.append(query)
        return answers.pop(0) if answers else real(query, ms)

    monkeypatch.setattr(be, "solve_query", solve)
    return calls


def test_identity_proof_is_solved_once(monkeypatch):
    calls = _counting_solver(monkeypatch)
    old, new = x + x + y, (x << 1) + y
    assert be._identity_proof(old, new) == ()
    assert be._identity_proof(old, new) == ()
    assert len(calls) == 1


def test_failed_identity_is_retried(monkeypatch):
    # A timeout is not remembered: the next call queries again and can prove it.
    calls = _counting_solver(monkeypatch, answers=["unknown"])
    old, new = x + x + y, (x << 1) + y
    assert be._identity_proof(old, new) is None
    assert be._identity_proof(old, new) == ()
    assert len(calls) == 2


def test_memo_never_proves_a_non_identity():
    assert be._identity_proof(x + y, x) is None
    assert be._identity_proof(x + y, x) is None
    assert be._identity_holds(x + x, x << 1)
    assert not be._identity_holds(x + x, x << 2)


def test_clear_memo_drops_identity_proofs(monkeypatch):
    calls = _counting_solver(monkeypatch)
    old, new = x + x + y, (x << 1) + y
    be._identity_proof(old, new)
    clear_memo()
    be._identity_proof(old, new)
    assert len(calls) == 2


def test_normalize_does_not_retry_a_failed_rewrite_within_one_call(monkeypatch):
    # Every identity fails: each distinct (old, new) is tried once per call, however many rounds.
    tried = []
    monkeypatch.setattr(be, "_identity_proof_uncached", lambda old, new, ms: tried.append((old, new)))
    formula = And(*parse_smt2_file(str(N2_SMT2 / "permit2_1327_frozen" / "x86_empty_3.smt2")))
    be.normalize_word_arith(formula)
    keys = [(o.get_id(), n.get_id()) for o, n in tried]
    assert tried and len(keys) == len(set(keys))
    first = len(tried)
    be.normalize_word_arith(formula)  # a new call retries them
    assert len(tried) == 2 * first


def test_sibling_normalization_reuses_proofs():
    # The same formula normalised twice in one process: the second call proves nothing anew
    # and yields the same rewrites (same result, same lemmas; lambda lemmas print with
    # fresh quantifier ids, so they are compared by name).
    formula = And(*parse_smt2_file(str(N2_SMT2 / "permit2_1327_frozen" / "x86_empty_3.smt2")))
    first, lemmas1 = be.normalize_word_arith(formula)
    real, calls = be._identity_proof_uncached, []

    def counted(old, new, ms):
        calls.append(1)
        return real(old, new, ms)

    be._identity_proof_uncached = counted
    try:
        second, lemmas2 = be.normalize_word_arith(formula)
    finally:
        be._identity_proof_uncached = real
    assert second.eq(first)
    assert [lemma.name for lemma in lemmas2] == [lemma.name for lemma in lemmas1]
    assert all(lemma.proved for lemma in lemmas2)
    assert len(calls) < len(lemmas1)  # only the identities that failed before are tried again
