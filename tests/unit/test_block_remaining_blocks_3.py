"""Task N3 (remaining-blocks-3): generic fixes found on the frozen-compiler hex.

- UF guard cases (uf_guards / assume_guard / _retry_over_guard_cases): x86 SDIV is a
  sign-branch tree with one holiman_udiv application per branch, against EVM's single
  holiman_udiv(|a|, |b|); the arguments agree only under the sign guards, so the
  unification route never merges them (PoolManager 16670 pair_2_74 / pair_4_84 goal 2).
  Splitting on the guard first lets each case unify.
- _text_size: the merge loops' pair order by sexpr length, memoized (same values).
"""
from pathlib import Path

import pytest
from z3 import (And, BitVec, BitVecSort, BoolVal, Function, If, Not, Or, Solver, Extract, parse_smt2_file,
                simplify, unsat)

import verification.block_equivalence as be
from common.store_forwarding import clear_memo

N2_SMT2 = Path(__file__).resolve().parents[2] / "cloud-inputs" / "n2" / "smt2"
a, b = BitVec("n3_a", 64), BitVec("n3_b", 64)
udiv = Function("n3_udiv", BitVecSort(64), BitVecSort(64), BitVecSort(64))


@pytest.fixture(autouse=True)
def _fresh_memo(monkeypatch):
    monkeypatch.delenv("BLOCK_PROOF_CACHE", raising=False)
    monkeypatch.delenv("BLOCK_PAIR_WORKERS", raising=False)
    clear_memo()
    yield
    clear_memo()


def _sign(x):
    return Extract(63, 63, x) == 1


def _abs(x):
    return If(_sign(x), -x, x)


def _sdiv_pair():
    """EVM: udiv(|a|, |b|) negated when the signs differ; x86: a sign-branch tree,
    one udiv application per branch. The goal says the two quotients differ."""
    q = udiv(_abs(a), _abs(b))
    evm = If(_sign(a) == _sign(b), q, -q)
    x86 = If(_sign(a) == _sign(b),
             If(_sign(a), udiv(-a, -b), udiv(a, b)),
             If(_sign(a), -udiv(-a, b), -udiv(a, -b)))
    return evm, x86


def _unsat(formula):
    s = Solver()
    s.add(formula)
    return s.check() == unsat


def test_uf_guards_finds_the_branch_guards_smallest_first():
    evm, x86 = _sdiv_pair()
    guards = be.uf_guards(evm != x86)
    assert guards, "the sign guards sit above udiv applications"
    sizes = [be._text_size(simplify(raws[0])) for raws in guards]
    assert sizes == sorted(sizes)
    # Every guard is the condition of an ite with a udiv application in a branch.
    texts = {simplify(raws[0]).sexpr() for raws in guards}
    assert simplify(_sign(a) == _sign(b)).sexpr() in texts


def test_uf_guards_ignores_formulas_without_repeated_ufs():
    assert be.uf_guards(If(_sign(a), a, b) == udiv(a, b)) == []
    assert be.uf_guards(If(_sign(a), a, b) == b) == []


def test_guard_cases_cover_the_formula():
    # A satisfiable F keeps a model in some case; an unsatisfiable F has none in either.
    f = And(If(_sign(a), udiv(a, b), udiv(b, a)) == 7, udiv(a, b) != udiv(b, a))
    raws = be.uf_guards(f)[0]
    cases = [be.assume_guard(f, raws, v) for v in (True, False)]
    assert not all(_unsat(c) for c in cases)
    g = And(f, Not(_sign(a)), udiv(b, a) != 7)
    raws = be.uf_guards(g)[0]
    assert all(_unsat(be.assume_guard(g, raws, v)) for v in (True, False))


def test_assume_guard_is_equivalent_under_its_literal():
    evm, x86 = _sdiv_pair()
    f = evm != x86
    for raws in be.uf_guards(f):
        for value in (True, False):
            literal = raws[0] if value else Not(raws[0])
            case = be.assume_guard(f, raws, value)
            assert _unsat(And(literal, f) != case)  # (L ∧ F) ≡ case


def test_guard_cases_refute_the_sdiv_shape():
    evm, x86 = _sdiv_pair()
    prover = be.BlockEquivalenceProver([], [], {}, timeout_ms=10000)
    proved, answer, lemmas = prover._retry_over_guard_cases(evm != x86)
    assert answer == "unsat"
    assert lemmas and all(r.name.startswith("guard_") and r.proved for r in lemmas)
    assert {r.name.split("_")[2] for r in lemmas} == {"0", "1"}  # both cases of the first guard


def test_guard_cases_never_refute_a_satisfiable_formula():
    evm, x86 = _sdiv_pair()
    prover = be.BlockEquivalenceProver([], [], {}, timeout_ms=5000)
    # Off by one in the negative-quotient branch: a real difference.
    wrong = If(_sign(a) == _sign(b), x86, x86 + 1)
    assert prover._retry_over_guard_cases(evm != wrong)[1] != "unsat"


def test_guard_route_returns_at_once_without_guards(monkeypatch):
    calls = []
    monkeypatch.setattr(be, "solve_query", lambda *args, **kw: calls.append(args) or "unknown")
    prover = be.BlockEquivalenceProver([], [], {}, timeout_ms=5000)
    f = udiv(a, b) != udiv(b, a)
    assert prover._retry_over_guard_cases(f) == (f, "unknown", ())
    assert calls == []


def test_guard_route_is_in_both_route_tables():
    import inspect
    source = inspect.getsource(be.BlockEquivalenceProver._check)
    assert source.count('("guards", False), ("unify", True)') == 1
    assert source.count('("guards", False),\n                       ("unify", True)') == 1


def test_text_size_is_the_sexpr_length():
    t = udiv(_abs(a), b) + a
    assert be._text_size(t) == len(t.sexpr())
    assert be._text_size(t) == len(t.sexpr())  # memoized: same value


@pytest.mark.slow
def test_pm16670_goal_2_is_refuted_by_guard_cases():
    path = N2_SMT2 / "pm16670" / "pair_2_74_goal_2_of_7.smt2"
    prover = be.BlockEquivalenceProver([], [], {}, timeout_ms=30000)
    _, answer, lemmas = prover._retry_over_guard_cases(And(*parse_smt2_file(str(path))))
    assert answer == "unsat" and all(r.proved for r in lemmas)
