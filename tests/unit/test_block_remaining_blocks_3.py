"""Task N3 (remaining-blocks-3): generic fixes found on the frozen-compiler hex.

- UF guard cases (uf_guards / assume_guard / _retry_over_guard_cases): x86 SDIV is a
  sign-branch tree with one holiman_udiv application per branch, against EVM's single
  holiman_udiv(|a|, |b|); the arguments agree only under the sign guards, so the
  unification route never merges them (PoolManager 16670 pair_2_74 / pair_4_84 goal 2).
  Splitting on the guard first lets each case unify.
- _text_size: the merge loops' pair order by sexpr length, memoized (same values).
- forward_selects_shared: the DIV summary's limb forwarding through one process-level
  cache (Aave Pool 7200: each hit re-forwarded the whole x86 memory chain per limb).
- Resumed potential solve credited per obligation class ("resume" stats): once it refuted
  a class, siblings resume it right after the potential route instead of after every
  other route (Aave Pool 6182 pair_63_2 goal 6: 2350s of failing routes first).
- _correspondence: a row whose quick solve is unknown gets its proposal from the
  blast_select_store form (Aave Pool 6182 rows 2/3/4: unknown at 30s directly, SAT in ~6s
  blasted; unknown made them "all" rows).
"""
from pathlib import Path

import pytest
from z3 import (And, BitVec, BitVecSort, Bool, BoolVal, Function, If, Not, Or, Solver, Extract, parse_smt2_file,
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


def _memory_chain(n):
    from z3 import Array, BitVecSort as S, Store, BitVecVal
    mem = Array("n3_mem", S(64), S(8))
    base = BitVec("n3_base", 64)
    for k in range(n):
        mem = Store(mem, base + BitVecVal(k, 64), Extract(7, 0, a + k))
    return mem, base


def test_shared_forwarding_equals_fresh_forwarding():
    from z3 import BitVecVal, Concat, Select
    from common.store_forwarding import _SHARED_FORWARD, forward_selects, forward_selects_shared
    mem, base = _memory_chain(40)
    loads = [Concat(*[Select(mem, base + BitVecVal(8 * w + 7 - i, 64)) for i in range(8)]) for w in range(4)]
    for load in loads + loads:  # second round: every node from the cache
        assert forward_selects_shared(load).eq(forward_selects(load))
    assert _SHARED_FORWARD
    clear_memo()
    assert not _SHARED_FORWARD


def test_forwarded_limb_is_unchanged_by_the_shared_cache():
    from z3 import BitVecVal, Concat, Select, Store, Array, BitVecSort as S
    from x86_64.summaries.div import _forwarded_limb
    limb = a * b + 3
    mem = Array("n3_stack", S(64), S(8))
    base = BitVec("n3_r14", 64)
    for i in range(8):
        mem = Store(mem, base + BitVecVal(i, 64), Extract(8 * i + 7, 8 * i, limb))
    load = Concat(*[Select(mem, base + BitVecVal(7 - i, 64)) for i in range(8)])
    assert _forwarded_limb(load).eq(limb)
    assert _forwarded_limb(load).eq(limb)  # cached


def _resume_harness(monkeypatch, stats_win):
    """A prover whose routes all fail except the resumed potential solve; returns
    (prover, call log). The potential route leaves PENDING pending, as a capped
    solve that ran out does; solve_query refutes only PENDING."""
    from time import monotonic
    from z3 import Bool
    pending_target = Bool("n3_pending_target")
    calls = []
    prover = be.BlockEquivalenceProver([], [], {}, timeout_ms=1000)
    prover.deadline = monotonic() + 600

    def potential(self, formula):
        calls.append("potential")
        if self._potential_pending is None:
            self._potential_pending = (formula, pending_target, ())
        return formula, "unknown", ()

    def fail(tag):
        def route(self, formula, *a, **k):
            calls.append(tag)
            return formula, "unknown", ()
        return route

    def solve(query, ms, trust_unknown=True):
        if query.eq(pending_target):
            calls.append("resume")
            return "unsat"
        return "unknown"

    P = be.BlockEquivalenceProver
    monkeypatch.setattr(P, "_retry_over_potential", potential)
    for name in ("_retry_over_lia", "_retry_over_nonlinear_mul", "_retry_with_uf_unification",
                 "_retry_over_guard_cases"):
        monkeypatch.setattr(P, name, fail(name))
    monkeypatch.setattr(be, "solve_query", solve)
    if stats_win:
        prover._route_stats[be._route_class("pair_1_2_goal_6_of_7")] = {("resume", False): (1, 90.0)}
    return prover, calls


def test_resume_waits_for_every_route_without_history(monkeypatch):
    prover, calls = _resume_harness(monkeypatch, stats_win=False)
    records = []
    assert prover._check("pair_1_2_goal_6_of_7", And(udiv(a, b) == 1, udiv(b, a) == 2), records, split=False)
    assert calls[-1] == "resume" and "_retry_with_uf_unification" in calls
    stats = prover._route_stats[be._route_class("pair_1_2_goal_6_of_7")]
    assert stats[("resume", False)][0] == 1  # the win is credited to the class


def test_resume_comes_first_once_it_refuted_the_class(monkeypatch):
    prover, calls = _resume_harness(monkeypatch, stats_win=True)
    records = []
    assert prover._check("pair_1_2_goal_6_of_7", And(udiv(a, b) == 1, udiv(b, a) == 2), records, split=False)
    first = calls.index("potential")
    assert calls[first + 1] == "resume"
    assert "_retry_with_uf_unification" not in calls and "_retry_over_guard_cases" not in calls
    assert records[-1].proved and records[-1].formula == Bool("n3_pending_target").sexpr()


def test_blasted_model_is_a_model_of_the_formula():
    from z3 import Array, BitVecSort as S, BitVecVal, Select, Store, is_true, sat, unsat
    mem, base = _memory_chain(16)
    f = And(Select(mem, base + BitVecVal(3, 64)) == 9, a != 0)
    prover = be.BlockEquivalenceProver([], [], {}, timeout_ms=5000)
    answer, model = prover._blasted_model(f)
    assert answer == sat and is_true(model.eval(f, model_completion=True))
    answer, model = prover._blasted_model(And(f, Select(mem, base + BitVecVal(3, 64)) == 8))
    assert answer == unsat and model is None


def test_correspondence_falls_back_to_the_blasted_model(monkeypatch):
    from types import SimpleNamespace
    from z3 import BitVecVal, Select, unknown
    from x86_64.cfg_state import PrefixSolver
    monkeypatch.setattr(PrefixSolver, "check", lambda self, *args, **kw: unknown)
    mem, base = _memory_chain(8)
    word = Select(mem, base + BitVecVal(2, 64))
    evm = [SimpleNamespace(condition=c, witness=None) for c in (word == 1, word == 2, word == 3, word == 4)]
    x86 = [SimpleNamespace(condition=c, witness=None) for c in (
        And(a == 1, word == 3), And(a == 255, word == 1), And(word == 2, word == 5))]
    x86 += [SimpleNamespace(condition=word == k, witness=None) for k in (1, 2, 3, 4) for _ in range(4)]
    prover = be.BlockEquivalenceProver([], [], {}, timeout_ms=5000)
    found = prover._correspondence(evm, x86, BoolVal(True), [])
    assert found[:3] == (2, 0, None)
