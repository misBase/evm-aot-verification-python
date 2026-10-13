import pytest
"""F4 (unify skips argument pairs of applications that can no longer merge),
POTCAP (capped final potential solve) and POTRESUME (only its own capped solve is resumed)."""
from time import monotonic

from z3 import And, BitVec, BitVecSort, Bool, Function, Not, ULT

import verification.block_equivalence as be

REAL_SOLVE = be.solve_query
a1, a2, p, q = (BitVec(f"u_{s}", 64) for s in ("a1", "a2", "p", "q"))
hf = Function("u_h", BitVecSort(64), BitVecSort(64), BitVecSort(64))
b1, b2 = p + q, q + p  # equal without any premise; longer than a1 / a2, so tried after them


@pytest.fixture(autouse=True)
def _no_cache_no_pool(monkeypatch):
    # Answers must come from the solver, not a proof cache from earlier runs; serial _check_all
    # (with a pair pool, _check runs in worker processes where test patches do not apply).
    monkeypatch.delenv("BLOCK_PROOF_CACHE", raising=False)
    monkeypatch.delenv("BLOCK_PAIR_WORKERS", raising=False)


def _recording_prove_equal(monkeypatch):
    tried, real = [], be._prove_equal
    monkeypatch.setattr(be, "_prove_equal", lambda pre, x, y, *a, **k: tried.append((x, y)) or real(pre, x, y, *a, **k))
    return tried


def _tried(tried, x, y):
    return any((s.eq(x) and t.eq(y)) or (s.eq(y) and t.eq(x)) for s, t in tried)


def test_f4_skips_a_pair_whose_applications_already_failed_to_merge(monkeypatch):
    tried = _recording_prove_equal(monkeypatch)
    F = Not(hf(a1, b1) == hf(a2, b2))  # a1 = a2 is not provable: h(a1, .) and h(a2, .) never merge
    out, lemmas = be.unify_uf_arguments(F, 3000)
    assert _tried(tried, a1, a2)
    assert not _tried(tried, b1, b2)
    assert lemmas == ()


def test_f4_still_merges_a_pair_another_application_pair_needs(monkeypatch):
    tried = _recording_prove_equal(monkeypatch)
    # h(a1, c1) vs h(a1, c2) differ only in c: that pair is not hopeless (c1 = c2 needs p == q).
    c1, c2 = p + 1, q + 1
    F = And(p == q, Not(hf(a1, c1) == hf(a2, c2)), ULT(hf(a1, c1), 5), ULT(5, hf(a1, c2)))
    out, lemmas = be.unify_uf_arguments(F, 3000)
    assert _tried(tried, c1, c2) and lemmas
    assert REAL_SOLVE(out, 3000) == "unsat"  # h(a1, b1), h(a1, b2) are one term now


def test_f4_soundness_unprovable_arguments_are_never_merged():
    F = And(p == q, Not(hf(a1, p) == hf(a2, q)))  # SAT: a1 != a2
    out, _ = be.unify_uf_arguments(F, 3000)
    assert REAL_SOLVE(out, 3000) == "sat"


# ---- potential route ------------------------------------------------------------------------

x, y = BitVec("u_x", 64), BitVec("u_y", 64)
MARK = Bool("u_potential_marker")  # in the telescoped target only


def _stub_potential(monkeypatch, applies=lambda f: True):
    """The memory-cost rewrite chain reduced to: target = F ∧ marker (when `applies`)."""
    monkeypatch.setattr(be, "abstract_memory_potential", lambda f: (f, applies(f)))
    monkeypatch.setattr(be, "telescope_potential", lambda f: (And(f, MARK), (), (), 1))
    monkeypatch.setattr(be, "unify_potential_arguments", lambda t, *a, **k: (t, ()))


def _solve_marker_with(monkeypatch, need_ms, budgets=None):
    """Queries with the marker are 'unsat' given > need_ms, else 'unknown'; everything else
    'unknown' (every other route fails)."""
    def solve(query, ms):
        if "u_potential_marker" in query.sexpr():
            if budgets is not None:
                budgets.append(ms)
            return "unsat" if ms > need_ms else "unknown"
        return "unknown"
    monkeypatch.setattr(be, "solve_query", solve)
    monkeypatch.setattr(be, "refute_over_bv_abstraction", lambda f, ms: (f, "unknown"))


def _prover(timeout_ms=1000, seconds=None):
    prover = be.BlockEquivalenceProver([], [], {}, timeout_ms=timeout_ms)
    prover.deadline = None if seconds is None else monotonic() + seconds
    return prover


def test_potcap_final_solve_capped_at_four_query_timeouts(monkeypatch):
    _stub_potential(monkeypatch)
    budgets = []
    _solve_marker_with(monkeypatch, need_ms=10**9, budgets=budgets)
    prover = _prover(seconds=100)
    proved, answer, lemmas = prover._retry_over_potential(ULT(x, y))
    assert answer == "unknown" and budgets and max(budgets) <= 4 * prover.timeout_ms
    assert prover._potential_pending[0].eq(ULT(x, y))  # kept for _check to resume
    prover._retry_over_potential(ULT(y, x))
    assert prover._potential_pending[0].eq(ULT(x, y))  # the first one is not overwritten


def test_potcap_sat_is_not_left_pending(monkeypatch):
    _stub_potential(monkeypatch)
    monkeypatch.setattr(be, "solve_query", lambda f, ms: "sat")
    prover = _prover(seconds=100)
    prover._retry_over_potential(ULT(x, y))
    assert prover._potential_pending is None


def test_potresume_every_route_fails_then_the_capped_solve_is_resumed(monkeypatch):
    _stub_potential(monkeypatch)
    # Needs 15s: more than the 4 x 1000 ms cap and than the route's share (1/3 of 30s).
    _solve_marker_with(monkeypatch, need_ms=15_000)
    F = And(ULT(x, y), ULT(y, x))
    records = []
    assert _prover(seconds=30)._check("pot", F, records)
    assert "u_potential_marker" in records[-1].formula  # what was refuted: the telescoped target


def test_potresume_without_a_node_deadline_nothing_is_resumed(monkeypatch):
    _stub_potential(monkeypatch)
    _solve_marker_with(monkeypatch, need_ms=4000)
    records = []
    assert not _prover()._check("pot", And(ULT(x, y), ULT(y, x)), records)


def test_potresume_soundness_foreign_pending_entry_is_not_claimed(monkeypatch):
    # A route leaves a pending entry for some other input; resuming it would "prove" F.
    _solve_marker_with(monkeypatch, need_ms=0)
    prover = _prover(seconds=30)
    other = Bool("u_other_input")

    def foreign(formula, answer, split=False):
        prover._potential_pending = (other, And(other, MARK), ())
        return formula, answer, ()
    monkeypatch.setattr(prover, "_retry_over_nonlinear_mul", foreign)
    records = []
    assert not prover._check("pot", ULT(x, y), records)  # SAT
    assert "u_potential_marker" not in records[-1].formula


def test_potresume_soundness_nested_check_pending_is_not_claimed(monkeypatch):
    # A nested _check inside a route resumes its own potential solve; the entry it leaves
    # behind belongs to the inner formula and must not prove the outer (SAT) one.
    inner_input = Bool("u_inner")
    _stub_potential(monkeypatch, applies=lambda f: "u_inner" in f.sexpr())
    _solve_marker_with(monkeypatch, need_ms=4000)
    prover = _prover(seconds=60)
    inner = []

    def nested(formula, answer, split=False):
        if not inner:
            prover._check("inner", And(inner_input, ULT(x, 3)), inner)
        return formula, answer, ()
    monkeypatch.setattr(prover, "_retry_over_nonlinear_mul", nested)
    records = []
    assert not prover._check("outer", ULT(x, y), records)
    assert inner and inner[-1].proved  # precondition: the nested entry existed and was resumed there
    assert "u_potential_marker" not in records[-1].formula
