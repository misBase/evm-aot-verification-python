"""F2 canon_binders (alpha-canonical binder names) and R2 (_to_smt2 refuses / repairs
binder capture: Z3's SMT2 printer does not rename a binder shadowing an outer one)."""
import pytest
from z3 import (And, Array, BitVec, BitVecSort, BitVecVal, Exists, ForAll, Function, Lambda, Not, QuantifierRef,
                Select, Solver, parse_smt2_string, to_symbol, z3core as C)

import verification.block_equivalence as be

S8, S64 = BitVecSort(8), BitVecSort(64)
M = Array("ac_M", S64, S8)
f = Function("ac_f", S8, S8, S8)
x, y, i = BitVec("ac_x", 8), BitVec("ac_y", 8), BitVec("ac_i", 8)


@pytest.fixture(autouse=True)
def _no_cache_no_pool(monkeypatch):
    # Answers must come from the solver, not a proof cache from earlier runs; serial _check_all
    # (with a pair pool, _check runs in worker processes where test patches do not apply).
    monkeypatch.delenv("BLOCK_PROOF_CACHE", raising=False)
    monkeypatch.delenv("BLOCK_PAIR_WORKERS", raising=False)


def canon(e, cache=None):
    from verification.alpha_canon import canon_binders
    return canon_binders(e, cache)


def _valid(claim):
    return be.solve_query(Not(claim), 3000) == "unsat"


def _round_trip(e):
    s = Solver()
    s.add(e)
    return parse_smt2_string(s.to_smt2())[0]


def _rename_inner(outer, name):
    """outer = Lambda(x, Select(Lambda(y, body), 3)) with the inner binder renamed to `name`
    (same de Bruijn body): a shadowing binder when name is outer's own binder name."""
    lam = outer.body().arg(0)
    ctx = lam.ctx
    inner = QuantifierRef(C.Z3_mk_lambda(ctx.ref(), 1, (C.Sort * 1)(lam.var_sort(0).ast),
                                         (C.Symbol * 1)(to_symbol(name, ctx)), lam.body().as_ast()), ctx)
    body = Select(inner, 3)
    return QuantifierRef(C.Z3_mk_lambda(ctx.ref(), 1, (C.Sort * 1)(outer.var_sort(0).ast),
                                        (C.Symbol * 1)(to_symbol(outer.var_name(0), ctx)), body.as_ast()), ctx)


OUTER_REF = Lambda([x], Select(Lambda([y], f(x, y)), 3))  # inner body refers to the outer x
SHADOW_REF = _rename_inner(OUTER_REF, OUTER_REF.var_name(0))  # same, inner binder also named ac_x
OWN_ONLY = _rename_inner(Lambda([x], Select(Lambda([y], f(y, y)), 3)), "ac_x")  # shadowing, no outer ref


def test_alpha_variants_become_one_ast():
    j = BitVec("ac_j", 64)
    k = BitVec("ac_k", 64)
    a, b = Lambda([j], Select(M, j + 1)), Lambda([k], Select(M, k + 1))
    assert not a.eq(b)  # precondition: bound names make distinct ASTs
    cache = {}
    assert canon(a, cache).eq(canon(b, cache))
    assert canon(Select(a, BitVecVal(4, 64)) == 0).eq(canon(Select(b, BitVecVal(4, 64)) == 0))


def test_canon_preserves_meaning_with_nested_binders():
    c = canon(OUTER_REF)
    assert _valid(Select(c, i) == Select(OUTER_REF, i))
    q = ForAll([x], Exists([y], f(x, y) == x))
    assert _valid(canon(q) == q)
    two = Lambda([x, y], f(x, y) + x)
    assert _valid(Select(canon(two), i, BitVecVal(5, 8)) == f(i, BitVecVal(5, 8)) + i)


def test_canon_smt2_round_trip_is_exact_for_nested_binders():
    for e in (Select(OUTER_REF, i) == 0, Select(SHADOW_REF, i) == 0,
              ForAll([x], Exists([y], Select(Lambda([i], f(i, x)), y) == x))):
        c = canon(e)
        back = _round_trip(c)
        assert back.sexpr() == c.sexpr()
        assert canon(back).eq(c)  # parsed lambdas are not .eq to built ones, but re-canonicalise to them
        assert _valid(back == e)


def test_canon_rejects_reserved_prefix_on_free_constants():
    from verification.alpha_canon import PREFIX
    clash = BitVec(f"{PREFIX}1_0", 8)
    with pytest.raises(ValueError):
        canon(clash + 1 == 0)
    with pytest.raises(ValueError):
        canon(Select(Lambda([x], x + clash), i) == 0)  # also inside a binder body


def test_binder_capture_risk_cases():
    from verification.alpha_canon import binder_capture_risk
    assert binder_capture_risk(Select(SHADOW_REF, i) == 0)
    assert not binder_capture_risk(Select(OUTER_REF, i) == 0)  # distinct names
    assert not binder_capture_risk(Select(OWN_ONLY, i) == 0)  # shadows, but never refers outward
    same_name_siblings = And(Select(Lambda([x], x + 1), i) == 0, Select(Lambda([x], x + 2), i) == 1)
    assert not binder_capture_risk(same_name_siblings)  # same name, not nested


def test_plain_smt2_printer_captures_the_shadowed_variable():
    # Documents why R2 exists: without renaming the round trip changes the meaning.
    e = Select(SHADOW_REF, i) == 0
    assert not _valid(_round_trip(e) == e)


def test_to_smt2_round_trip_preserves_meaning_under_shadowing():
    e = Select(SHADOW_REF, i) == 0
    back = And(*parse_smt2_string(be._to_smt2(e)))
    assert _valid(back == e)


def test_to_smt2_validates_capture_free_formulas_without_renaming_free_constants(monkeypatch):
    from z3 import simplify
    # The complete transport contract canonicalises all binders, even without
    # prior capture; raw text identity is no longer the acceptance criterion.
    e = Select(OWN_ONLY, i) == 0
    monkeypatch.setattr(Solver, "check", lambda *a, **kw: pytest.fail("transport is not an SMT proof"))
    back = parse_smt2_string(be._to_smt2(e), ctx=e.ctx)[0]
    assert canon(simplify(canon(e))).eq(canon(simplify(back)))
    text = be._to_smt2(e)
    assert "(declare-fun ac_i () (_ BitVec 8))" in text
    assert "(declare-fun ac_f ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))" in text


def test_to_smt2_refuses_when_renaming_is_impossible():
    from verification.alpha_canon import PREFIX
    clash = BitVec(f"{PREFIX}1_0", 8)
    with pytest.raises(ValueError):
        be._to_smt2(And(Select(SHADOW_REF, i) == clash))
