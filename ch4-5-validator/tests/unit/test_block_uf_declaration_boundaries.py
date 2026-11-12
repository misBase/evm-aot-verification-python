"""Cached interpretations must never acquire input functions hidden in AST metadata."""
import pytest
import z3 as z

import verification.block_equivalence as be


def as_array(function):
    return z.ArrayRef(z.Z3_mk_as_array(function.ctx_ref(), function.ast), function.ctx)


def answer(formula):
    solver = z.Solver(); solver.set(timeout=2000); solver.add(formula)
    return solver.check()


def hidden_read(kind, function, x, y=None):
    if kind == "as_array":
        return z.Select(as_array(function), x) if y is None else z.Select(as_array(function), x, y)
    arrays = [z.K(x.sort(), x)] + ([] if y is None else [z.K(y.sort(), y)])
    return z.Select(z.Map(function, *arrays), z.BitVecVal(0, x.size()))


@pytest.mark.parametrize("kind", ["map", "as_array"])
def test_owned_mul_hidden_in_function_values_cannot_turn_real_sat_into_unsat(kind):
    x, y = z.BitVecs("hidden_mul_x hidden_mul_y", 16)
    functions = {}
    be.abstract_nonlinear_mul(x*y != 0, functions=functions)
    owned = functions[(16, 2)]
    original = x*y != hidden_read(kind, owned, x, y)
    assert answer(original) == z.sat
    assert any(f.eq(owned) for f in be._all_ufs(original))
    with pytest.raises(ValueError, match="reserved function"):
        be.abstract_nonlinear_mul(original, functions=functions)


@pytest.mark.parametrize("kind", ["map", "as_array"])
def test_cached_potential_hidden_in_function_values_is_not_reinterpreted(monkeypatch, kind):
    monkeypatch.setattr(be, "_POTENTIAL", {})
    word = z.BitVec("hidden_potential_word", 64)
    owned = be._potential(64)
    original = be._memory_cost(word) != hidden_read(kind, owned, word)
    assert answer(original) == z.sat
    assert any(f.eq(owned) for f in be._all_ufs(original))
    target, changed = be.abstract_memory_potential(original)
    assert not changed and target.eq(original) and answer(target) == z.sat


@pytest.mark.parametrize("kind", ["map", "as_array"])
def test_foreign_potential_function_values_do_not_disable_a_fresh_abstraction(monkeypatch, kind):
    monkeypatch.setattr(be, "_POTENTIAL", {})
    word = z.BitVec("foreign_potential_word", 64)
    foreign = z.Function("foreign_potential_function", word.sort(), word.sort())
    original = be._memory_cost(word) != hidden_read(kind, foreign, word)
    target, changed = be.abstract_memory_potential(original)
    assert changed and not be._POTENTIAL[64].eq(foreign)
    assert answer(original) == answer(target) == z.sat


@pytest.mark.parametrize("annotation", ["pattern", "no_pattern"])
def test_owned_function_in_quantifier_metadata_is_collected_and_rejected(annotation):
    x, y, q = z.BitVecs("annotated_x annotated_y annotated_q", 16)
    functions = {}
    be.abstract_nonlinear_mul(x*y != 0, functions=functions)
    owned = functions[(16, 2)]
    predicate = z.Function("independent_annotation_body", q.sort(), z.BoolSort())
    options = {"patterns": [owned(q, q)]} if annotation == "pattern" else {"no_patterns": [owned(q, q)]}
    quantifier = z.ForAll(q, predicate(q), **options)
    original = z.And(x*y != 0, quantifier)
    assert any(f.eq(owned) for f in be._all_ufs(original))
    with pytest.raises(ValueError, match="reserved function"):
        be.abstract_nonlinear_mul(original, functions=functions)


@pytest.mark.parametrize("annotation", ["pattern", "no_pattern"])
def test_metadata_uf_addition_to_witness_tiers_remains_a_sat_only_restriction(annotation):
    q = z.BitVec("witness_annotation_q", 8)
    predicate = z.Function("witness_annotation_body", q.sort(), z.BoolSort())
    hint = z.Function("witness_annotation_hint", q.sort(), q.sort())
    options = {"patterns": [hint(q)]} if annotation == "pattern" else {"no_patterns": [hint(q)]}
    formula = z.ForAll(q, predicate(q), **options)
    tiers = be._witness_tiers(formula)
    assert tiers and any(f.eq(hint) for f in tiers[-1])
    assert be.sat_by_constant_array_ufs(formula, 1000) == "sat"
    assert answer(formula) == z.sat


@pytest.mark.parametrize("kind", ["map", "as_array"])
def test_foreign_input_function_stays_foreign_and_witness_tiers_keep_refusing_function_values(kind):
    x, y = z.BitVecs("foreign_hidden_x foreign_hidden_y", 16)
    foreign = z.Function("foreign_function_value", x.sort(), y.sort(), x.sort())
    original = x*y != hidden_read(kind, foreign, x, y)
    assert be._array_argument_ufs(original) is None
    assert be._witness_tiers(original) == []
    functions = {}
    target, changed = be.abstract_nonlinear_mul(original, functions=functions)
    assert changed and not any(f.eq(foreign) for f in functions.values())
    assert answer(original) == answer(target) == z.sat
    assert z.simplify(be.concretize_mul(target, functions)).eq(z.simplify(original))


def test_parametric_map_declaration_is_preserved_when_rebuilding_changed_array_children():
    x, y, index = z.BitVecs("map_rebuild_x map_rebuild_y map_rebuild_i", 8)
    word = x.sort()
    left, right, result = (z.Array(name, word, word) for name in ("map_left", "map_right", "map_result"))
    foreign = z.Function("mapped_foreign", word, word, word)
    original = z.Map(foreign, z.Store(left, index, x*y), right) != result
    functions = {}
    target, changed = be.abstract_nonlinear_mul(original, functions=functions)
    assert changed and any(f.eq(foreign) for f in be._all_ufs(target))
    assert be.concretize_mul(target, functions).eq(z.simplify(original))


def test_as_array_and_uf_inside_lambda_remain_exact_when_other_products_change():
    x, y, index = z.BitVecs("lambda_rebuild_x lambda_rebuild_y lambda_rebuild_i", 8)
    foreign = z.Function("as_array_foreign", x.sort(), x.sort())
    array = z.Array("as_array_original", x.sort(), x.sort())
    binder = z.Lambda(index, foreign(index))
    original = z.And(as_array(foreign) == array, binder == array, x*y != 0)
    functions = {}
    target, changed = be.abstract_nonlinear_mul(original, functions=functions)
    assert changed and any(f.eq(foreign) for f in be._all_ufs(target))
    assert be.concretize_mul(target, functions).eq(z.simplify(original))
