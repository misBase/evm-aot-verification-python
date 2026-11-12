"""Deep products are abstracted completely, with exact builtin interpretation."""
import gzip
import hashlib
from pathlib import Path

import pytest
import z3 as z

import verification.block_equivalence as be


def sat(formula):
    solver = z.Solver(); solver.set(timeout=2000); solver.add(formula)
    return solver.check()


def check_roundtrip(formula, max_rounds=8):
    functions = {}
    abstract, changed = be.abstract_nonlinear_mul(formula, max_rounds=max_rounds, functions=functions)
    assert changed and not be._nonlinear_mul_terms(abstract)
    restored = be.concretize_mul(abstract, functions)
    assert restored.eq(z.simplify(formula))
    return abstract, functions


@pytest.mark.parametrize("positive", [1, 2, 8, 99])
def test_twenty_nested_products_are_one_complete_pass_for_any_positive_value(positive):
    a, b = z.BitVecs("deep_product_a deep_product_b", 8)
    value = a
    for _ in range(20): value = (value+b)*b
    formula = z.And(a == 3, b == 1, value == 23)
    abstract, functions = check_roundtrip(formula, positive)
    assert set(functions) == {(8, 2)}
    assert sat(formula) == sat(abstract) == z.sat


@pytest.mark.parametrize("disabled", [0, -1])
def test_nonpositive_is_an_exact_noop(disabled):
    a, b = z.BitVecs("disabled_product_a disabled_product_b", 8)
    formula, functions = z.And(a == 1, a*b != 0), {}
    target, changed = be.abstract_nonlinear_mul(formula, max_rounds=disabled, functions=functions)
    assert not changed and target.eq(formula) and functions == {}


def test_shared_terms_width_separation_and_unsigned_wrap():
    a, b = z.BitVecs("wrap_product_a wrap_product_b", 8)
    x, y = z.BitVecs("wrap_product_x wrap_product_y", 16)
    shared = a*b
    formula = z.And(a == 255, b == 2, shared == 254, shared+shared == 252,
                    x == 65535, y == 2, x*y == 65534)
    abstract, functions = check_roundtrip(formula)
    assert set(functions) == {(8, 2), (16, 2)}
    assert sat(formula) == sat(abstract) == z.sat
    used, seen, work = set(), set(), [abstract]
    while work:
        term = work.pop()
        if term.get_id() in seen: continue
        seen.add(term.get_id())
        if z.is_app(term) and term.decl().eq(functions[(8, 2)]): used.add(term.get_id())
        work.extend(term.children())
    assert len(used) == 1


def test_nary_products_preserve_the_complete_width_arity_signature():
    formula = z.And(*z.parse_smt2_string("""
        (declare-const arity_a (_ BitVec 8))
        (declare-const arity_b (_ BitVec 8))
        (declare-const arity_c (_ BitVec 8))
        (assert (= arity_a #xff)) (assert (= arity_b #x02)) (assert (= arity_c #x03))
        (assert (= (bvmul arity_a arity_b arity_c) #xfa))
    """))
    functions = {}
    abstract, changed = be.abstract_nonlinear_mul(formula, functions=functions)
    assert changed and not be._nonlinear_mul_terms(abstract)
    assert (8, 3) in functions and functions[(8, 3)].arity() == 3
    restored = be.concretize_mul(abstract, functions)
    check = z.Solver(); check.set(timeout=2000); check.add(formula != restored)
    assert check.check() == z.unsat
    assert sat(formula) == sat(abstract) == z.sat


def test_function_map_is_shared_only_across_exact_inputs_and_foreign_uf_is_preserved():
    a, b = z.BitVecs("shared_product_a shared_product_b", 8)
    functions = {}
    be.abstract_nonlinear_mul(a*b == 1, functions=functions)
    owned = functions[(8, 2)]
    be.abstract_nonlinear_mul((a+b)*b == 2, functions=functions)
    assert len(functions) == 1 and functions[(8, 2)].eq(owned)
    alias = z.Function(str(owned.name()), a.sort(), b.sort(), a.sort())
    assert alias.eq(owned)
    wrong_namespace = a*b != alias(a, b)
    assert sat(wrong_namespace) == z.sat
    with pytest.raises(ValueError, match="reserved function"):
        be.abstract_nonlinear_mul(wrong_namespace, functions=functions)
    foreign = z.Function("foreign_product", a.sort(), b.sort(), a.sort())
    formula = z.And(a == 1, b == 1, foreign(a, b) == 2, a*b != foreign(a, b))
    abstract, _ = check_roundtrip(formula)
    assert any(f.eq(foreign) for f in be._all_ufs(abstract))
    assert sat(formula) == sat(abstract) == z.sat


def test_new_function_cannot_alias_an_existing_input_function(monkeypatch):
    import common.fresh_symbols as symbols
    a, b = z.BitVecs("fresh_product_a fresh_product_b", 8)
    existing = z.Function("existing_product", a.sort(), b.sort(), a.sort())
    original = z.And(a == 1, b == 1, existing(a, b) == 2, a*b != existing(a, b))
    native, attempts = symbols.FreshFunction, []
    def collide(*sorts):
        attempts.append(True)
        return existing if len(attempts) == 1 else native(*sorts)
    monkeypatch.setattr(symbols, "FreshFunction", collide)
    abstract, functions = check_roundtrip(original)
    assert len(attempts) >= 2 and not any(f.eq(existing) for f in functions.values())
    assert sat(original) == sat(abstract) == z.sat


def test_quantifier_is_left_identical_and_not_entered():
    a, b, q = z.BitVecs("binder_product_a binder_product_b binder_product_q", 8)
    formula = z.And(z.ForAll(q, q*b != a), a*b != 3)
    original = z.simplify(formula)
    target, functions = check_roundtrip(formula)
    old = next(t for t in original.children() if z.is_quantifier(t))
    assert any(t.eq(old) for t in target.children())
    assert set(functions) == {(8, 2)}


def test_real_safe_maps8_has_no_residual_products_and_restores_ast_exactly():
    data = gzip.decompress((Path(__file__).parent/"data"/"block_18089_x86_maps_8_0.smt2.gz").read_bytes())
    assert hashlib.sha256(data).hexdigest() == "7d2ee5914f6ccd46779021fcf95228f9f97f3c4194ea2dbdad9c3ac3afc4bfb7"
    formula = z.And(*z.parse_smt2_string(data.decode()))
    assert len(be._nonlinear_mul_terms(formula)) == 295
    _, functions = check_roundtrip(formula)
    assert set(functions) == {(63, 2), (64, 2), (128, 2)}
