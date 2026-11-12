"""Input-disjoint fresh symbols preserve the demonstrated abstraction models."""
import pytest
from z3 import (And, Array, BitVecSort, BoolSort, Const, Context, ForAll, Function,
                Lambda, Map, Select, Solver, UDiv, substitute)

from common.fresh_symbols import FreshSymbols


def answer(formula):
    solver = Solver(ctx=formula.ctx)
    solver.set(timeout=1000)
    solver.add(formula)
    return str(solver.check())


@pytest.mark.parametrize("case", ["divrem_result", "divrem_congruence", "mul_congruence", "uf_app"])
def test_allocator_keeps_the_four_original_sat_counterexamples_satisfiable(case):
    # A new test context starts its native fresh counter at zero. No factory
    # mock or counter manipulation hides the real name-collision behaviour.
    ctx = Context()
    word = BitVecSort(8, ctx)
    x, y = Const("fresh_x", word), Const("fresh_y", word)
    if case in ("divrem_result", "uf_app"):
        prefix = "divrem_result" if case == "divrem_result" else "uf_app"
        old = Const(f"{prefix}!0", word)
        term = UDiv(x, y) if case == "divrem_result" else Function("input_uf", word, word)(x)
        formula = term != old
        fresh = FreshSymbols(formula).const(word, prefix)
        assert str(fresh.decl().name()) != str(old.decl().name())
        weakened = substitute(formula, (term, fresh))
    else:
        old = Function("f!0", word, word, word)
        term = UDiv(x, y) if case == "divrem_congruence" else x * y
        formula = term != old(x, y)
        fresh = FreshSymbols(formula).function(word, word, word)
        assert str(fresh.name()) != str(old.name())
        weakened = substitute(formula, (term, fresh(x, y)))
    assert answer(formula) == answer(weakened) == "sat"


def test_normal_namespace_const_and_function_are_fresh():
    ctx = Context()
    word = BitVecSort(8, ctx)
    x, y = Const("normal_x", word), Const("normal_y", word)
    allocator = FreshSymbols(x == y)
    value = allocator.const(word, "new_word")
    function = allocator.function(word, word, word)
    assert not value.eq(x) and not value.eq(y)
    assert answer(And(x == y, value != x, function(x, y) != value)) == "sat"


def test_names_are_reserved_across_sorts_and_arities():
    ctx = Context()
    byte, word = BitVecSort(8, ctx), BitVecSort(16, ctx)
    existing = Const("reserved!0", word)
    allocator = FreshSymbols(existing)
    value = allocator.const(byte, "reserved")
    assert str(value.decl().name()) != "reserved!0"
    ctx = Context()
    word = BitVecSort(8, ctx)
    existing = Function("f!0", word, word)  # Different from the requested arity.
    function = FreshSymbols(existing).function(word, word, word)
    assert str(function.name()) != "f!0"


@pytest.mark.parametrize("kind", ["const", "function"])
def test_newly_allocated_names_are_reserved(kind):
    # Contexts have independent native counters; the allocator's reservation
    # must still keep the names it returned disjoint across its whole batch.
    first, second = Context(), Context()
    a, b = BitVecSort(8, first), BitVecSort(8, second)
    allocator = FreshSymbols()
    if kind == "const":
        names = [str(allocator.const(sort, "batch").decl().name()) for sort in (a, b)]
    else:
        names = [str(allocator.function(sort, sort).name()) for sort in (a, b)]
    assert len(set(names)) == 2


def test_multiple_inputs_and_contexts_do_not_skip_equal_ast_ids():
    first, second = Context(), Context()
    a, b = BitVecSort(8, first), BitVecSort(8, second)
    one, two = Const("first!0", a), Const("second!0", b)
    allocator = FreshSymbols(one, two)
    assert str(allocator.const(a, "second").decl().name()) != "second!0"


@pytest.mark.parametrize("binder", ["forall", "lambda"])
def test_binder_names_are_reserved_even_without_free_body_symbols(binder):
    ctx = Context()
    word = BitVecSort(8, ctx)
    bound = Const("bound!0", word)
    formula = ForAll([bound], bound == bound) if binder == "forall" else Lambda([bound], bound)
    value = FreshSymbols(formula).const(word, "bound")
    assert str(value.decl().name()) != "bound!0"


def test_uf_declarations_in_map_parameters_are_reserved():
    ctx = Context()
    word = BitVecSort(8, ctx)
    function = Function("f!0", word, word, word)
    left, right = Array("meta_left", word, word), Array("meta_right", word, word)
    formula = Select(Map(function, left, right), Const("meta_index", word)) == 0
    value = FreshSymbols(formula).function(word, word, word)
    assert str(value.name()) != "f!0"


def test_uf_declarations_only_in_quantifier_patterns_are_reserved():
    ctx = Context()
    word = BitVecSort(8, ctx)
    x = Const("pattern_x", word)
    predicate = Function("pattern_p", word, BoolSort(ctx))
    pattern_only = Function("f!0", word, word)
    formula = ForAll([x], predicate(x), patterns=[pattern_only(x)])
    value = FreshSymbols(formula).function(word, word)
    assert str(value.name()) != "f!0"
