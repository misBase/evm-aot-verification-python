"""UF result sorts must survive transport; old alpha caches can contain lossy answers."""
from hashlib import sha256

import pytest
import z3 as z

import common.isolated_sat as isolated
from common.fresh_symbols import FreshSymbols
import verification.block_equivalence as be
from verification import proof_cache as pc


def formulas():
    x, y, t = z.BitVecs("overload_x overload_y overload_t", 8)
    f = z.Function("overload_f", x.sort(), z.BoolSort())
    g = z.Function("overload_f", x.sort(), x.sort())
    safe_f = z.Function("distinct_bool_function", x.sort(), z.BoolSort())
    safe_g = z.Function("distinct_word_function", x.sort(), x.sort())
    return (z.And(z.Distinct(g(x), g(y), g(t)), f(x) == f(y)),
            z.And(z.Distinct(safe_g(x), safe_g(y), safe_g(t)), safe_f(x) == safe_f(y)))


def answer(formula):
    solver = z.Solver(); solver.set(timeout=1000); solver.add(formula)
    return solver.check()


def old_key(kind, *assertions):
    version = f"{z.get_version_string()}\0{kind}\0"
    return sha256(f"{version}alpha\0{pc.alpha_digest(assertions)}".encode()).hexdigest()


def test_demonstrated_lossy_sat_to_unsat_transport_is_rejected():
    original, _ = formulas()
    solver = z.Solver(); solver.add(original)
    assert answer(original) == z.sat
    assert answer(z.And(*z.parse_smt2_string(solver.to_smt2()))) == z.unsat
    assert FreshSymbols(original).has_overloads
    with pytest.raises(ValueError, match="overloaded declarations"):
        be._to_smt2(original)


def test_isolation_refuses_overloaded_input_before_starting_a_child(monkeypatch):
    original, _ = formulas()
    monkeypatch.setattr(isolated.subprocess, "run", lambda *a, **kw: pytest.fail("unsafe query sent to child"))
    assert isolated.isolated_sat(original, 1000) == "unknown"


def test_parallel_checks_validate_the_entire_batch_before_submitting(monkeypatch):
    from types import SimpleNamespace
    original, _ = formulas()
    pool = SimpleNamespace(submit=lambda *a, **kw: pytest.fail("partial batch submitted before validation"))
    monkeypatch.setattr(be, "_pair_pool", lambda: pool)
    prover = object.__new__(be.BlockEquivalenceProver)
    prover.deadline, prover.timeout_ms = None, 1000
    checked = []
    prover._check = lambda name, formula, records: checked.append(name) or False
    # Not transportable: the whole batch is checked in this process, none of it in the pool.
    assert list(prover._check_all([("safe", z.BoolVal(True), ""), ("unsafe", original, "")], [])) == [False, False]
    assert checked == ["safe", "unsafe"]


def test_parallel_alias_cases_validate_before_submitting(monkeypatch):
    from time import monotonic
    from types import SimpleNamespace
    original, _ = formulas()
    monkeypatch.setattr(be, "solve_query", lambda *a, **kw: "unknown")
    pool = SimpleNamespace(submit=lambda *a, **kw: pytest.fail("partial alias batch submitted before validation"))
    monkeypatch.setattr(be, "_pair_pool", lambda: pool)
    # Not transportable: no alias proof at all (the caller's other routes go on), nothing submitted.
    assert be._refute_alias_queries([("safe", z.BoolVal(True)), ("unsafe", original)],
                                    1000, monotonic()+5, None, True) is None


def test_unique_names_and_repeated_identical_declarations_remain_supported():
    _, safe = formulas()
    repeated = z.And(safe, safe)
    assert not FreshSymbols(repeated).has_overloads
    assert answer(z.And(*z.parse_smt2_string(be._to_smt2(repeated)))) == answer(repeated) == z.sat


def test_old_wrong_alpha_answer_cannot_poison_a_safely_renamed_query(tmp_path, monkeypatch):
    unsafe, safe = formulas()
    assert old_key("check", unsafe) == old_key("check", safe)
    assert answer(safe) == z.sat and not FreshSymbols(safe).has_overloads
    monkeypatch.setenv("BLOCK_PROOF_CACHE", str(tmp_path/"old-alpha.sqlite"))
    pc.store(old_key("check", unsafe), "unsat")
    assert pc.query_key("check", safe)[0] != old_key("check", safe)
    assert be.solve_query(safe, 1000) == "sat"
    assert pc.lookup(old_key("check", unsafe)) == "unsat"
    assert pc.lookup(pc.query_key("check", safe)) == "sat"


def test_old_wrong_core_is_not_read(tmp_path, monkeypatch):
    _, safe = formulas()
    monkeypatch.setenv("BLOCK_PROOF_CACHE", str(tmp_path/"old-core.sqlite"))
    goal = z.BoolVal(True)
    pc.store(old_key("core", safe, goal), [])
    assert be.unsat_core([safe], goal, 1000) is None


def test_old_lemma_statement_namespace_is_also_invalidated(tmp_path, monkeypatch):
    _, safe = formulas()
    monkeypatch.setenv("BLOCK_PROOF_CACHE", str(tmp_path/"old-lemma.sqlite"))
    labels = (("unsafe_transport", "unsat"),)
    body = pc.alpha_digest([safe])
    old = sha256(f"{z.get_version_string()}\0lemma\0summary_lemma\0{labels!r}\0{body}".encode()).hexdigest()
    pc.record_lemma(old)
    key = pc.statement_key("summary_lemma", [("unsafe_transport", "unsat", safe)])
    assert key != old and not pc.lemma_proved(key)
    pc.record_lemma(key)
    assert pc.lemma_proved(key)


@pytest.mark.parametrize("kind", ["map", "as_array", "pattern", "no_pattern"])
def test_overloads_in_declaration_parameters_and_annotations_are_seen(kind):
    word = z.BitVecSort(8)
    x = z.Const("overload_metadata_x", word)
    f = z.Function("overload_metadata_f", word, word)
    g = z.Function("overload_metadata_f", word, z.BoolSort())
    if kind == "map":
        hidden = z.Map(g, z.K(word, x)) == z.K(word, z.BoolVal(True))
    elif kind == "as_array":
        array = z.ArrayRef(z.Z3_mk_as_array(g.ctx_ref(), g.ast), g.ctx)
        hidden = z.Select(array, x)
    else:
        options = {"patterns": [g(x)]} if kind == "pattern" else {"no_patterns": [g(x)]}
        hidden = z.ForAll(x, x == x, **options)
    original = z.And(f(x) == x, hidden)
    assert FreshSymbols(original).has_overloads
    with pytest.raises(ValueError, match="overloaded declarations"):
        be._to_smt2(original)


@pytest.mark.parametrize("kind", ["bvadd", "true", "and", "let"])
def test_builtin_spelling_cannot_alias_a_real_builtin_in_the_complete_formula(kind):
    word = z.BitVecSort(8)
    x, y = z.BitVecs("builtin_transport_x builtin_transport_y", 8)
    p, q = z.Bools("builtin_transport_p builtin_transport_q")
    if kind == "bvadd": formula = z.Function("bvadd", word, word, word)(x, y) != x+y
    elif kind == "true": formula = z.Distinct(z.Bool("true"), z.BoolVal(True))
    elif kind == "and": formula = z.Function("and", p.sort(), q.sort(), p.sort())(p, q) != z.And(p, q)
    else: formula = z.Function("let", word, word, word)(x, y) != x+y
    assert not FreshSymbols(formula).has_overloads and answer(formula) == z.sat
    with pytest.raises(ValueError, match="SMT2 round trip"):
        be._to_smt2(formula)


def test_a_single_declaration_probe_alone_misses_builtin_shadowing():
    word = z.BitVecSort(8)
    function = z.Function("bvadd", word, word, word)
    symbols = FreshSymbols(function)
    left, right = (symbols.const(word, "probe_arg") for _ in range(2))
    result = symbols.const(word, "probe_result")
    probe = function(left, right) == result
    solver = z.Solver(); solver.add(probe)
    assert probe.eq(z.parse_smt2_string(solver.to_smt2())[0])
    # The declaration roundtrips alone, but cannot coexist faithfully with builtin add.
    formula = function(left, right) != left+right
    assert answer(formula) == z.sat
    with pytest.raises(ValueError): be._to_smt2(formula)


@pytest.mark.parametrize("kind", ["uf", "bool", "bv", "store", "lambda", "map", "as_array", "forall"])
def test_full_gate_preserves_normal_compositions_and_binder_metadata(kind):
    from verification.alpha_canon import canon_binders
    word = z.BitVecSort(8)
    x, y = z.BitVecs("normal_transport_x normal_transport_y", 8)
    array = z.Array("normal_transport_array", word, word)
    function = z.Function("normal_transport_function", word, word)
    if kind == "uf": formula = function(x) != function(y)
    elif kind == "bool": formula = z.Or(z.Bool("normal_transport_flag"), x != y)
    elif kind == "bv": formula = x+y != x
    elif kind == "store": formula = z.Select(z.Store(array, x, y), y) != x
    elif kind == "lambda": formula = z.Lambda(x, function(x)) != array
    elif kind == "map": formula = z.And(z.Map(function, array) != array, function(x) == y)
    elif kind == "as_array":
        value = z.ArrayRef(z.Z3_mk_as_array(function.ctx_ref(), function.ast), function.ctx)
        formula = value != array
    else: formula = z.ForAll(x, function(x) == x)
    canonical = canon_binders(z.simplify(canon_binders(formula)))
    parsed = z.parse_smt2_string(be._to_smt2(formula), ctx=formula.ctx)
    assert len(parsed) == 1
    assert canonical.eq(canon_binders(z.simplify(parsed[0])))


def test_map_only_reference_with_missing_printer_declaration_is_rejected_safely():
    word = z.BitVecSort(8)
    function = z.Function("metadata_only_map_function", word, word)
    array = z.Array("metadata_only_map_array", word, word)
    # Z3's current raw printer omits function's declaration when it exists only in Map params.
    with pytest.raises(ValueError, match="SMT2 round trip"):
        be._to_smt2(z.Map(function, array) != array)


def test_quoted_names_are_conservatively_refused_and_regular_spaces_are_supported():
    word = z.BitVecSort(8)
    x = z.BitVec("quoted_transport_x", 8)
    with pytest.raises(ValueError, match="SMT2 round trip"):
        be._to_smt2(z.Function("|quoted_transport_function|", word, word)(x) != x)
    formula = z.Function("transport function with spaces", word, word)(x) != x
    assert answer(z.parse_smt2_string(be._to_smt2(formula))[0]) == answer(formula) == z.sat


def test_original_scalar_names_are_kept_without_a_new_context_or_solver_check(monkeypatch):
    word = z.BitVec("unchanged_scalar_name", 64)
    flag = z.Bool("unchanged_scalar_flag")
    formula = z.And(word == 3, flag)
    monkeypatch.setattr(z, "Context", lambda *a, **kw: pytest.fail("new Context"))
    monkeypatch.setattr(z.Solver, "check", lambda *a, **kw: pytest.fail("transport is not an SMT proof"))
    parsed = z.parse_smt2_string(be._to_smt2(formula), ctx=formula.ctx)[0]
    assert z.simplify(parsed).eq(z.simplify(formula))
    text = be._to_smt2(formula)
    assert "(declare-fun unchanged_scalar_name () (_ BitVec 64))" in text
    assert "(declare-fun unchanged_scalar_flag () Bool)" in text


def test_reserved_free_binder_prefix_is_refused_even_without_prior_capture():
    from verification.alpha_canon import PREFIX
    formula = z.BitVec(PREFIX+"1_0", 8) == 1
    with pytest.raises(ValueError, match="reserved binder prefix"):
        be._to_smt2(formula)


def test_full_gate_checks_the_complete_returned_assertion_conjunction(monkeypatch):
    function = z.Function("assertion_count_function", z.BoolSort(), z.BoolSort())
    formula = function(z.Bool("assertion_count_x"))
    monkeypatch.setattr(z, "parse_smt2_string", lambda *a, **kw: [z.BoolVal(True), z.BoolVal(True)])
    with pytest.raises(ValueError, match="normalized statement"):
        be._to_smt2(formula)
    left, right = z.Bools("split_assertion_left split_assertion_right")
    monkeypatch.setattr(z, "parse_smt2_string", lambda *a, **kw: [left, right])
    assert be._to_smt2(z.And(left, right))


def test_empty_parser_result_is_only_an_equivalent_empty_conjunction(monkeypatch):
    assert be._to_smt2(z.BoolVal(True))
    monkeypatch.setattr(z, "parse_smt2_string", lambda *a, **kw: [])
    assert be._to_smt2(z.BoolVal(True))
    with pytest.raises(ValueError, match="normalized statement"):
        be._to_smt2(z.BoolVal(False))
    with pytest.raises(ValueError, match="normalized statement"):
        be._to_smt2(z.Bool("nontrivial_assertion_not_True"))


def test_empty_true_transport_retains_an_existing_nondefault_context(monkeypatch):
    context = z.Context()
    formula = z.BoolVal(True, ctx=context)
    monkeypatch.setattr(z.Context, "__init__", lambda *a, **kw: pytest.fail("created a new Context"))
    assert be._to_smt2(formula)
