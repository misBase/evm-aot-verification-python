"""Declaration parameters share the UF alpha namespace with ordinary apps."""
from hashlib import sha256

import pytest
import z3 as z

import verification.block_equivalence as be
from verification import proof_cache as pc


# Frozen pre-v3 digests of the exact alias_review_* counterexamples. They are
# independent of the currently tested encoder; only the outer Z3 version varies.
V2 = {
    "map": ("61fa70ee669c336d02dc908f4dae68bce1a7816482d3615f53d8d6ebcbca05d8",
            "91a34933143c441dbad43c8cfb91c606e4d01bbd24a6ba637c634dc4ffaa6899"),
    "asarray": ("d7cebb5b64c8f87b9378d93c1e9703b317adcdbacb5e56a64c00111d3061d2ce",
                "a0f4991a67344cf09b7b6e56eaed795003d3ecd26e723e2891e55948534e6fae"),
}


def as_array(function):
    return z.ArrayRef(z.Z3_mk_as_array(function.ctx_ref(), function.ast), function.ctx)


def queries(mode, prefix="alias_review"):
    word = z.BitVecSort(8)
    array, index = z.Array(prefix + "_A", word, word), z.BitVec(prefix + "_i", 8)
    f, g = z.Function(prefix + "_f", word, word), z.Function(prefix + "_g", word, word)
    source = z.Map(f, array) if mode == "map" else as_array(f)
    argument = z.Select(array, index) if mode == "map" else index
    return z.Select(source, index) != f(argument), z.Select(source, index) != g(argument)


def direct(formula):
    solver = z.Solver(); solver.set(timeout=1000); solver.add(formula)
    return str(solver.check())


@pytest.fixture(autouse=True)
def clean_cache_env(monkeypatch):
    monkeypatch.delenv("BLOCK_PROOF_CACHE", raising=False)


@pytest.mark.parametrize("mode", ["map", "asarray"])
def test_same_and_different_parameter_functions_cannot_share_an_answer(tmp_path, monkeypatch, mode):
    same, different = queries(mode)
    assert direct(same) == "unsat" and direct(different) == "sat"
    assert pc.query_key("check", same) != pc.query_key("check", different)
    monkeypatch.setenv("BLOCK_PROOF_CACHE", str(tmp_path / "answers.sqlite"))
    assert be.solve_query(same, 1000) == "unsat"
    assert be.solve_query(different, 1000) == "sat"
    assert pc.cached_answer(pc.query_key("check", different), 1000) == "sat"


@pytest.mark.parametrize("mode", ["map", "asarray"])
@pytest.mark.parametrize("different", [False, True])
def test_consistent_renaming_keeps_a_real_cache_hit(tmp_path, monkeypatch, mode, different):
    left = queries(mode, "parameter_left")[different]
    right = queries(mode, "parameter_right")[different]
    assert pc.query_key("check", left) == pc.query_key("check", right)
    monkeypatch.setenv("BLOCK_PROOF_CACHE", str(tmp_path / "renamed.sqlite"))
    expected = "sat" if different else "unsat"
    assert be.solve_query(left, 1000) == expected
    monkeypatch.setattr(be, "_solve_query", lambda *a: pytest.fail("an alpha-identical query was solved again"))
    assert be.solve_query(right, 1000) == expected


@pytest.mark.parametrize("mode", ["map", "asarray"])
def test_v2_wrong_query_core_and_statement_entries_are_never_read(tmp_path, monkeypatch, mode):
    same, different = queries(mode)
    old_query = sha256(f"{z.get_version_string()}\0check\0transport-v2\0alpha\0{V2[mode][0]}".encode()).hexdigest()
    old_core = sha256(f"{z.get_version_string()}\0core\0transport-v2\0alpha\0{V2[mode][1]}".encode()).hexdigest()
    labels = (("alias", "unsat"),)
    old_statement = sha256(f"{z.get_version_string()}\0transport-v2\0lemma\0decl_alias\0{labels!r}\0{V2[mode][0]}".encode()).hexdigest()
    monkeypatch.setenv("BLOCK_PROOF_CACHE", str(tmp_path / "v2.sqlite"))
    pc.store(old_query, "unsat"); pc.store(old_core, []); pc.record_lemma(old_statement)
    assert pc.query_key("check", different) != (old_query,)
    assert be.solve_query(different, 1000) == "sat"
    outcome = {}
    assert be.unsat_core([different], z.BoolVal(True), 1000, outcome) is None
    assert outcome["answer"] == "sat"
    key = pc.statement_key("decl_alias", [("alias", "unsat", different)])
    assert key != old_statement and not pc.lemma_proved(key)
    assert pc.lookup(old_query) == "unsat"  # old evidence retained, not trusted


def test_cross_position_and_cross_statement_aliases_remain_distinct(tmp_path, monkeypatch):
    word = z.BitVecSort(8); array = z.Array("cross_A", word, word); i = z.BitVec("cross_i", 8)
    f, g = z.Function("cross_f", word, word), z.Function("cross_g", word, word)
    a, b, value = z.Select(z.Map(f, array), i), z.Select(z.Map(g, array), i), z.Select(array, i)
    valid = (a != f(value), b != g(value))
    invalid = (a != g(value), b != f(value))
    assert direct(z.And(*valid)) == "unsat" and direct(z.And(*invalid)) == "sat"
    assert pc.query_key("check", *valid) != pc.query_key("check", *invalid)
    yes = pc.statement_key("two", [(str(n), "unsat", q) for n, q in enumerate(valid)])
    no = pc.statement_key("two", [(str(n), "unsat", q) for n, q in enumerate(invalid)])
    assert yes != no
    monkeypatch.setenv("BLOCK_PROOF_CACHE", str(tmp_path / "lemmas.sqlite"))
    pc.record_lemma(yes)
    assert pc.lemma_proved(yes) and not pc.lemma_proved(no)


def test_decl_parameters_can_refer_to_builtins_without_becoming_ufs():
    word = z.BitVecSort(8); array = z.Array("builtin_map_A", word, word); i = z.BitVec("builtin_map_i", 8)
    function = z.Function("builtin_map_user", word, word)
    negate = (-i).decl()
    native = z.Select(z.Map(negate, array), i) != -z.Select(array, i)
    arbitrary = z.Select(z.Map(function, array), i) != -z.Select(array, i)
    assert direct(native) == "unsat" and direct(arbitrary) == "sat"
    assert pc.query_key("check", native) != pc.query_key("check", arbitrary)


def test_parameter_function_signatures_and_quantifier_sorts_are_complete():
    keys = []
    for width in (8, 16):
        word = z.BitVecSort(width); i = z.Const("typed_bound", word)
        f = z.Function("typed_function", word, word)
        query = z.ForAll([i], z.Select(as_array(f), i) == f(i))
        keys.append(pc.query_key("check", query))
        j = z.Const("renamed_bound", word); g = z.Function("renamed_function", word, word)
        assert keys[-1] == pc.query_key("check", z.ForAll([j], z.Select(as_array(g), j) == g(j)))
    assert keys[0] != keys[1]
    assert pc.alpha_digest([z.Bool("typed_constant")]) != pc.alpha_digest([z.BitVec("typed_constant", 1)])


def test_array_domain_and_range_sorts_and_constant_array_parameters():
    a = z.Array("sort_array", z.BitVecSort(8), z.BitVecSort(16))
    b = z.Array("sort_array", z.BitVecSort(16), z.BitVecSort(8))
    assert pc.alpha_digest([a]) != pc.alpha_digest([b])
    i = z.BitVec("constant_array_index", 8)
    assert pc.query_key("check", z.Select(z.K(i.sort(), z.BitVecVal(0, 8)), i) == 0) != \
        pc.query_key("check", z.Select(z.K(i.sort(), z.BitVecVal(1, 8)), i) == 0)


@pytest.mark.parametrize("left,right", [(z.BoolVal(True), z.BoolVal(False)),
    (z.BitVecVal(0, 8), z.BitVecVal(1, 8)), (z.IntVal(-1), z.IntVal(1)),
    (z.RealVal("1/2"), z.RealVal("2/3"))])
def test_values_keep_their_value_not_just_their_declaration(left, right):
    assert pc.alpha_digest([left]) != pc.alpha_digest([right])
    assert pc.alpha_digest([left]) == pc.alpha_digest([left])


def test_extract_indices_are_not_replaced_by_operator_name_only():
    x = z.BitVec("parameter_extract", 16)
    assert pc.query_key("check", z.Extract(7, 0, x) == 0) != pc.query_key("check", z.Extract(15, 8, x) == 0)


def test_unknown_parameters_skip_all_cache_callers(monkeypatch, tmp_path):
    x = z.BitVec("unknown_parameter", 16); query = z.Extract(7, 0, x) == 0
    with monkeypatch.context() as mp:
        mp.setattr(pc.C, "Z3_get_decl_parameter_kind", lambda *a: 999999)
        assert pc.query_key("check", query) is None
        assert pc.statement_key("unsupported", [("lemma", "unsat", query)]) is None
    monkeypatch.setenv("BLOCK_PROOF_CACHE", str(tmp_path / "none.sqlite"))
    assert pc.lookup(None) is None
    pc.record_answer(None, "unsat", 1000); pc.record_lemma(None); pc.store(None, "unsat")
    assert not pc.lemma_proved(None)


def test_unrepresented_sort_definitions_use_the_original_solver_without_caching(tmp_path, monkeypatch):
    datatype = z.Datatype("uncached_sort_definition"); datatype.declare("only_constructor"); datatype = datatype.create()
    query = z.Const("uncached_sort_value", datatype) != datatype.only_constructor
    assert pc.query_key("check", query) is None
    assert pc.statement_key("datatype", [("root", "unsat", query)]) is None
    monkeypatch.setenv("BLOCK_PROOF_CACHE", str(tmp_path / "unsupported-sort.sqlite"))
    assert be.solve_query(query, 1000) == "unsat"
    assert pc.lookup(pc.query_key("check", query)) is None
    outcome = {}
    assert be.unsat_core([query], z.BoolVal(True), 1000, outcome) == [0]
    assert outcome["answer"] == "unsat"
    assert not pc.lemma_proved(pc.statement_key("datatype", [("root", "unsat", query)]))


def test_uncacheable_primary_key_still_checks_the_whole_pure_bv_query(tmp_path, monkeypatch):
    monkeypatch.setenv("BLOCK_PROOF_CACHE", str(tmp_path / "uncacheable.sqlite"))
    def unsupported(*args):
        raise pc._UnsupportedAlpha("diagnostic unsupported metadata")
    monkeypatch.setattr(pc, "alpha_digest", unsupported)
    x = z.BitVec("uncached_bv_value", 8)
    assert pc.query_key("bv_abstraction", x == 3) is None
    assert be.solve_pure_bv(z.And(x == 3, x != 3), 1000) == "unsat"
    assert be.solve_pure_bv(x == 3, 1000) == "sat"
