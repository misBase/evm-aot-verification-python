from z3 import And, BitVec, ULT

import verification.block_equivalence as be
from verification import proof_cache


def _fresh_connections():
    proof_cache._CONNECTIONS.clear()


def test_decided_answer_is_reused_without_solving(tmp_path, monkeypatch):
    monkeypatch.setenv("BLOCK_PROOF_CACHE", str(tmp_path / "cache.sqlite"))
    _fresh_connections()
    x = BitVec("pc_x", 8)
    formula = And(ULT(x, 4), x == 9)
    assert be.solve_query(formula, 5000) == "unsat"
    _fresh_connections()  # as a later run / another process would
    monkeypatch.setattr(be, "_solve_query", lambda f, t: (_ for _ in ()).throw(AssertionError("solved again")))
    assert be.solve_query(formula, 5000) == "unsat"


def test_unknown_skips_only_budgets_it_already_tried(tmp_path, monkeypatch):
    monkeypatch.setenv("BLOCK_PROOF_CACHE", str(tmp_path / "cache.sqlite"))
    _fresh_connections()
    x = BitVec("pc_u", 8)
    formula = x == 1
    calls = []
    monkeypatch.setattr(be, "_solve_query", lambda f, t: calls.append(t) or "unknown")
    assert be.solve_query(formula, 5000) == "unknown"
    assert be.solve_query(formula, 3000) == "unknown" and calls == [5000]  # same wait skipped
    monkeypatch.setattr(be, "_solve_query", lambda f, t: calls.append(t) or "sat")
    assert be.solve_query(formula, 9000) == "sat" and calls == [5000, 9000]  # more budget: solved
    assert be.solve_query(formula, 1000) == "sat"  # decided answer replaced the unknown record


def test_same_text_different_sorts_do_not_collide():
    a8, b8 = BitVec("pc_a", 8), BitVec("pc_b", 8)
    a64, b64 = BitVec("pc_a", 64), BitVec("pc_b", 64)
    assert str(a8 == b8) == str(a64 == b64)
    assert proof_cache.query_key("check", a8 == b8) != proof_cache.query_key("check", a64 == b64)


def test_unsat_core_is_cached(tmp_path, monkeypatch):
    monkeypatch.setenv("BLOCK_PROOF_CACHE", str(tmp_path / "cache.sqlite"))
    _fresh_connections()
    x = BitVec("pc_c", 8)
    parts = [ULT(x, 4), x != 7, x == x]
    core = be.unsat_core(parts, x == 9, 5000)
    assert core == [0]
    _fresh_connections()
    monkeypatch.setattr(be, "_unsat_core", lambda *a: (_ for _ in ()).throw(AssertionError("solved again")))
    assert be.unsat_core(parts, x == 9, 5000) == [0]


def test_alpha_renamed_query_hits_without_solving(tmp_path, monkeypatch):
    # Same obligation from two call sites: only the havoc prefix / slot numbering differ.
    monkeypatch.setenv("BLOCK_PROOF_CACHE", str(tmp_path / "cache.sqlite"))
    _fresh_connections()
    a, b = BitVec("block17_stack_9", 8), BitVec("block18_stack_11", 8)
    assert be.solve_query(And(ULT(a, 4), a == 9), 5000) == "unsat"
    _fresh_connections()
    monkeypatch.setattr(be, "_solve_query", lambda f, t: (_ for _ in ()).throw(AssertionError("solved again")))
    assert be.solve_query(And(ULT(b, 4), b == 9), 5000) == "unsat"


def test_renaming_is_injective():
    # x, y distinct vs the same symbol twice: satisfiable vs not, so never one key.
    from z3 import Bool, Function, BitVecSort, BoolSort, Not
    p = Function("pc_p", BitVecSort(8), BoolSort())
    x, y = BitVec("pc_x", 8), BitVec("pc_y", 8)
    assert proof_cache.query_key("check", And(p(x), Not(p(y))))[0] != \
        proof_cache.query_key("check", And(p(x), Not(p(x))))[0]
    assert proof_cache.query_key("check", Bool("pc_q"))[0] == proof_cache.query_key("check", Bool("pc_r"))[0]


def test_answers_under_the_exact_key_stay_readable(tmp_path, monkeypatch):
    monkeypatch.setenv("BLOCK_PROOF_CACHE", str(tmp_path / "cache.sqlite"))
    _fresh_connections()
    x = BitVec("pc_old", 8)
    alpha, exact = proof_cache.query_key("check", x == 1)
    proof_cache.store(exact, "sat")  # as written by a run before alpha keys
    assert proof_cache.lookup((alpha, exact)) == "sat"


def test_alpha_key_ignores_let_layout_but_not_structure():
    # Same term shared twice vs written out twice: one AST, one key; a genuinely
    # different sum (x+y vs x+x) must not collide.
    from z3 import BitVecVal
    x, y = BitVec("pc_s", 8), BitVec("pc_t", 8)
    t = x * BitVecVal(3, 8) + y
    assert proof_cache.query_key("check", And(t == 1, t != 2))[0] == \
        proof_cache.query_key("check", And(x * BitVecVal(3, 8) + y == 1, x * BitVecVal(3, 8) + y != 2))[0]
    assert proof_cache.query_key("check", x + y == 1)[0] != proof_cache.query_key("check", x + x == 1)[0]


def test_indexed_operators_keep_their_indices():
    # The C decl string of extract omits (hi, lo): two different slices must not collide.
    from z3 import Extract
    x = BitVec("pc_w", 64)
    assert proof_cache.query_key("check", Extract(7, 0, x) == 1)[0] != \
        proof_cache.query_key("check", Extract(15, 8, x) == 1)[0]


def test_bound_variable_names_do_not_matter():
    from z3 import ForAll
    a, b, i = BitVec("pc_i", 8), BitVec("pc_j", 8), BitVec("pc_k", 8)
    assert proof_cache.query_key("check", ForAll([a], ULT(a, i)))[0] == \
        proof_cache.query_key("check", ForAll([b], ULT(b, i)))[0]


def test_disabled_without_env(monkeypatch):
    monkeypatch.delenv("BLOCK_PROOF_CACHE", raising=False)
    assert not proof_cache.enabled()
    assert proof_cache.lookup("anything") is None
