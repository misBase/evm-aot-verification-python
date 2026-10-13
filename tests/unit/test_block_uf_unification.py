"""UF argument unification may only substitute equalities entailed by F."""
import pytest
from z3 import (And, BitVec, BitVecSort, BitVecVal, Function, BoolVal, If, Not, Solver, UGT, ULE, ULT, is_false, sat, unsat,
                simplify)

import verification.block_equivalence as be
from verification.block_equivalence import (BlockEquivalenceProver, Obligation, _refute_by_cases,
                                            abstract_nonlinear_mul, square_monotonicity,
                                            sweep_equalities, unify_uf_arguments)

S = BitVecSort(64)
h = Function("unify_h", S, S)


def answer(formula):
    solver = Solver()
    solver.set(timeout=3000)
    solver.add(formula)
    return solver.check()


# Deterministic budget for queries too heavy for answer()'s 3s wall clock.
# z3 4.15.4, unloaded: the 8-store offset-view rewrite check costs ~13-15M
# rlimit (2.5-3.3s), the second telescope identity 3-7M (1.8-5.5s); 200M leaves
# >10x margin and does not depend on machine load.
_RLIMIT = 200_000_000


def answer_rlimit(formula, rlimit=_RLIMIT):
    solver = Solver()
    solver.set(rlimit=rlimit)
    solver.add(formula)
    return solver.check()


def test_entailed_argument_equality_is_merged():
    c = BitVec("unify_c", 64)
    formula = And(c != 0, h(If(c == 0, 5, c + 1)) != h(c + 1))
    unified, lemmas = unify_uf_arguments(formula, 3000)
    assert lemmas and all(l.answer == "unsat" for l in lemmas)
    assert answer(unified) == unsat


def test_argument_containing_its_partner_terminates():
    # x86 recomputes words as f(w) with f(w) = w; replacing w by f(w) would loop.
    c = BitVec("unify_c", 64)
    unified, lemmas = unify_uf_arguments(h(c) != h(If(c == 0, 0, c)), 3000)
    assert 0 < len(lemmas) <= 2 and answer(unified) == unsat


def test_arguments_equal_only_in_some_models_are_not_merged():
    c, d = BitVec("unify_c", 64), BitVec("unify_d", 64)
    formula = And(ULT(c, 10), h(c) == 0, h(d) != 0)  # c = d is consistent but not entailed
    unified, lemmas = unify_uf_arguments(formula, 3000)
    assert lemmas == () and unified.eq(formula) and answer(unified) == sat
    records = []
    assert not BlockEquivalenceProver([], [], {}, timeout_ms=3000)._check("pair", formula, records)
    assert records[-1].answer == "sat" and records[-1].lemmas == ()


def test_opaque_uf_results_do_not_invent_argument_equalities():
    c, d = BitVec("unify_c", 64), BitVec("unify_d", 64)
    g = Function("unify_g", S, S)
    # g(c) = g(d) does not entail c = d (g need not be injective).
    formula = And(g(c) == g(d), h(c) != h(d))
    assert unify_uf_arguments(formula, 3000)[1] == ()
    assert answer(formula) == sat


def test_sweep_merges_only_entailed_equalities():
    c = BitVec("unify_c", 64)
    # Same values on every small fingerprint, but unequal once c >= 2^20.
    formula = And(h(c + 1) == 0, h((c & 0xFFFFF) + 1) != 0)
    swept, lemmas = sweep_equalities(formula, 3000)
    assert lemmas == () and answer(swept) == sat
    swept, lemmas = sweep_equalities(And(ULT(c, 100), formula), 3000)
    assert lemmas and answer(swept) == unsat


def test_case_split_requires_every_case():
    c = BitVec("unify_c", 64)
    assert _refute_by_cases(BoolVal(True), If(c == 0, 1, c) != c, 3000) is None
    assert _refute_by_cases(c != 0, If(c == 0, 1, c) != c, 3000)


def test_timeouts_never_become_proofs(monkeypatch):
    c = BitVec("unify_c", 64)
    formula = And(UGT(c, 1), h(If(c == 0, 5, c + 1)) != h(c + 1))  # c != 0 would decide the guard
    monkeypatch.setattr(be, "solve_query", lambda query, timeout: "unknown")
    monkeypatch.setattr(be, "solve_pure_bv", lambda query, timeout: "unknown")
    monkeypatch.setattr(be, "unsat_core", lambda assertions, goal, timeout: None)
    assert unify_uf_arguments(formula, 3000)[1] == ()
    records = []
    assert not BlockEquivalenceProver([], [], {}, timeout_ms=3000)._check("pair", formula, records)
    assert records[-1].answer == "unknown" and not records[-1].proved


def _unknown_unless_lemma(real, final):
    # Obligations mention unify_h; lemma queries only its arguments.
    def solve(query, timeout):
        if "unify_h" in query.sexpr() or (is_false(query) and final == "unknown"):
            return "unknown"
        return real(query, timeout)
    return solve


def test_prover_proves_through_unification_when_direct_query_is_unknown(monkeypatch):
    c = BitVec("unify_c", 64)
    formula = And(UGT(c, 1), h(If(c == 0, 5, c + 1)) != h(c + 1))
    monkeypatch.setattr(be, "solve_query", _unknown_unless_lemma(be.solve_query, "unsat"))
    monkeypatch.setattr(be, "solve_pure_bv", lambda query, timeout: "unknown")  # obligation-level route
    records = []
    assert BlockEquivalenceProver([], [], {}, timeout_ms=3000)._check("pair", formula, records)
    assert records[-1].proved and records[-1].lemmas


def test_final_query_unknown_keeps_obligation_open(monkeypatch):
    c = BitVec("unify_c", 64)
    formula = And(c != 0, h(If(c == 0, 5, c + 1)) != h(c + 1))
    # Lemmas are refuted for real, but the rewritten obligation times out.
    monkeypatch.setattr(be, "solve_query", _unknown_unless_lemma(be.solve_query, "unknown"))
    monkeypatch.setattr(be, "solve_pure_bv", lambda query, timeout: "unknown")
    monkeypatch.setattr(be, "is_false", lambda query: False)  # force the solver on the rewrite
    records = []
    assert not BlockEquivalenceProver([], [], {}, timeout_ms=3000)._check("pair", formula, records)
    assert records[-1].answer == "unknown" and records[-1].lemmas == ()


def test_unrefuted_lemma_invalidates_record():
    lemma = Obligation("unify_0_case_0", "(x)", "unknown")
    assert not Obligation("pair", "(false)", "unsat", lemmas=(lemma,)).proved


def test_square_monotonicity_axioms_hold_for_bvmul():
    from z3 import BitVecs, Not, Var, substitute_funs
    x, y = BitVecs("unify_x unify_y", 16)
    functions = {}
    relaxed, _ = abstract_nonlinear_mul(And(x * x != 0, y * y != 1), functions=functions)
    axioms = square_monotonicity(relaxed, functions)
    assert len(axioms) == 2
    (f,) = functions.values()
    for axiom in axioms:  # read the UF as bvmul again: every instance is valid
        exact = substitute_funs(axiom, (f, Var(0, BitVecSort(16)) * Var(1, BitVecSort(16))))
        assert answer(Not(exact)) == unsat


def test_equality_cache_never_transfers_to_a_weaker_premise():
    from z3 import And, BitVec
    from verification.block_equivalence import _prove_equal
    a, b, c = BitVec("ca", 8), BitVec("cb", 8), BitVec("cc", 8)
    cache = {}
    assert _prove_equal(And(a == b, c == 1), a, b, 2000, None, cache) is not None
    # Weaker premise (a == b dropped): the cached refutation must not apply.
    assert _prove_equal(And(c == 1, c != 2), a, b, 2000, None, cache) is None
    # Stronger premise reuses it.
    assert _prove_equal(And(a == b, c == 1, a != 3), a, b, 2000, None, cache) is not None


def test_unification_first_still_falls_back_to_mul_abstraction(monkeypatch):
    # Regression: Safe 588 pair_6_0 is provable only via the mul abstraction;
    # once a sibling needed unification that route must still run in full.
    c = BitVec("route_c", 64)
    formula = And(c != 0, c == 0)
    prover = BlockEquivalenceProver([], [], {}, timeout_ms=3000)
    prover._node_needed_unification = True
    monkeypatch.setattr(be, "solve_query", lambda query, timeout: "unknown")  # exact route never answers
    monkeypatch.setattr(be, "solve_pure_bv", lambda query, timeout: "unknown")
    calls = []
    monkeypatch.setattr(prover, "_retry_with_uf_unification", lambda f, a: (calls.append("unify"), (f, "unknown", ()))[1])
    monkeypatch.setattr(prover, "_retry_over_nonlinear_mul", lambda f, a, split=False: (calls.append("mul"), (f, "unsat", ()))[1])
    records = []
    assert prover._check("pair", formula, records)
    assert calls == ["unify", "mul"]


def test_unify_across_merges_only_under_shared_premise():
    from z3 import Function, BitVecSort, Solver, sat, unsat
    from verification.block_equivalence import unify_across
    g = Function("across_g", BitVecSort(8), BitVecSort(8))
    a, b, d = BitVec("across_a", 8), BitVec("across_b", 8), BitVec("across_d", 8)
    f1 = And(a == b, g(a) != g(b))
    f2 = And(a == b, d == 1, g(a) != g(b))
    out, lemmas = unify_across([f1, f2], 3000)
    assert lemmas
    for f in out:
        s = Solver(); s.add(f); assert s.check() == unsat
    # A sibling lacking a == b: common premise is empty, nothing may merge,
    # and the SAT sibling must stay SAT.
    f3 = And(d == 2, g(a) != g(b))
    out, lemmas = unify_across([f1, f3], 3000)
    assert not lemmas and out[1].eq(f3)
    s = Solver(); s.add(out[1]); assert s.check() == sat


# --- normalize_word_arith: memory word counts / gas comparisons made syntactic ---

def _mstore_gas_pair():
    """EVM OOG vs x86 pass on the MSTORE after CALLDATACOPY(fmp=128, 0, cds)."""
    from z3 import Extract, Not, ULE, ZeroExt
    cds, gas = BitVec("nw_cds", 64), BitVec("nw_gas", 64)
    w1, w2 = Extract(63, 5, 159 + cds), Extract(63, 5, 191 + cds)                # EVM word counts
    w1_x86 = Extract(63, 5, 31 + 32 * ZeroExt(5, Extract(63, 5, 159 + cds)))    # x86: words(32*words)
    def cost(w):
        z = ZeroExt(5, w)
        return 3 * z + ZeroExt(9, Extract(63, 9, z * z))
    copy = 3 * ZeroExt(5, Extract(63, 5, 31 + cds))
    avail_evm = gas - 189 - (cost(w1) - 9) - copy
    avail_x86 = gas - 180 - copy - cost(w1_x86)
    fee_x86 = cost(Extract(63, 5, 31 + 32 * ZeroExt(5, w2))) - cost(w1_x86)
    x86_ok = Not(Extract(64, 64, ZeroExt(1, avail_x86) + (2 ** 65 - 1) * ZeroExt(1, fee_x86)) == 1)
    premise = And(cds != 0, Extract(63, 37, 160 + cds) == 0, ULE(189, gas), ULE(cost(w1) - 9 + copy, gas - 189))
    return premise, x86_ok, Not(ULE(cost(w2) - cost(w1), avail_evm))


def test_word_rewrite_schemas_are_identities():
    from z3 import BitVecVal, Concat, Extract, Not, ZeroExt
    x, r = BitVec("nw_x", 64), BitVec("nw_r", 64)
    a, b = BitVec("nw_a", 64), BitVec("nw_b", 64)
    terms = [Extract(63, 5, 191 + r), Extract(63, 5, 31 + 32 * x + r), Extract(63, 5, 2 ** 64 - 1 + 96 * x),
             Extract(64, 64, ZeroExt(1, a) + (2 ** 65 - 1) * ZeroExt(1, b)) == 1,
             Extract(64, 64, ZeroExt(1, a) + ZeroExt(1, b)) == 0,
             Concat(Extract(63, 8, 128 + r), 128 + Extract(7, 0, r))]
    for t in terms:
        t = simplify(t)  # the prover only sees flattened sums
        new = be._word_rewrite(t)
        assert new is not None, t
        assert answer(Not(t == new)) == unsat, t   # valid for every value, not just in some model


def test_word_rewrite_rejects_non_identities():
    from z3 import Concat, Extract, ZeroExt
    r, a, b = BitVec("nw_r", 64), BitVec("nw_a", 65), BitVec("nw_b", 64)
    bad_concat = Concat(Extract(63, 8, 128 + r), 1 + Extract(7, 0, r))  # low byte is not (128 + r)[7:0]
    formula = be.normalize_word_arith(bad_concat == 0)[0]
    assert answer(formula != (bad_concat == 0)) == unsat                 # normalisation stays an equivalence
    assert be._word_rewrite(simplify(Extract(64, 64, a + ZeroExt(1, b)) == 1)) is None  # a may have its top bit set


def test_normalize_word_arith_refutes_mstore_gas_pair():
    premise, x86_ok, evm_oog = _mstore_gas_pair()
    formula = And(premise, x86_ok, evm_oog)
    normalized, lemmas = be.normalize_word_arith(formula)
    assert lemmas and all(l.answer == "unsat" for l in lemmas)
    # Word counts and gas sums become the same terms on both sides, so the
    # OOG/pass contradiction is syntactic: no square reasoning is needed.
    assert is_false(normalized)
    x86_words = be.normalize_word_arith(x86_ok)[0]
    evm_words = be.normalize_word_arith(evm_oog)[0]
    squares = lambda f: {t.sexpr() for t in be._nonlinear_mul_terms(f)}
    assert squares(x86_words) == squares(evm_words) and len(squares(evm_words)) == 2


def test_normalize_word_arith_keeps_satisfiable_pairs_satisfiable():
    from z3 import Not
    premise, x86_ok, evm_oog = _mstore_gas_pair()
    formula = And(premise, x86_ok, Not(evm_oog))                  # both sides pass: consistent
    normalized, _ = be.normalize_word_arith(formula)
    functions = {}
    abstract = abstract_nonlinear_mul(normalized, functions=functions)[0]
    assert _refute_by_cases(BoolVal(True), abstract, 5000) is None
    assert answer(normalized) != unsat


def test_prover_proves_mstore_gas_pair_through_normalized_route(monkeypatch):
    # Plain routes see different word-count terms; force them to fail so the
    # normalised route must carry the proof, and its rewrite proofs are recorded.
    premise, x86_ok, evm_oog = _mstore_gas_pair()
    formula = And(premise, x86_ok, evm_oog)
    prover = BlockEquivalenceProver([], [], {}, timeout_ms=5000)
    prover._node_needed_unification = False
    real = prover._retry_over_nonlinear_mul
    monkeypatch.setattr(prover, "_retry_over_nonlinear_mul",
                        lambda f, a, split=False: real(f, a, split) if split else (f, a, ()))
    monkeypatch.setattr(prover, "_retry_with_uf_unification", lambda f, a: (f, a, ()))
    monkeypatch.setattr(prover, "_retry_over_lia", lambda f: (f, "unknown", ()))  # LIA also proves it
    monkeypatch.setattr(be, "solve_query", lambda q, t, _real=be.solve_query: "unknown" if be._nonlinear_mul_terms(q) else _real(q, t))
    records = []
    assert prover._check("pair", formula, records)
    assert records[-1].proved and any(l.name.startswith("normalize_") for l in records[-1].lemmas)


def test_offset_view_select_reads_x86_memory_in_evm_offsets():
    # x86 memory is Lambda(a, M[a - R15]) under stores at R15 + offset; EVM reads M at the offset.
    from z3 import Array, BitVecSort, BitVecVal, Lambda, Not, Select, Store, Extract
    M = Array("ov_M", BitVecSort(64), BitVecSort(8))
    r15, f, v = BitVec("ov_r15", 64), BitVec("ov_f", 64), BitVec("ov_v", 8)
    a = BitVec("ov_a", 64)
    x86 = Store(Lambda([a], Select(M, a - r15)), r15 + f + 4, v)
    evm = Store(M, f + 4, v)
    read = simplify(Select(x86, r15 + 0x40), bv_sort_ac=True)
    new = be._offset_view_select(read)
    assert new is not None and answer(Not(read == new)) == unsat
    assert simplify(new, bv_sort_ac=True).eq(simplify(Select(evm, BitVecVal(0x40, 64)), bv_sort_ac=True))
    # A chain over some other base is left alone (fail-closed).
    assert be._offset_view_select(Select(Store(M, r15 + f, v), r15 + 0x40)) is None


def test_multi_part_concat_join_is_checked_slice_by_slice():
    from z3 import BitVecVal, Concat, Extract
    x, y = BitVec("cj_x", 64), BitVec("cj_y", 64)
    p = x * y
    good = simplify(Concat(BitVecVal(0, 64), Extract(63, 8, p), Extract(7, 0, p)))  # low byte pushed into a product
    new = be._word_rewrite(good)
    assert new is not None and be._identity_holds(good, new)
    bad = Concat(BitVecVal(0, 64), Extract(63, 8, p), Extract(7, 0, x))
    assert not be._identity_holds(bad, be._word_rewrite(bad))


def test_div_quotient_axioms_are_valid_and_guarded():
    from z3 import BitVecVal, Concat, Not, UDiv, ZeroExt
    x, y = BitVec("dq_x", 64), BitVec("dq_y", 64)
    q = UDiv(Concat(BitVecVal(0, 64), x), ZeroExt(64, y))
    (axiom,) = be.div_quotient_axioms([q == 0])
    assert answer_rlimit(Not(axiom)) == unsat
    assert be.div_quotient_axioms([UDiv(Concat(y, x), ZeroExt(64, y)) == 0]) == ()  # dividend may exceed 2^64


def test_mul_truncation_axioms_hold_for_bvmul():
    from z3 import Extract, Not, substitute
    x, y = BitVec("mt_x", 64), BitVec("mt_y", 64)
    f = simplify(And(x * y == 5, Extract(7, 0, x * y) == 3))   # the low byte is pushed to x[7:0]*y[7:0]
    functions = {}
    abstract, _ = abstract_nonlinear_mul(f, functions=functions)
    axioms = be.mul_truncation_axioms(abstract, functions)
    assert axioms and answer(And(abstract, *axioms)) == unsat   # abstract SAT without them
    concrete = [be.concretize_mul(a, functions) for a in axioms]
    assert all(answer(Not(c)) == unsat for c in concrete)


def test_generalized_products_prove_only_tautologies():
    from z3 import BitVecVal, Not, ULT
    x, y = BitVec("gp_x", 64), BitVec("gp_y", 64)
    p = BitVecVal(10**18, 64) * x
    tautology = (p == y) == And(Not(ULT(p, y)), Not(ULT(y, p)))
    g = be._generalize_products(tautology)
    assert be.solve_query(Not(g), 5000) == "unsat"
    not_valid = ULT(p, y)                                   # depends on the values
    assert be.solve_query(Not(be._generalize_products(not_valid)), 5000) == "sat"


def test_offset_view_identity_is_proved_by_generalisation():
    from z3 import Array, BitVecSort, Lambda, Select, Store
    M = Array("ovi_M", BitVecSort(64), BitVecSort(8))
    r15, p, a = BitVec("ovi_r15", 64), BitVec("ovi_p", 64), BitVec("ovi_a", 64)
    view = Lambda([a], Select(M, a - r15))
    x86 = view
    for k in range(32):                                   # 32 byte stores at r15 + p + k
        x86 = Store(x86, r15 + p + k, BitVec(f"ovi_v{k}", 8))
    q = BitVec("ovi_q", 64)
    old = simplify(Select(x86, r15 + q), bv_sort_ac=True)
    new = simplify(be._offset_view_select(old), bv_sort_ac=True)
    assert be._identity_holds(old, new, 1000)
    # A rewrite that is not the offset-view instance is rejected.
    wrong = simplify(Select(M, q + 1), bv_sort_ac=True)
    assert not be._offset_view_identity(old, wrong, 1000)


def _step_lemma_chain(prefix, address=lambda r15, p, k: r15 + p + k, index=lambda a, r15: a - r15):
    from z3 import Array, Lambda, Select, Store
    M = Array(f"{prefix}_M", BitVecSort(64), BitVecSort(8))
    r15, p, a, q = (BitVec(f"{prefix}_{n}", 64) for n in ("r15", "p", "a", "q"))
    x86 = Lambda([a], Select(M, index(a, r15)))
    for k in range(8):
        x86 = Store(x86, address(r15, p, k), BitVec(f"{prefix}_v{k}", 8))
    return M, p, q, simplify(Select(x86, r15 + q), bv_sort_ac=True)


def test_offset_view_step_lemma_proves_the_rewrite_without_per_read_queries(monkeypatch):
    M, p, q, old = _step_lemma_chain("sl")
    new = simplify(be._offset_view_select(old), bv_sort_ac=True)
    assert answer_rlimit(Not(old == new)) == unsat                # the rewrite is right
    monkeypatch.setattr(be, "_offset_view_identity", lambda *a: pytest.fail("per-read solver proof used"))
    proof = be._identity_proof(old, new)
    assert [l.name for l in proof] == ["offset_view_step_lemma"] and proof[0].answer == "unsat"
    from z3 import Array, parse_smt2_string
    decls = {f"ov_step_{n}": BitVec(f"ov_step_{n}", 64) for n in "boi"}
    decls.update(ov_step_v=BitVec("ov_step_v", 8), ov_step_Y=Array("ov_step_Y", BitVecSort(64), BitVecSort(8)))
    assert answer_rlimit(parse_smt2_string(f"(assert {proof[0].formula})", decls=decls)[0]) == unsat  # recorded lemma re-checked
    # The rewrite's normalisation record carries the lemma it rests on.
    _, lemmas = be.normalize_word_arith(old == 0)
    assert any(l.lemmas and l.lemmas[0].name == "offset_view_step_lemma" and l.proved for l in lemmas)


def test_offset_view_step_lemma_never_accepts_a_wrong_rewrite():
    from z3 import Select, Store
    M, p, q, old = _step_lemma_chain("sw")
    right = simplify(be._offset_view_select(old), bv_sort_ac=True)
    shifted = right.arg(0)
    wrong_read = simplify(Select(shifted, q + 1), bv_sort_ac=True)
    wrong_store = simplify(Select(Store(shifted.arg(0), p + 1, shifted.arg(2)), q), bv_sort_ac=True)
    for wrong in (wrong_read, wrong_store, simplify(Select(M, q), bv_sort_ac=True)):
        assert be._offset_view_by_step_lemma(old, wrong) is None
        assert not be._identity_holds(old, wrong)


def test_offset_view_step_lemma_falls_back_on_non_syntactic_steps(monkeypatch):
    calls = []
    real = be._offset_view_identity
    monkeypatch.setattr(be, "_offset_view_identity", lambda *a: calls.append(a) or real(*a))
    from z3 import Select
    # A store whose address is not base + offset (coefficient 2 on the base), and
    # a root that is not λa. M[a - base]: both leave the step-lemma path.
    M, _, q, nonlinear = _step_lemma_chain("sn", address=lambda r15, p, k: 2 * r15 + p + k)
    _, _, _, bad_root = _step_lemma_chain("sr", index=lambda a, r15: 2 * a - r15)
    for term in (nonlinear, bad_root):
        candidate = simplify(Select(M, q), bv_sort_ac=True)   # what a naive unshift would claim
        assert be._offset_view_by_step_lemma(term, candidate) is None
        calls.clear()
        assert not be._identity_holds(term, candidate) and calls  # fell back to the solver proof, still refused


def test_offset_view_step_lemma_is_not_cached_when_unproved(monkeypatch):
    monkeypatch.setattr(be, "_OFFSET_VIEW_STEP", {})
    monkeypatch.setattr(be, "solve_query", lambda formula, timeout_ms: "unknown")
    M, p, q, old = _step_lemma_chain("su")
    new = simplify(be._offset_view_select(old), bv_sort_ac=True)
    assert be._offset_view_by_step_lemma(old, new) is None and be._OFFSET_VIEW_STEP == {}


def _mstore_then_mload(x86_high_bytes):
    """abi_encode's mstore(pos, 32); len = mload(value) (CErc20 12930 shape).

    EVM: len is not uint64 (some of its top 24 bytes is nonzero), read in
    Z3-simplified form. x86: the top `x86_high_bytes` bytes of the same read
    are zero. With 24 the pair is UNSAT only through pos/value aliasing.
    """
    from z3 import Array, BitVecSort, BitVecVal, Concat, Extract, Not, Or, Select, Store
    M = Array("al_M", BitVecSort(64), BitVecSort(8))
    pos, value = BitVec("al_pos", 64), BitVec("al_value", 64)
    mem = M
    for j in range(32):
        mem = Store(mem, pos + j, BitVecVal(32 if j == 31 else 0, 8))
    word = Concat(*(Select(mem, value + i) for i in range(32)))
    evm = simplify(Not(And(*(Select(mem, value + i) == 0 for i in range(24)))), bv_sort_ac=True)
    x86 = Extract(255, 256 - 8 * x86_high_bytes, word) == 0
    return And(evm, x86), pos, value


def test_alias_split_refutes_mstore_then_mload():
    formula, _, _ = _mstore_then_mload(24)
    formula = simplify(formula, bv_sort_ac=True)
    _, _, offsets = be._alias_offsets(formula)
    assert len(offsets) == 32 + 24 - 1              # stores pos+0..31 meet reads value+0..23
    proofs = be._alias_split(formula, 5000)
    assert proofs is not None and all(p.proved for p in proofs)
    names = {p.name for p in proofs}
    assert {"alias_cover", "alias_apart", "alias_residual", "alias_case_0"} <= names
    assert len(names) == len(offsets) + 3


def test_alias_split_keeps_satisfiable_pairs_open():
    formula, _, _ = _mstore_then_mload(8)          # x86 checks only the top limb: SAT
    assert answer(formula) == sat
    assert be._alias_split(simplify(formula, bv_sort_ac=True), 5000) is None


def test_alias_split_rejects_an_unjustified_forwarding(monkeypatch):
    # A buggy forwarder that also skips the stores meeting at d0 = 0 (a case
    # the split no longer covers) is caught: its facts are satisfiable.
    formula, _, _ = _mstore_then_mload(24)
    formula = simplify(formula, bv_sort_ac=True)
    x, y, offsets = be._alias_offsets(formula)
    monkeypatch.setattr(be, "_alias_offsets", lambda f, extras=None: (x, y, [d for d in offsets if d != 0]))
    real = be._forward_apart
    monkeypatch.setattr(be, "_forward_apart", lambda f, a, b, offs, extras=(): real(f, a, b, [*offs, 0], extras))
    assert be._alias_split(formula, 5000) is None


def test_alias_split_needs_one_base_pair():
    from z3 import Array, BitVecSort, BitVecVal, Select, Store
    M = Array("al2_M", BitVecSort(64), BitVecSort(8))
    p, q, v = BitVec("al2_p", 64), BitVec("al2_q", 64), BitVec("al2_v", 64)
    two_pairs = Select(Store(Store(M, p, BitVecVal(1, 8)), q, BitVecVal(2, 8)), v) == 3
    assert be._alias_offsets(two_pairs) is None
    assert be._alias_offsets(Select(M, v) == 3) is None


def _residue_store(value):
    """x86 copy residue: one raw byte store at F + 5 + L below the stores at F + 0/1; read at w."""
    from z3 import Array, BitVecSort, BitVecVal, If, Select, Store
    M = Array("at_M", BitVecSort(64), BitVecSort(8))
    F, L, w = BitVec("at_F", 64), BitVec("at_L", 64), BitVec("at_w", 64)
    chain = Store(Store(Store(M, F + 5 + L, BitVecVal(7, 8)), F, BitVecVal(1, 8)), F + 1, BitVecVal(2, 8))
    expected = If(w == F, 1, If(w == F + 1, 2, If(w == F + 5 + L, value, Select(M, w))))
    return simplify(Select(chain, w) != expected, bv_sort_ac=True), w, F + 5 + L


def test_alias_split_cases_on_a_term_offset_store():
    formula, w, p = _residue_store(7)
    assert be._alias_offsets(formula) is None                     # outside the (F, w) pair
    extras = {}
    assert be._alias_offsets(formula, extras) is not None and [r.eq(w) for r, _ in extras.values()] == [True]
    proofs = be._alias_split(formula, 5000)
    assert proofs is not None and all(p.proved for p in proofs)
    assert {"alias_cover", "alias_term_0", "alias_apart", "alias_residual"} <= {p.name for p in proofs}


def test_alias_split_term_offset_keeps_a_wrong_byte_open():
    formula, _, _ = _residue_store(8)                             # w == F + 5 + L reads 7, not 8
    assert answer(formula) == sat
    assert be._alias_split(formula, 5000) is None


def test_alias_split_term_offset_needs_a_free_read_constant():
    from z3 import Array, BitVecSort, BitVecVal, Select, Store
    M = Array("at2_M", BitVecSort(64), BitVecSort(8))
    F, w = BitVec("at2_F", 64), BitVec("at2_w", 64)
    # the store address mentions the read constant: w := F + w is no substitution instance
    formula = Select(Store(Store(M, F, BitVecVal(1, 8)), F + w * w, BitVecVal(7, 8)), w) == 3
    assert be._alias_offsets(formula, {}) is None


def test_alias_split_hands_only_unknown_cases_to_the_fallback(monkeypatch):
    formula, _, _ = _mstore_then_mload(24)
    formula = simplify(formula, bv_sort_ac=True)
    seen = []
    monkeypatch.setattr(be, "solve_query", lambda q, t: "unknown")
    assert be._alias_split(formula, 5000, fallback=lambda q: seen.append(q)) is None and seen
    lemma = Obligation("inner", "true", "unsat")
    proofs = be._alias_split(formula, 5000, fallback=lambda q: (q, (lemma,)))
    assert proofs is not None and all(p.proved and p.lemmas == (lemma,) for p in proofs)
    monkeypatch.setattr(be, "solve_query", lambda q, t: "sat")    # a model is never retried
    assert be._alias_split(formula, 5000, fallback=lambda q: 1 / 0) is None


def test_power_of_two_times_zero_extension_becomes_a_shift():
    from z3 import BitVecVal, Concat, Not
    x = BitVec("rw_x", 59)
    t = simplify(BitVecVal(32, 64) * Concat(BitVecVal(0, 5), x))
    new = be._word_rewrite(t)
    assert new is not None and new.eq(Concat(x, BitVecVal(0, 5)))
    assert answer(Not(t == new)) == unsat
    # Only when the zero prefix is exactly k bits for 2^k (else it may overflow).
    y = BitVec("rw_y", 60)
    assert be._word_rewrite(simplify(BitVecVal(32, 64) * Concat(BitVecVal(0, 4), y))) is None


def test_restore_rewritten_conjuncts_only_readds_conjuncts_of_the_input():
    from z3 import Exists, UGE
    from verification.block_equivalence import restore_rewritten_conjuncts
    p, c = BitVec("restore_p", 64), BitVec("restore_c", 64)
    borrow_free, guarded = UGE(p, 160), If(c == 0, p, c) != 7
    quantified = Exists([c], p == c + 1)
    before = And(borrow_free, guarded, quantified, h(p) != 0)
    # A premise-justified merge rewrote the fact that justified it (self-erasure).
    after = And(BoolVal(True), quantified, h(p) != 0)
    restored = restore_rewritten_conjuncts(before, after)
    assert answer(And(before, Not(restored))) == unsat  # every model of the input survives
    kept = {x.get_id() for x in be._conjuncts(restored)}
    assert borrow_free.get_id() in kept  # the erased ite-free fact is back
    assert guarded.get_id() not in kept  # ite guards would only widen the case tree
    assert restore_rewritten_conjuncts(before, before).eq(before)
    # Nothing is invented: a satisfiable input stays satisfiable.
    assert answer(restore_rewritten_conjuncts(And(ULT(p, 5), p != 3), And(ULT(p, 5)))) == sat


def test_unify_route_survives_sweep_self_erasure(monkeypatch):
    # The sweep may rewrite the conjunct that justified its merge (Safe 9733:
    # the x86 borrow chain pos + 32 >= 160); the route must still see the fact.
    p = BitVec("restore_p", 64)
    fact = ULE(160, p)
    formula = And(fact, h(If(ULE(p, 160), BitVecVal(160, 64), p)) != h(p))
    lemma = Obligation("sweep_0_case_0", "", "unsat")
    monkeypatch.setattr(be, "unify_uf_arguments", lambda f, *a, **k: (f, ()))
    erase = lambda f, *a, **k: (And(*(c for c in be._conjuncts(f) if "unify_h" in str(c))), (lemma,))
    monkeypatch.setattr(be, "sweep_equalities", erase)
    prover = BlockEquivalenceProver([], [], {}, timeout_ms=3000)
    assert prover._retry_with_uf_unification(formula, "unknown")[1] == "unsat"
    # A formula whose fact does not force the merge must not become a proof.
    weak = And(ULE(150, p), h(If(ULE(p, 160), BitVecVal(160, 64), p)) != h(p))
    assert prover._retry_with_uf_unification(weak, "unknown")[1] == "unknown"


@pytest.mark.slow
def test_safe_9733_mcopy_gas_obligation_is_refuted():
    # x86 path 22 (OOG at the MCOPY gas check) implies EVM path 13's OOG
    # conjunct; unknown before restore_rewritten_conjuncts (sweep self-erasure).
    from pathlib import Path
    from z3 import parse_smt2_file
    path = Path(__file__).parents[1] / "data" / "block_obligations" / "safe9733_x86_maps_22_29.smt2"
    formula = be.normalize_word_arith(And(*parse_smt2_file(str(path))))[0]
    prover = BlockEquivalenceProver([], [], {}, timeout_ms=30000)
    proved, answer_, lemmas = prover._retry_with_uf_unification(formula, "unknown")
    assert answer_ == "unsat" and lemmas and all(l.answer == "unsat" for l in lemmas)


# --- memory-cost potential: telescoped memory-expansion charges ---

def _charges(sizes, m0):
    """Executor-shaped charges If(s <= m, 0, C(s) - C(m)); C(m) is carried as an ite of costs."""
    m, cost, out = m0, be._memory_cost(m0), []
    for s in sizes:
        fits = ULE(s, m)
        out.append(If(fits, BitVecVal(0, 64), be._memory_cost(s) - cost))
        m, cost = If(fits, m, s), If(fits, cost, be._memory_cost(s))
    return sum(out[1:], out[0])


def _expansion_pair(x86_sizes):
    """EVM expands once to max(a, b) + l (MCOPY); x86 to the sizes given. Words < 2^20."""
    a, b, l, m0, gas = (BitVec(f"pot_{n}", 64) for n in ("a", "b", "l", "m0", "gas"))
    bounds = And(*(ULT(v, 2 ** 20) for v in (a, b, l, m0)))
    evm = _charges([a, b, If(ULE(a, b), b, a) + l], m0)
    x86 = _charges(x86_sizes(a, b, l), m0)
    return And(bounds, ULE(x86, gas), Not(ULE(evm, gas)))


def test_telescope_step_is_an_identity():
    c, x, y, z = BitVec("ts_c", 64), BitVec("ts_x", 64), BitVec("ts_y", 64), BitVec("ts_z", 64)
    for t in (If(c == 1, BitVecVal(0, 64), x - y + 3 * z), If(ULE(c, x), x - 5 * y, BitVecVal(0, 64))):
        t = simplify(t)
        new = be._telescope_step(t)
        assert new is not None and answer_rlimit(Not(t == new)) == unsat
    assert be._telescope_step(simplify(If(c == 1, BitVecVal(0, 64), x + y))) is None  # nothing subtracted


def test_literal_branch_is_read_as_its_word_count():
    w, c = BitVec("lp_w", 64), BitVec("lp_c", 64) == 0
    p = be._potential(64)
    axioms = {}
    lifted = be._lift_potential(If(c, p(w), BitVecVal(9, 64)), axioms)
    assert lifted.eq(p(If(c, w, BitVecVal(3, 64))))                  # C(3) = 9 + 0
    (axiom,) = axioms.values()
    assert answer(Not(axiom == (p(BitVecVal(3, 64)) == 9))) == unsat
    assert be._lift_potential(If(c, p(w), BitVecVal(10, 64)), {}) is None  # 10 is no C(w)


def test_potential_route_refutes_charges_in_different_steps():
    # Same final msize, different intermediate expansions: equal totals only after telescoping.
    formula = _expansion_pair(lambda a, b, l: [a, b, a + l, b + l])
    prover = BlockEquivalenceProver([], [], {}, timeout_ms=10000)
    proved, answer_, lemmas = prover._retry_over_potential(formula)
    assert answer_ == "unsat" and lemmas and all(l.answer == "unsat" for l in lemmas)
    assert not be._nonlinear_mul_terms(proved)  # no square left (-P(m0) is linear)


def test_potential_route_keeps_a_differing_total_unproved():
    # x86 never expands to b + l: its total can be smaller, the pair is satisfiable.
    formula = _expansion_pair(lambda a, b, l: [a, b, a + l])
    a, b, l, m0, gas = (BitVec(f"pot_{n}", 64) for n in ("a", "b", "l", "m0", "gas"))
    witness = [(a, BitVecVal(0, 64)), (b, BitVecVal(64, 64)), (l, BitVecVal(64, 64)), (m0, BitVecVal(0, 64))]
    total = simplify(be.substitute(_charges([a, b, a + l], m0), *witness)).as_long()
    assert be.is_true(simplify(be.substitute(formula, *witness, (gas, BitVecVal(total, 64)))))
    prover = BlockEquivalenceProver([], [], {}, timeout_ms=5000)
    assert prover._retry_over_potential(formula)[1] == "unknown"


@pytest.mark.slow
def test_safe_11803_mcopy_gas_map_is_refuted_by_potential():
    # EVM charges MCOPY once to max(src, dst) + len, x86 to src + len and the
    # destination with the next store: every other route was unknown (900s node).
    from pathlib import Path
    from z3 import parse_smt2_file
    path = Path(__file__).parents[1] / "data" / "block_obligations" / "safe11803_x86_maps_0_0.smt2"
    formula = be.normalize_word_arith(And(*parse_smt2_file(str(path))))[0]
    prover = BlockEquivalenceProver([], [], {}, timeout_ms=30000)
    proved, answer_, lemmas = prover._retry_over_potential(formula)
    assert answer_ == "unsat" and lemmas and all(l.answer == "unsat" for l in lemmas)
