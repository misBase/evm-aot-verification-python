"""Task M (hard blocks): generic fixes.

- Lambda-aware normalisation (_normalize_lambdas): x86 hashes read memory
  through the R15 offset view inside sha3_slice lambdas, which the rounds of
  normalize_word_arith never entered (Permit2 1327 x86_maps_0_46).
- Identity unification (unify_identities): host-call arguments both sides
  build from the same values in different spellings are identities; one
  premise-free normalisation merges them (Aave Pool 8248 pair_0_1).
"""
from pathlib import Path

import pytest
from z3 import (And, Array, ArraySort, BitVec, BitVecSort, BitVecVal, Concat, Extract, Function, If, Lambda, Not, Select,
                Store, ULE, is_false, parse_smt2_file, simplify)

import verification.block_equivalence as be

SMT2 = Path(__file__).resolve().parents[2] / "cloud-inputs" / "m" / "smt2"
BV8, BV64, BV256 = BitVecSort(8), BitVecSort(64), BitVecSort(256)


@pytest.fixture(autouse=True)
def _no_cache(monkeypatch):
    monkeypatch.delenv("BLOCK_PROOF_CACHE", raising=False)
    monkeypatch.delenv("BLOCK_PAIR_WORKERS", raising=False)


# --- lambda bodies -------------------------------------------------------------


def _hashes(prefix, x86_offset=0):
    """The same 4-byte hash input read as EVM does (M at p + i) and as x86 does
    (stores at R15 + p + k over the view λa. M[a - R15], read at R15 + p + i)."""
    M = Array(f"{prefix}_M", BV64, BV8)
    r15, p, n = (BitVec(f"{prefix}_{s}", 64) for s in ("r15", "p", "n"))
    a, i, j = (BitVec(f"{prefix}_{s}", 64) for s in ("a", "i", "j"))
    vs = [BitVec(f"{prefix}_v{k}", 8) for k in range(4)]
    x86, evm = Lambda([a], Select(M, a - r15)), M
    for k, v in enumerate(vs):
        x86, evm = Store(x86, r15 + p + k + x86_offset, v), Store(evm, p + k, v)
    h = Function(f"{prefix}_sha3", ArraySort(BV64, BV8), BV64, BV256)
    zero = BitVecVal(0, 8)
    return (h(Lambda([i], If(ULE(n, i), zero, Select(x86, r15 + p + i))), n),
            h(Lambda([j], If(ULE(n, j), zero, Select(evm, p + j))), n), h)


def test_lambda_bodies_are_normalised():
    x86, evm, _ = _hashes("ln")
    formula, lemmas = be.normalize_word_arith(x86 != evm)
    assert is_false(simplify(formula))                     # both hash inputs are now one term
    assert any(l.name.endswith("_lambda") for l in lemmas) and all(l.proved for l in lemmas)


def test_without_the_lambda_pass_the_hashes_stay_apart(monkeypatch):
    x86, evm, _ = _hashes("lo")
    monkeypatch.setattr(be, "_normalize_lambdas", lambda f, lemmas, deadline=None: f)
    formula, _ = be.normalize_word_arith(x86 != evm)
    assert not is_false(simplify(formula))


def test_nested_lambdas_are_normalised_with_their_body():
    # Level 2 hashes level 1's value (as Permit2 1327's sha3 chain): the inner lambda sits in
    # the outer one's body and is normalised there.
    x86, evm, h = _hashes("nl")
    i, n = BitVec("nl_i2", 64), BitVec("nl_n", 64)
    outer = lambda inner: h(Lambda([i], If(i == 0, Extract(7, 0, inner), BitVecVal(0, 8))), n)
    formula, lemmas = be.normalize_word_arith(outer(x86) != outer(evm))
    assert is_false(simplify(formula)) and all(l.proved for l in lemmas)


def test_different_hash_inputs_are_not_merged():
    x86, _, _ = _hashes("nd", x86_offset=1)                # x86 stores one byte higher: another input
    _, evm, _ = _hashes("nd")
    formula, lemmas = be.normalize_word_arith(x86 != evm)
    assert not is_false(simplify(formula)) and be.solve_query(formula, 5000) != "unsat"
    assert all(l.proved for l in lemmas)


def test_lambda_rewrite_needs_the_inner_proofs(monkeypatch):
    # Fail-closed: when no inner rewrite is proved, the lambda keeps its x86 form.
    x86, evm, _ = _hashes("lp")
    monkeypatch.setattr(be, "_identity_proof", lambda old, new, timeout_ms=1000: None)
    formula, _ = be.normalize_word_arith(x86 != evm)
    assert not is_false(simplify(formula))


@pytest.mark.skipif(not (SMT2 / "permit2_1327_x86_maps_0_46.smt2").exists(), reason="fixture missing")
def test_permit2_1327_x86_maps_0_46_blasted_normal_form():
    formula = And(*parse_smt2_file(str(SMT2 / "permit2_1327_x86_maps_0_46.smt2")))
    formula, _ = be.skolemize_array_disequalities(formula)
    normalized, lemmas = be.normalize_word_arith(formula)
    assert all(l.proved for l in lemmas)
    assert be.solve_query(simplify(normalized, blast_select_store=True), 30000) == "unsat"


# --- identity unification -------------------------------------------------------


def _byte_split(prefix):
    """x86's sum with its low byte summed separately, and EVM's word sum."""
    a, b = BitVec(f"{prefix}_a", 64), BitVec(f"{prefix}_b", 64)
    return Concat(Extract(63, 8, a + b), Extract(7, 0, a) + Extract(7, 0, b)), a + b


def test_identity_arguments_are_merged():
    x86, evm = _byte_split("ui")
    f = Function("ui_call", BV64, BV256)
    formula = And(f(x86) == 0, f(evm) != 0)                # one call failed, the other succeeded
    assert not x86.eq(evm)
    (merged,), lemmas = be.unify_identities([formula])
    assert is_false(simplify(merged))
    assert len(lemmas) == 1 and lemmas[0].name == "unify_identities_1" and lemmas[0].proved


def test_premise_equalities_are_not_identities():
    a, b = BitVec("up_a", 64), BitVec("up_b", 64)
    f = Function("up_call", BV64, BV256)
    formula = And(a == b, f(a) == 0, f(b) != 0)             # equal only under the premise
    (merged,), lemmas = be.unify_identities([formula])
    assert merged.eq(formula) and lemmas == ()


def test_only_identity_pairs_are_merged():
    x86, evm = _byte_split("um")
    c, d = BitVec("um_c", 64), BitVec("um_d", 64)
    f = Function("um_call", BV64, BV64, BV256)
    formula = And(f(x86, c) == 0, f(evm, d) != 0)
    (merged,), lemmas = be.unify_identities([formula])
    assert len(lemmas) == 1 and be.solve_query(merged, 5000) == "sat"   # c, d still differ
    assert be.solve_query(And(merged, c == d), 5000) == "unsat"         # the merged argument agrees


def test_node_unification_rewrites_every_sibling():
    x86, evm = _byte_split("un")
    f = Function("un_call", BV64, BV256)
    g = BitVec("un_g", 256)
    pairs = [("pair_0_1", And(f(x86) == 0, f(evm) != 0), ""), ("pair_0_2", And(f(x86) == g, f(evm) != g), "")]
    prover = be.BlockEquivalenceProver([], [], {}, timeout_ms=3000)
    out, lemmas, rewritten = prover._unify_node(pairs)
    assert rewritten == {"pair_0_1", "pair_0_2"} and lemmas[0].name.startswith("unify_identities_")
    assert all(is_false(simplify(f)) for _, f, _ in out)


def test_unification_route_uses_identities():
    x86, evm = _byte_split("ur")
    f = Function("ur_call", BV64, BV256)
    prover = be.BlockEquivalenceProver([], [], {}, timeout_ms=3000)
    proved, answer, lemmas = prover._retry_with_uf_unification(And(f(x86) == 0, f(evm) != 0), "unknown")
    assert answer == "unsat" and lemmas[0].name.startswith("unify_identities_") and all(l.proved for l in lemmas)


@pytest.mark.slow
@pytest.mark.skipif(not (SMT2 / "aave_8248_pair_0_1.smt2").exists(), reason="fixture missing")
def test_aave_8248_pair_0_1_by_identities():
    formula = And(*parse_smt2_file(str(SMT2 / "aave_8248_pair_0_1.smt2")))
    prover = be.BlockEquivalenceProver([], [], {}, timeout_ms=30000)
    out, lemmas, rewritten = prover._unify_node([("pair_0_1", formula, "")])
    assert rewritten == {"pair_0_1"} and all(l.proved for l in lemmas)
    records = []
    assert prover._check("pair_0_1", out[0][1], records) and records[-1].proved
