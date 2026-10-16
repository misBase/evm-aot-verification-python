"""Permit2 1327: SAT checks over UFs applied to lambda arrays.

Z3's array theory is incomplete for an uninterpreted function applied to a
lambda, so model_domain_nonempty (host-gas oracle axioms over sha3_slice of a
memory window) was always unknown. sat_by_constant_array_ufs proves SAT with
a checked constant-function witness and never answers "unsat".
"""
from pathlib import Path

import pytest
from z3 import (And, Array, ArraySort, BitVec, BitVecSort, BitVecVal, Extract, Function, If, Lambda, Map, Select, ULE, ULT,
                parse_smt2_file)

import verification.block_equivalence as be

BV64, BV8, BV256 = BitVecSort(64), BitVecSort(8), BitVecSort(256)
M = Array("w_M", BV64, BV8)
i, x, n = BitVec("w_i", 64), BitVec("w_x", 64), BitVec("w_n", 64)
sha3 = Function("w_sha3_slice", ArraySort(BV64, BV8), BV256, BV256)
host_gas = Function("host_gas_sload", BV256, BV256, BitVecSort(64))
window = Lambda([i], Select(M, x + i))
shifted = Lambda([i], Select(M, x + i + 1))
entry = And(ULT(x, 1 << 40), ULT(n, 1 << 20))
axiom = ULE(host_gas(sha3(window, BitVecVal(32, 256)), BitVecVal(0, 256)), 2100)
MD1327 = Path(__file__).resolve().parents[2] / "cloud-inputs" / "permit2" / "md1327.smt2"


@pytest.fixture(autouse=True)
def _no_cache(monkeypatch):
    monkeypatch.delenv("BLOCK_PROOF_CACHE", raising=False)
    monkeypatch.delenv("BLOCK_PAIR_WORKERS", raising=False)


def _check_sat(formula, timeout_ms=5000):
    records = []
    ok = be.BlockEquivalenceProver([], [], {}, timeout_ms=timeout_ms)._check(
        "model_domain_nonempty", formula, records, expected="sat")
    return ok, records[-1]


def test_lambda_under_uf_is_unknown_to_the_direct_solver():
    # The incompleteness this route works around; if Z3 ever decides it, the
    # route is merely redundant.
    assert be.solve_query(And(entry, axiom), 2000) in ("unknown", "sat")


def test_witness_proves_oracle_axiom_over_lambda():
    assert be.sat_by_constant_array_ufs(And(entry, axiom), 5000) == "sat"
    ok, record = _check_sat(And(entry, axiom))
    assert ok and record.answer == "sat" and record.expected == "sat"


def test_witness_value_is_chosen_by_the_solver():
    # A constant function, not a fixed constant: sha3_slice must equal 7 here.
    formula = And(entry, axiom, sha3(window, BitVecVal(32, 256)) == 7)
    assert be.sat_by_constant_array_ufs(formula, 5000) == "sat"


def test_uf_under_lambda_binder_is_restricted():
    nested = Lambda([i], If(ULT(i, 32), Select(M, i), Extract(7, 0, sha3(window, BitVecVal(1, 256)))))
    formula = And(entry, ULE(host_gas(sha3(nested, BitVecVal(32, 256)), BitVecVal(0, 256)), 2100))
    assert [f.name() for f in be._array_argument_ufs(formula)] == ["w_sha3_slice"]
    assert be.sat_by_constant_array_ufs(formula, 5000) == "sat"


def test_needs_nonconstant_function_is_unknown_not_unsat():
    # Satisfiable, but not by a constant sha3_slice: the restriction is UNSAT,
    # which proves nothing about the formula.
    formula = And(entry, sha3(window, BitVecVal(32, 256)) != sha3(shifted, BitVecVal(32, 256)))
    assert be.sat_by_constant_array_ufs(formula, 5000) == "unknown"


def test_unsat_formula_is_never_sat():
    formula = And(entry, axiom, ULT(x, 0))
    assert be.sat_by_constant_array_ufs(formula, 5000) == "unknown"
    ok, record = _check_sat(formula)
    assert not ok and record.answer != "sat"


def test_no_array_ufs_returns_at_once():
    assert be._array_argument_ufs(entry) == []
    assert be.sat_by_constant_array_ufs(entry, 5000) == "unknown"
    ok, _ = _check_sat(entry)  # the direct query still decides it
    assert ok


def test_function_referenced_as_value_is_refused():
    # substitute_funs leaves Map(f, ...) alone, so f would survive in F' and
    # the substitution lemma would not apply: no witness is attempted.
    inc = Function("w_inc", BV8, BV8)
    formula = And(axiom, Map(inc, M) == M)
    assert be._array_argument_ufs(formula) is None
    assert be.sat_by_constant_array_ufs(formula, 5000) == "unknown"


def test_unsat_expected_checks_do_not_use_the_witness(monkeypatch):
    called = []
    monkeypatch.setattr(be, "sat_by_constant_array_ufs", lambda *a: called.append(a) or "sat")
    records = []
    be.BlockEquivalenceProver([], [], {}, timeout_ms=2000)._check("pair_0_0", And(entry, axiom), records)
    assert not called and not records[-1].proved


@pytest.mark.skipif(not MD1327.exists(), reason="captured Permit2 obligation not present")
def test_permit2_1327_model_domain_nonempty():
    formula = And(*parse_smt2_file(str(MD1327)))
    ok, record = _check_sat(formula, timeout_ms=30000)
    assert ok and record.answer == "sat"
    assert record.elapsed_seconds < 20
