"""Division facts require a real generic theorem and a checked ground lift."""
from dataclasses import replace

import pytest
from z3 import (And, BitVec, BitVecSort, Context, Function, UDiv, URem, ZeroExt,
                Z3_OP_BUDIV, Z3_OP_BUDIV_I, simplify)

from verification import block_equivalence as be
from x86_64.summaries import div_identity as identity


@pytest.fixture(autouse=True)
def isolated_cache(monkeypatch):
    monkeypatch.setattr(identity, "_SELF_DIV_PROOFS", {})
    monkeypatch.delenv("BLOCK_PROOF_CACHE", raising=False)


def _division(ctx=None):
    x, y = BitVec("identity_x", 64, ctx=ctx), BitVec("identity_y", 64, ctx=ctx)
    return x, y, UDiv(ZeroExt(64, x), ZeroExt(64, y))


def test_real_generic_theorem_and_ground_lift_keep_every_dependency():
    x, y, term = _division()
    original = And(x == y, y != 0, term != 1)
    augmented, records = identity.with_division_identities(original, timeout_ms=30000)
    assert records and all(record.proved for record in records)
    [record] = records
    assert record.required_lemmas == tuple(child.name for child in record.lemmas)
    generic, lift = record.lemmas
    assert generic.provenance == "generic_division_identity"
    assert lift.provenance == "division_congruence_lift"
    assert not replace(record, lemmas=(generic,)).proved
    assert not replace(record, lemmas=(replace(generic, answer="unknown"), lift)).proved
    abstract, _ = be.abstract_divrem_congruence(augmented)
    assert be.solve_pure_bv(abstract, 1000) == "unsat"

    # The same cached theorem must leave division by zero in the input domain.
    zero = And(x == 0, y == 0, term != 1)
    augmented_zero, zero_records = identity.with_division_identities(zero, timeout_ms=2000)
    assert zero_records and all(record.proved for record in zero_records)
    abstract_zero, _ = be.abstract_divrem_congruence(augmented_zero)
    assert be.solve_pure_bv(abstract_zero, 1000) == "sat"


@pytest.mark.parametrize("case", ("high-bits", "signed", "remainder", "width64", "width256", "lookalike"))
def test_other_domains_and_operators_are_unchanged_without_a_solver(monkeypatch, case):
    x, y = BitVec("wrong_identity_x", 128), BitVec("wrong_identity_y", 128)
    low_x, low_y, unsigned = _division()
    terms = {
        "high-bits": UDiv(x, y),
        "signed": ZeroExt(64, low_x) / ZeroExt(64, low_y),
        "remainder": URem(ZeroExt(64, low_x), ZeroExt(64, low_y)),
        "width64": UDiv(low_x, low_y),
        "width256": UDiv(ZeroExt(192, low_x), ZeroExt(192, low_y)),
        "lookalike": Function("bvudiv_i", BitVecSort(128), BitVecSort(128), BitVecSort(128))(x, y),
    }

    def no_solver(*args, **kwargs):
        pytest.fail("an unsupported division domain reached the solver")

    monkeypatch.setattr(be, "solve_pure_bv", no_solver)
    query = terms[case] != 1
    unchanged, records = identity.with_division_identities(query, timeout_ms=1000)
    assert unchanged.eq(query) and not records and not identity._SELF_DIV_PROOFS


@pytest.mark.parametrize("failure", ("generic", "lift"))
def test_mock_unknown_never_adds_an_identity(monkeypatch, failure):
    calls = []

    def solve(*args):
        calls.append(args[1])
        return "unknown" if failure == "generic" or len(calls) > 1 else "unsat"

    monkeypatch.setattr(be, "solve_pure_bv", solve)
    query = _division()[2] != 1
    unchanged, records = identity.with_division_identities(query, timeout_ms=1000)
    assert unchanged.eq(query) and not records
    assert len(calls) == (1 if failure == "generic" else 2)
    assert all(0 < budget <= 1000 for budget in calls)


def test_mock_cache_separates_actual_operator_kind_and_context(monkeypatch):
    # This test checks cache routing only; the first test proves a real theorem.
    calls = []
    monkeypatch.setattr(be, "solve_pure_bv", lambda query, budget: calls.append(query) or "unsat")
    raw = _division()[2]
    internal = simplify(raw)
    assert {raw.decl().kind(), internal.decl().kind()} == {Z3_OP_BUDIV, Z3_OP_BUDIV_I}
    for term in (raw, internal, _division(Context())[2]):
        _, records = identity.with_division_identities(term != 1, timeout_ms=1000)
        assert records and records[0].proved
    assert len(identity._SELF_DIV_PROOFS) == 3
    assert len(calls) == 6  # separate generic + lift for each kind/context


def test_mock_forged_unproved_cache_entry_is_rejected(monkeypatch):
    monkeypatch.setattr(be, "solve_pure_bv", lambda *args: "unsat")
    term = _division()[2]
    identity.with_division_identities(term != 1, timeout_ms=1000)
    key = (term.ctx, term.decl().kind())
    value, theorem, proof = identity._SELF_DIV_PROOFS[key]
    identity._SELF_DIV_PROOFS[key] = (value, theorem, replace(proof, answer="unknown"))

    def no_solver(*args):
        pytest.fail("a forged unproved cache entry must be rejected")

    monkeypatch.setattr(be, "solve_pure_bv", no_solver)
    query = term != 1
    unchanged, records = identity.with_division_identities(query, timeout_ms=1000)
    assert unchanged.eq(query) and not records
