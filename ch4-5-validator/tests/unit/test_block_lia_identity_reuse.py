"""LIA join proof reuse; run with the isolated candidate first on sys.path."""
from pathlib import Path
import runpy

import pytest
import z3 as z

from common.store_forwarding import clear_memo
import verification.block_equivalence as be
from verification.linear_encoding import split_limb_joins


def _branch_obligation():
    # Reuse the existing real EVM / amd64 limb-order fixture, without copying it.
    fixture = Path(be.__file__).resolve().parents[1] / "tests/unit/test_block_div_pairing.py"
    return runpy.run_path(str(fixture))["_obligation"](full=False)[0]


def test_structural_join_avoids_raw_bitblast_and_records_actual_goal(monkeypatch):
    clear_memo()
    formula = _branch_obligation()
    observed, structural = {}, set()
    identity, solve = be._identity_proof, be.solve_query

    def prove(old, new, timeout_ms=1000):
        goal = z.Not(old == new).sexpr()
        proof = identity(old, new, timeout_ms)
        observed[goal] = proof
        if proof == () and be._concat_matches(old, new):
            structural.add(goal)
        return proof

    def no_raw_multiplier(query, timeout_ms):
        assert not be._nonlinear_mul_terms(query), "raw multiplier query reached the solver"
        return solve(query, timeout_ms)

    monkeypatch.setattr(be, "_identity_proof", prove)
    monkeypatch.setattr(be, "solve_query", no_raw_multiplier)
    prover = be.BlockEquivalenceProver([], [], {}, timeout_ms=30000)
    _, answer, lemmas = prover._retry_over_lia(formula)
    assert answer == "unsat"
    joins = [lemma for lemma in lemmas if lemma.name.startswith("join_")]
    assert joins and structural
    assert any(lemma.formula in structural for lemma in joins)
    for lemma in joins:
        assert lemma.formula in observed
        assert observed[lemma.formula] is not None
        assert lemma.lemmas == observed[lemma.formula]
        assert lemma.proved


def test_wrong_low_slice_is_not_proved_or_rewritten():
    clear_memo()
    x, y = z.BitVecs("join_bad_x join_bad_y", 64)
    limb = x * y + x
    low = z.simplify(z.Extract(7, 0, limb), bv_sort_ac=True)
    wrong = z.Concat(z.Extract(63, 8, limb), low + 1)
    formula = wrong != limb
    assert z.is_true(z.simplify(z.substitute(formula, (x, z.BitVecVal(0, 64)), (y, z.BitVecVal(0, 64)))))
    assert split_limb_joins(formula) == []
    assert not be._concat_matches(wrong, limb)
    assert be._identity_proof(wrong, limb, 1000) is None
    prover = be.BlockEquivalenceProver([], [], {}, timeout_ms=1000)
    unchanged, answer, lemmas = prover._retry_over_lia(formula)
    assert unchanged.eq(formula) and answer == "unknown" and lemmas == ()


def test_abort_is_observed_before_a_structural_join(monkeypatch):
    clear_memo()
    formula = _branch_obligation()
    candidates = split_limb_joins(z.simplify(formula, bv_sort_ac=True))
    assert candidates and any(be._concat_matches(old, new) for old, new in candidates)
    entered = []
    identity = be._identity_proof

    def prove(*args, **kwargs):
        entered.append(True)
        return identity(*args, **kwargs)

    def abort():
        raise be.ProofBudgetExceeded("injected node cancellation")

    monkeypatch.setattr(be, "_identity_proof", prove)
    monkeypatch.setattr(be, "check_abort", abort)
    prover = be.BlockEquivalenceProver([], [], {}, timeout_ms=1000)
    with pytest.raises(be.ProofBudgetExceeded, match="injected node cancellation"):
        prover._retry_over_lia(formula)
    assert entered == []
