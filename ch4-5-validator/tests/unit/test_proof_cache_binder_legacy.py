"""Correct legacy answers must not transfer through a shadowed SMT-text collision."""
from hashlib import sha256

import pytest
from z3 import And, Select, Solver, get_version_string, substitute

from tests.unit.test_block_alpha_canon import OWN_ONLY, SHADOW_REF, f
from tests.unit.test_isolated_binder_serialization import answer, shadowed_sat
import verification.block_equivalence as be
from verification import proof_cache as pc
from verification.alpha_canon import binder_capture_risk, canon_binders


def legacy_key(kind, formula):
    solver = Solver()
    solver.add(formula)
    text = pc.canonical_names(solver.to_smt2())
    return sha256(f'{get_version_string()}\0{kind}\0{text}'.encode()).hexdigest()


def collision(kind, current, old):
    # Solver-held AST references affect let sharing; both layouts are valid old runs.
    for n in range(5):
        for m in range(5):
            holders, older = [Solver() for _ in range(n)], [Solver() for _ in range(m)]
            for solver in holders:
                solver.add(current)
            for solver in older:
                solver.add(old)
            key = legacy_key(kind, current)
            if key == legacy_key(kind, old):
                return holders, older, key
    pytest.fail('expected the demonstrated legacy printer collision')


@pytest.mark.parametrize('safe_current,kind', [(False, 'check'), (True, 'check'), (False, 'core')])
def test_a_correct_legacy_unsat_answer_never_refutes_a_different_sat_ast(
        tmp_path, monkeypatch, safe_current, kind):
    if safe_current:
        current = And(f(7, 3) != 7, f(3, 3) == 7, Select(OWN_ONLY, 7) == 7)
        old = substitute(current, (OWN_ONLY, SHADOW_REF))
        assert not binder_capture_risk(current) and binder_capture_risk(old)
    else:
        current = shadowed_sat()
        old = substitute(current, (SHADOW_REF, OWN_ONLY))
    assert str(answer(current)) == 'sat' and str(answer(old)) == 'unsat'
    holders, older, exact = collision(kind, current, old)
    assert pc.query_key(kind, current)[0] != pc.query_key(kind, old)[0]
    monkeypatch.setenv('BLOCK_PROOF_CACHE', str(tmp_path / 'legacy.sqlite'))
    pc.store(exact, 'unsat' if kind == 'check' else [])
    assert pc.lookup(exact) == ('unsat' if kind == 'check' else [])
    if kind == 'check':
        assert be.solve_query(current, 5000) == 'sat'
    else:
        outcome = {}
        assert be.unsat_core([], current, 5000, outcome) is None
        assert outcome.get('answer') == 'sat'


def test_structural_binder_answers_still_reuse_without_solving(tmp_path, monkeypatch):
    monkeypatch.setenv('BLOCK_PROOF_CACHE', str(tmp_path / 'alpha.sqlite'))
    current = shadowed_sat()
    renamed = canon_binders(current)
    assert be.solve_query(current, 5000) == 'sat'
    assert pc.query_key('check', current) == pc.query_key('check', renamed)
    assert len(pc.query_key('check', current)) == 1

    def unexpected(*args, **kwargs):
        pytest.fail('a structural alpha hit must not solve again')

    monkeypatch.setattr(be, '_solve_query', unexpected)
    assert be.solve_query(renamed, 5000) == 'sat'
