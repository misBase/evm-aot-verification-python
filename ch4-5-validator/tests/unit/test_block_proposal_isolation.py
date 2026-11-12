"""Expensive proposals use original-valid models and never abstract SAT answers."""
from pathlib import Path
import gzip
import sys

import pytest
from z3 import And, BitVec, Solver, is_true, parse_smt2_string, sat, unsat

import common.isolated_sat as isolated
from common.node_monitor import NodeMemoryExceeded
import verification.block_equivalence as be


@pytest.fixture
def expensive(monkeypatch):
    monkeypatch.setattr(isolated, 'expensive_bitblast', lambda f: True)
    def forbidden(*args, **kwargs):
        pytest.fail('an expensive proposal must not allocate a parent solver')
    monkeypatch.setattr(be, '_solver', forbidden)


def test_valid_model_is_returned_without_the_full_fallback(expensive, monkeypatch):
    x = BitVec('proposal_x', 64)
    formula = x == 7
    solver = Solver()
    solver.add(formula)
    assert solver.check() == sat
    model = solver.model()
    monkeypatch.setattr(isolated, 'isolated_small_mul_model', lambda *a: model)
    monkeypatch.setattr(isolated, 'isolated_sat', lambda *a, **kw: pytest.fail('unneeded fallback'))
    result, witness = be.BlockEquivalenceProver([], [], {}, timeout_ms=3000)._blasted_model(formula)
    assert result == sat and witness is model and is_true(witness.eval(formula))


@pytest.mark.parametrize('answer', ['sat', 'unsat', 'unknown'])
def test_missed_search_passes_only_original_formula_to_fallback(expensive, monkeypatch, answer):
    x = BitVec('proposal_fallback', 64)
    formula, clock, seen = x == 2**40, [0.0], []
    monkeypatch.setattr(be, 'monotonic', lambda: clock[0])
    def missed(original, budget):
        assert original.eq(formula) and budget == 5000
        clock[0] = 4.0
    def fallback(original, budget, *, blast):
        seen.append((original, budget, blast))
        return answer
    monkeypatch.setattr(isolated, 'isolated_small_mul_model', missed)
    monkeypatch.setattr(isolated, 'isolated_sat', fallback)
    result, witness = be.BlockEquivalenceProver([], [], {}, timeout_ms=30000)._blasted_model(formula)
    assert len(seen) == 1 and seen[0][0].eq(formula) and seen[0][1:] == (26000, True)
    assert (result == unsat) == (answer == 'unsat') and result != sat and witness is None


def test_expired_candidate_does_not_gain_another_budget(expensive, monkeypatch):
    clock = [0.0]
    monkeypatch.setattr(be, 'monotonic', lambda: clock[0])
    def late(*args):
        clock[0] = 31.0
    monkeypatch.setattr(isolated, 'isolated_small_mul_model', late)
    monkeypatch.setattr(isolated, 'isolated_sat', lambda *a, **kw: pytest.fail('budget exhausted'))
    assert be.BlockEquivalenceProver([], [], {}, timeout_ms=30000)._blasted_model(
        BitVec('proposal_late', 64) == 0) == ('unknown', None)


def test_node_abort_is_never_a_model_or_decision(expensive, monkeypatch):
    def aborted(*args):
        raise NodeMemoryExceeded('node stopped')
    monkeypatch.setattr(isolated, 'isolated_small_mul_model', aborted)
    with pytest.raises(NodeMemoryExceeded):
        be.BlockEquivalenceProver([], [], {}, timeout_ms=3000)._blasted_model(
            BitVec('proposal_abort', 64) == 0)


@pytest.mark.skipif(sys.platform != 'linux', reason='OS-limited scalar worker uses /proc')
def test_real_proposal_returns_a_model_of_the_original_formula():
    path = Path(__file__).with_name('data') / '18089_model_row0_blast.smt2.gz'
    formula = And(*parse_smt2_string(gzip.decompress(path.read_bytes()).decode()))
    answer, model = be.BlockEquivalenceProver([], [], {}, timeout_ms=5000)._blasted_model(formula)
    assert answer == sat and model is not None
    assert is_true(model.eval(formula, model_completion=True))
