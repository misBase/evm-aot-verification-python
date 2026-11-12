"""A path kept without a witness gets one larger blasted search, paid from the run's budget."""
import pytest
from z3 import BitVecs, sat, unknown, unsat

import common.isolated_sat as isolated
import x86_64.cfg_state as cs


@pytest.fixture
def kept(monkeypatch):
    """Every slot-sized check is unknown and the refutation probe too: the path is kept
    without a witness. The witness search answers `answer` (sat: the real solver)."""
    calls, answer = [], {"witness": unknown}

    def bounded(solver, timeout_ms, tag, wall_ms=None):
        calls.append((tag, timeout_ms, wall_ms))
        if tag != "witness":
            return unknown
        return solver.check() if answer["witness"] == sat else answer["witness"]
    monkeypatch.setattr(cs, "_bounded_check", bounded)
    monkeypatch.setattr(isolated, "isolated_sat", lambda *a, **k: "unknown")
    x, y = BitVecs("ws_x ws_y", 8)
    path = cs.X86Constraints()
    path.add(x + y == 7)
    return path, calls, answer


def test_the_search_finds_a_literal_witness_and_spends_the_budget(kept):
    path, calls, answer = kept
    answer["witness"] = sat
    prefix = cs.PrefixSolver()
    assert path.is_possible(1000, prefix) and path._witness is not None
    assert ("witness", 1000 * cs.WITNESS_SEARCH_FACTOR, cs.WITNESS_SEARCH_WALL_MS) in calls
    assert prefix.witness_seconds < cs.WITNESS_SEARCH_SECONDS


def test_an_unsat_search_prunes_and_an_unknown_one_keeps_the_path(kept):
    path, _, answer = kept
    answer["witness"] = unsat
    assert not path.is_possible(1000, cs.PrefixSolver())  # the blasted rewrite is exact
    answer["witness"] = unknown
    assert path.is_possible(1000, cs.PrefixSolver()) and path._witness is None


def test_no_search_once_the_budget_is_spent(kept):
    path, calls, answer = kept
    answer["witness"] = sat
    prefix = cs.PrefixSolver()
    prefix.witness_seconds = 0
    assert path.is_possible(1000, prefix) and path._witness is None
    assert all(tag != "witness" for tag, _, _ in calls)


def test_a_search_that_raises_still_pays_for_its_time(kept, monkeypatch):
    import time
    path, _, _ = kept
    def failing(solver, timeout_ms, tag, wall_ms=None):
        if tag != "witness":
            return unknown
        time.sleep(0.05)
        raise RuntimeError("stopped mid-search")
    monkeypatch.setattr(cs, "_bounded_check", failing)
    prefix = cs.PrefixSolver()
    with pytest.raises(RuntimeError):
        path.is_possible(1000, prefix)
    assert prefix.witness_seconds <= cs.WITNESS_SEARCH_SECONDS - 0.05
