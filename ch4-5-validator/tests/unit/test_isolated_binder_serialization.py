"""The isolation boundary must preserve de Bruijn bindings before printing SMT2."""
import json
from types import SimpleNamespace
import sys

import pytest
from z3 import And, BitVec, Select, Solver, parse_smt2_string, sat, unsat

import common.isolated_sat as isolated
from tests.unit.test_block_alpha_canon import SHADOW_REF, f
from verification.alpha_canon import PREFIX
from verification.block_equivalence import _parse_transport


def shadowed_sat():
    return And(f(7, 3) == 7, f(3, 3) != 7, Select(SHADOW_REF, 7) == 7)


def answer(formula):
    solver = Solver()
    solver.add(formula)
    return solver.check()


def test_unprotected_printing_turns_a_real_sat_query_into_unsat():
    formula = shadowed_sat()
    solver = Solver()
    solver.add(formula)
    assert answer(formula) == sat
    assert answer(And(*parse_smt2_string(solver.to_smt2()))) == unsat


@pytest.mark.parametrize("options", [{}, {"blast": True}, {"rlimit": 10000}, {"pure_bv": True}])
def test_every_isolation_route_sends_an_equivalent_query(monkeypatch, options):
    formula, sent = shadowed_sat(), []
    def run(*a, **kw):
        parsed = And(*parse_smt2_string(kw["input"]))
        sent.append(parsed)
        return SimpleNamespace(returncode=0, stdout=json.dumps(dict(parsed_alpha=_parse_transport(kw["input"])[1], payload=str(answer(parsed)))))
    monkeypatch.setattr(isolated.subprocess, "run", run)
    assert isolated.isolated_sat(formula, 5000, **options) == "sat"
    assert len(sent) == 1 and answer(formula != sent[0]) == unsat


@pytest.mark.skipif(sys.platform != "linux", reason="hard AS limit uses Linux /proc")
def test_real_child_preserves_the_sat_shadowing_counterexample():
    assert isolated.isolated_sat(shadowed_sat(), 5000) == "sat"


def test_reserved_prefix_collision_is_unknown_without_starting_a_child(monkeypatch):
    clash = BitVec(f"{PREFIX}1_0", 8)
    formula = And(shadowed_sat(), clash == 0)
    monkeypatch.setattr(isolated.subprocess, "run", lambda *a, **kw: pytest.fail("unsafe query sent to child"))
    assert isolated.isolated_sat(formula, 5000) == "unknown"
