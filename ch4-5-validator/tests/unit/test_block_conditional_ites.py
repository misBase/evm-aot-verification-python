"""Path consequences simplify differing ITEs; weakening never certifies SAT."""
from dataclasses import replace
import gzip
from hashlib import sha256
from pathlib import Path

import pytest
from z3 import (And, BitVecs, BitVecSort, Bool, BoolVal, Concat, ForAll, If, is_bv_value,
                Lambda, Not, Select, UDiv, URem, Var, parse_smt2_string)

import verification.block_equivalence as be


def example(case):
    x, y = BitVecs(f"ci_{case}_x ci_{case}_y", 8)
    flag = Bool(f"ci_{case}_flag")
    cases = {
        "false": And(Not(flag), Not(If(flag, y, x) == x)),
        "true": And(flag, Not(If(flag, x, y) == x)),
        "unknown_guard": And(BoolVal(True), Not(If(flag, y, x) == x)),
        "sat_counterexample": And(flag, Not(If(flag, y, x) == x)),
        "alias": And(Not(flag), Not(Concat(If(flag, y, x), If(flag, y, x)) == Concat(x, x))),
        "shared_divrem": And(UDiv(x, y) > 0, Not(If(UDiv(x, y) == 0, y, x) == x)),
        "distinct_operator": And(UDiv(x, y) > 0, Not(If(URem(x, y) == 0, y, x) == x)),
    }
    return cases[case]


@pytest.mark.parametrize("case", ["false", "true", "alias", "shared_divrem"])
def test_proved_original_branch_and_its_dependencies_are_preserved(case):
    formula = example(case)
    proved, answer, records = be.refute_conditional_ites(formula, 5000)
    assert answer == "unsat" and len(records) == 1 and records[0].proved
    root = records[0]
    assert root.required_lemmas and root.lemmas[-1].name == "conditional_ite_residual"
    guards = root.lemmas[:-1]
    assert len(guards) == 1 and guards[0].required_lemmas
    assert not replace(root, lemmas=()).proved
    assert not replace(root, lemmas=root.lemmas[1:]).proved
    assert not replace(guards[0], lemmas=()).proved
    assert be.solve_query(formula, 1000) == be.solve_query(proved, 1000) == "unsat"


@pytest.mark.parametrize("case", ["unknown_guard", "sat_counterexample", "distinct_operator"])
def test_undecided_or_satisfiable_original_is_never_certified(case):
    formula = example(case)
    assert be.solve_query(formula, 1000) == "sat"
    unchanged, answer, records = be.refute_conditional_ites(formula, 5000)
    assert unchanged.eq(formula) and answer == "unknown" and not records


def test_unknown_side_checks_leave_the_original(monkeypatch):
    formula = example("false")
    monkeypatch.setattr(be, "_prove_equal", lambda *args, **kw: None)
    unchanged, answer, records = be.refute_conditional_ites(formula, 5000)
    assert unchanged.eq(formula) and answer == "unknown" and not records


def test_original_literal_branch_is_tried_first(monkeypatch):
    x, y = BitVecs("ci_literal_x ci_literal_y", 8)
    flag, attempted = Bool("ci_literal_flag"), []
    formula = And(Not(flag), y == 1, Not(If(flag, x, 1) == y))
    prove = be._prove_equal

    def track(prefix, ite, arm, *args, **kw):
        attempted.append(arm)
        return prove(prefix, ite, arm, *args, **kw)

    monkeypatch.setattr(be, "_prove_equal", track)
    assert be.refute_conditional_ites(formula, 5000)[1] == "unsat"
    assert is_bv_value(attempted[0]) and attempted[0].as_long() == 1


def test_preparation_deadline_is_charged_before_any_side_proof(monkeypatch):
    formula, clock, forwarded = example("false"), [0.0], []
    monkeypatch.setattr(be, "monotonic", lambda: clock[0])

    def forward(term, cache):
        forwarded.append(term)
        clock[0] = 2.0
        return term

    def unexpected(*args, **kw):
        raise AssertionError("preparation already exhausted the deadline")

    monkeypatch.setattr(be, "forward_selects", forward)
    monkeypatch.setattr(be, "_prove_equal", unexpected)
    unchanged, answer, records = be.refute_conditional_ites(formula, 1000)
    assert len(forwarded) == 1
    assert unchanged.eq(formula) and answer == "unknown" and not records
    clock[0] = 3.0
    forwarded.clear()
    assert be.refute_conditional_ites(formula, 1000, deadline=2.0)[1:] == ("unknown", ())
    assert not forwarded


def test_side_proof_finishing_after_deadline_is_discarded(monkeypatch):
    formula, clock = example("false"), [0.0]
    monkeypatch.setattr(be, "monotonic", lambda: clock[0])

    def late_proof(*args, **kw):
        assert 0 < args[3] <= 1000
        clock[0] = 2.0
        return []

    monkeypatch.setattr(be, "_prove_equal", late_proof)
    unchanged, answer, records = be.refute_conditional_ites(formula, 1000)
    assert unchanged.eq(formula) and answer == "unknown" and not records


def test_no_raw_ite_goal_returns_before_forwarding(monkeypatch):
    x, y = BitVecs("ci_no_ite_x ci_no_ite_y", 8)
    formula = And(x > 0, Not(x == y))

    def unexpected(*args, **kw):
        raise AssertionError("unrelated goal reached forwarding")

    monkeypatch.setattr(be, "forward_selects", unexpected)
    unchanged, answer, records = be.refute_conditional_ites(formula, 5000)
    assert unchanged.eq(formula) and answer == "unknown" and not records


def test_binders_and_open_variables_bail_before_forwarding(monkeypatch):
    x, y = BitVecs("ci_bound_x ci_bound_y", 8)
    flag = Bool("ci_bound_flag")
    goal = Not(If(flag, y, x) == x)
    formulas = (And(ForAll([x], x == x), goal),
                And(Var(0, BitVecSort(8)) == x, goal),
                And(Not(flag), Not(Select(Lambda([x], x), y) == x)))

    def unexpected(*args, **kw):
        raise AssertionError("unsupported formula reached forwarding")

    monkeypatch.setattr(be, "forward_selects", unexpected)
    for formula in formulas:
        unchanged, answer, records = be.refute_conditional_ites(formula, 5000)
        assert unchanged.eq(formula) and answer == "unknown" and not records


def test_check_route_pins_the_complete_conditional_subtree(monkeypatch):
    formula = example("false")
    result = be.refute_conditional_ites(formula, 5000)
    assert result[1] == "unsat"
    monkeypatch.setattr(be, "solve_query", lambda *a, **kw: "unknown")
    monkeypatch.setattr(be, "refute_conditional_ites", lambda *a, **kw: result)
    prover, records = be.BlockEquivalenceProver([], [], {}, timeout_ms=1000), []
    assert prover._check("conditional_route", formula, records, split=False)
    assert records[0].required_lemmas == ("conditional_ites",)
    assert not replace(records[0], lemmas=()).proved


def test_safely_captured_real_h2_is_discovered_without_manual_candidates():
    path = Path(__file__).with_name("data") / "h2_22918_conditional_ite.smt2.gz"
    text = gzip.decompress(path.read_bytes())
    assert sha256(text).hexdigest() == "053364d149ad1479b026c99f07339a8dd9ddccbead6cca5c269eb1213039e525"
    formula = And(*parse_smt2_string(text.decode()))
    _, answer, records = be.refute_conditional_ites(formula, 30000)
    assert answer == "unsat" and len(records) == 1 and records[0].proved
    guards = records[0].lemmas[:-1]
    assert len(guards) == 1 and guards[0].name == "conditional_ite_0"
    assert len(guards[0].lemmas) == 1 and guards[0].required_lemmas
    assert records[0].lemmas[-1].formula == "false"
