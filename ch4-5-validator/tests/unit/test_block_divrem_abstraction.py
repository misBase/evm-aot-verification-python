"""Opaque div/rem results may prove a query UNSAT, never SAT or an input restriction."""
import gzip
from pathlib import Path
from types import SimpleNamespace

import pytest
from z3 import (And, BitVec, BitVecSort, ForAll, Function, Lambda, Not,
                SRem, Select, UDiv, URem, is_const, parse_smt2_string, simplify, substitute)

import verification.block_equivalence as be
from common.store_forwarding import forward_selects, join_extracts
from verification.block_parallel import _record, close_edge
from verification.block_specialization import BlockSpecialization as S
from verification.cutpoint_relation import RelationGoal as G


@pytest.fixture(autouse=True)
def no_cache(monkeypatch):
    monkeypatch.delenv("BLOCK_PROOF_CACHE", raising=False)
    monkeypatch.delenv("BLOCK_PAIR_WORKERS", raising=False)


@pytest.mark.parametrize("operation", [UDiv, URem, lambda x, y: x / y, SRem, lambda x, y: x % y])
def test_builtin_result_is_shared_and_every_original_model_extends(operation):
    x, y, a, b = (BitVec(f"dr_{s}", 8) for s in ("x", "y", "a", "b"))
    term = operation(x, y)
    formula = And(term == a, term == b)
    abstract, changed = be.abstract_divrem_results(formula)
    first, second = abstract.children()
    fresh = first.arg(0)
    assert changed and is_const(fresh) and fresh.eq(second.arg(0))
    restored = substitute(abstract, (fresh, term))
    assert be.solve_query(Not(formula == restored), 1000) == "unsat"
    simplified, changed = be.abstract_divrem_results(simplify(formula))
    assert changed  # Z3's *_i builtins after simplify are covered too.


def test_holiman_and_builtin_lookalike_uninterpreted_functions_are_not_replaced():
    x, y = BitVec("dr_uf_x", 8), BitVec("dr_uf_y", 8)
    for name in ("holiman_udiv", "holiman_udivrem", "bvudiv", "bvurem_i"):
        function = Function(name, BitVecSort(8), BitVecSort(8), BitVecSort(8))
        formula = function(x, y) == 0
        unchanged, changed = be.abstract_divrem_results(formula)
        assert not changed and unchanged.eq(formula)


def test_binders_and_free_de_bruijn_variables_are_rejected():
    from z3 import Var
    x, y = BitVec("dr_bound_x", 8), BitVec("dr_bound_y", 8)
    for formula in (ForAll([x], URem(x, y) == 0), Select(Lambda([x], URem(x, y)), y) == 0,
                    UDiv(Var(0, BitVecSort(8)), y) == 0):
        unchanged, changed = be.abstract_divrem_results(formula)
        assert not changed and unchanged.eq(formula)


def test_abstract_sat_is_not_a_refutation_and_false_goal_stays_false():
    x, y = BitVec("dr_false_x", 8), BitVec("dr_false_y", 8)
    formula = And(y != 0, URem(x, y) == y)
    abstract, changed = be.abstract_divrem_results(formula)
    assert changed and be.solve_query(abstract, 1000) == "sat"
    assert be.solve_query(formula, 1000) == "unsat"  # Abstract SAT says nothing about the original.
    prover = be.BlockEquivalenceProver([], [], {}, timeout_ms=1000)
    assert not close_edge(prover, "H2_false_divrem", And(x == 7, y == 3),
                          [("target", (G("gas", URem(x, y) == 2),))]).proved


def test_unknown_abstraction_uses_the_original_full_route(monkeypatch):
    x, y = BitVec("dr_unknown_x", 8), BitVec("dr_unknown_y", 8)
    goal = URem(x, y) == 1
    real = be.solve_query
    monkeypatch.setattr(be, "solve_query", lambda q, ms, **kw:
                        "unknown" if "divrem_result" in q.sexpr() else real(q, ms, **kw))
    prover = be.BlockEquivalenceProver([], [], {}, timeout_ms=1000)
    record = close_edge(prover, "H2_divrem_fallback", And(x == 7, y == 3),
                        [("target", (G("gas", goal),))])
    assert record.proved and not any(r.name.endswith("_divrem") for r in record.lemmas)


def test_real_23092_failure_is_refuted_without_a_512_bit_remainder_circuit():
    fixture = Path(__file__).with_name("data") / "h2_23092_live_stack_prefix_13.smt2.gz"
    formula = And(*parse_smt2_string(gzip.decompress(fixture.read_bytes()).decode()))
    forwarded = simplify(join_extracts(forward_selects(formula, {}), {}), bv_sort_ac=True)
    abstract, changed = be.abstract_divrem_results(forwarded)
    assert changed and be.solve_query(abstract, 3000) == "unsat"
    while str(formula.decl().name()) == "and" and formula.num_args() == 1:
        formula = formula.arg(0)
    base, goal = And(*formula.children()[:-1]), formula.arg(formula.num_args() - 1).arg(0)
    record = close_edge(be.BlockEquivalenceProver([], [], {}, timeout_ms=3000), "H2_real_23092", base,
                        [("target", (G("live_stack_prefix", goal),))])
    assert record.proved and any(r.name.endswith("_divrem") for r in record.lemmas)


def test_split_parent_is_not_reported_proved_until_all_contexts_are_proved():
    parent = S(18089, 18, None, 320)
    children = (S(18089, 18, None, 320, ((3, 4418),)),
                S(18089, 18, None, 320, ((3, 4418), (6, 0))))
    result = SimpleNamespace(diagnostics={18089: dict(instances=[], status="queued")})
    def record(spec, status, contexts=()):
        _record(result, dict(spec=spec, contexts=contexts, reasons=(), seconds=0, queries=0, failed=[]), status)
    record(parent, "split", children)
    assert result.diagnostics[18089]["status"] == "inconclusive"
    record(children[0], "proved")
    assert result.diagnostics[18089]["status"] == "inconclusive"
    record(children[1], "proved")
    assert result.diagnostics[18089]["status"] == "proved"
    record(children[1], "inconclusive")
    assert result.diagnostics[18089]["status"] == "inconclusive"
