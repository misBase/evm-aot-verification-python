"""The context DAG summary preserves the two original eligibility predicates."""
import gc
import gzip
from pathlib import Path
from time import monotonic
import weakref

import pytest
from z3 import (And, Array, BitVec, BitVecSort, Bool, ForAll, Function, If, Lambda,
                Map, Not, Select, Store, Var, is_and, is_not, is_or, parse_smt2_string)

import verification.block_equivalence as be
import verification.block_parallel as bp
from verification.cutpoint_relation import RelationGoal


def original_flags(term):
    return be._no_binder(term), bool(be._ite_conditions(term))


def test_ground_binder_open_var_and_declaration_parameters_match_originals():
    x, y, i = BitVec("eligibility_x", 8), BitVec("eligibility_y", 8), BitVec("eligibility_i", 8)
    flag = Bool("eligibility_flag")
    array = Array("eligibility_array", BitVecSort(8), BitVecSort(8))
    choice = If(flag, x, y)
    memory = Store(array, i, choice)
    lam = Lambda([i], If(flag, Select(array, i), x))
    quant = ForAll([i], If(flag, i == x, i == y))
    open_var = Var(0, BitVecSort(8))
    function = Function("eligibility_map_function", BitVecSort(8), BitVecSort(8))
    roots = [x, choice, choice == x, Select(memory, i), lam, lam == array,
             quant, And(quant, choice == x), open_var, open_var == x,
             And(open_var == x, choice == x), Map(function, memory) == array]
    summary = bp._ConditionalEligibility(lambda: None)
    assert [summary.flags(term) for term in roots] == [original_flags(term) for term in roots]
    # An ITE outside a binder still exists, while the whole root is not ground.
    assert summary.flags(And(quant, choice == x)) == (False, True)
    assert summary.flags(lam) == (False, False)


def test_actual_budget_stop_edge_matches_every_original_field_predicate():
    path = Path(__file__).with_name("data") / "h2_385_conditional_eligibility.smt2.gz"
    # This is the actual complete edge recorded at a budget stop, not a SAT
    # witness. Its inventory contains47 distinct constants and no overloaded UF.
    formula = And(*parse_smt2_string(gzip.decompress(path.read_bytes()).decode()))
    while is_and(formula) and formula.num_args() == 1:
        formula = formula.arg(0)
    negative = formula.arg(formula.num_args() - 1)
    assert is_not(negative)
    relation = negative.arg(0)
    while (is_or(relation) or is_and(relation)) and relation.num_args() == 1:
        relation = relation.arg(0)
    roots = [*be._conjuncts(And(*formula.children()[:-1])), *be._conjuncts(relation)]
    summary = bp._ConditionalEligibility(lambda: None)
    assert len(be._conjuncts(relation)) == 120
    for root in roots:
        assert summary.flags(root) == original_flags(root)


def test_keyed_context_and_ast_arguments_stay_alive():
    flag = Bool("eligibility_alive_flag")
    root = If(flag, BitVec("eligibility_alive_x", 8), BitVec("eligibility_alive_y", 8))
    alive = weakref.ref(root)
    summary = bp._ConditionalEligibility(lambda: None)
    assert summary.flags(root) == (True, True)
    del root
    gc.collect()
    assert alive() is not None
    assert all(key == (id(term.ctx), term.get_id()) for key, (term, _, _) in summary.memo.items())


def test_an_interrupted_scan_does_not_cache_an_unfinished_root():
    count = 0
    def budget():
        nonlocal count
        count += 1
        if count == 2:
            raise be.ProofBudgetExceeded("existing H2 deadline")
    root = If(Bool("eligibility_deadline_flag"), BitVec("eligibility_deadline_x", 8), 0) == 0
    summary = bp._ConditionalEligibility(budget)
    with pytest.raises(be.ProofBudgetExceeded):
        summary.flags(root)
    assert (id(root.ctx), root.get_id()) not in summary.memo
    summary.budget = lambda: None
    assert summary.flags(root) == original_flags(root)


def test_prepare_keeps_candidate_and_owner_order_and_ready_proofs(monkeypatch):
    x, y = BitVec("eligibility_order_x", 8), BitVec("eligibility_order_y", 8)
    flag = Bool("eligibility_order_flag")
    index = BitVec("eligibility_order_index", 8)
    array = Array("eligibility_order_array", BitVecSort(8), BitVecSort(8))
    bases = [And(Not(flag), index == n) for n in range(4)]
    goals = [[("target", (RelationGoal("gas", If(flag, y, x) == Select(Store(Store(array, 0, x), n + 1, y), 0)),))]
             for n in range(4)]
    def prepare():
        p = be.BlockEquivalenceProver([], [], {}, timeout_ms=1000)
        p.deadline = monotonic() + 30
        return bp.prepare_shared(p, bases, goals)
    new = prepare()
    class OriginalPredicates:
        def __init__(self, budget):
            self.budget = budget
        def flags(self, root):
            self.budget()
            return original_flags(root)
    with monkeypatch.context() as mp:
        mp.setattr(bp, "_ConditionalEligibility", OriginalPredicates)
        old = prepare()
    assert list(new["canonical"]) == list(old["canonical"])
    assert list(new["canonical_proofs"]) == list(old["canonical_proofs"])
    for key in new["canonical_proofs"]:
        assert [entry[0] for entry in new["canonical_proofs"][key]] == [entry[0] for entry in old["canonical_proofs"][key]]
    for n, (base, targets) in enumerate(zip(bases, goals)):
        ready_new = bp._canonical_ready(new, base, targets, f"edge_{n}")
        ready_old = bp._canonical_ready(old, base, targets, f"edge_{n}")
        assert list(ready_new) == list(ready_old)
        assert ready_new and all(r.proved for parts in ready_new.values() for r in parts)
