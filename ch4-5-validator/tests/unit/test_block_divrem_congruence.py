"""Checked division abstractions and their transported dependency manifests."""
import gzip
from dataclasses import replace
from pathlib import Path
import pickle
from time import monotonic
import zlib

import pytest
from z3 import (And, Bool, BitVec, BitVecSort, BitVecVal, Extract, ForAll, Function, If, Lambda,
                Not, SRem, Select, UDiv, URem, is_app, is_bv, parse_smt2_string)

import verification.block_equivalence as be
from verification.block_parallel import slim, verify_parallel


@pytest.fixture(autouse=True)
def no_cache(monkeypatch):
    monkeypatch.delenv("BLOCK_PROOF_CACHE", raising=False)
    monkeypatch.delenv("BLOCK_PAIR_WORKERS", raising=False)


def test_same_builtin_and_sort_retains_application_congruence():
    x, y, a, b = (BitVec(f"dc_{s}", 8) for s in ("x", "y", "a", "b"))
    formula = And(x == a, y == b, UDiv(x, y) != UDiv(a, b))
    abstract, changed = be.abstract_divrem_congruence(formula)
    assert changed and be.solve_query(abstract, 1000) == "unsat"


@pytest.mark.parametrize("case", ["operator", "width", "arguments", "zero_divisor"])
def test_distinct_arithmetic_is_never_conflated(case):
    x, y, z = (BitVec(f"dc_distinct_{s}", 8) for s in ("x", "y", "z"))
    wide = BitVec("dc_distinct_wide", 16)
    formulas = {
        "operator": And(x == 254, y == 2, UDiv(x, y) != x / y),
        "width": And(wide == 257, Extract(7, 0, UDiv(wide, BitVecVal(2, 16)))
                     != UDiv(Extract(7, 0, wide), BitVecVal(2, 8))),
        "arguments": And(x == 7, y == 2, z == 3, UDiv(x, y) != UDiv(x, z)),
        "zero_divisor": And(x == 7, UDiv(x, BitVecVal(0, 8)) != URem(x, BitVecVal(0, 8))),
    }
    formula = formulas[case]
    assert be.solve_query(formula, 1000) == "sat"
    abstract, changed = be.abstract_divrem_congruence(formula)
    assert changed and be.solve_query(abstract, 1000) == "sat"
    unchanged, answer, records = be.refute_divrem_congruence(formula, 1000)
    assert answer == "unknown" and unchanged.eq(formula) and not records


def test_binders_and_uninterpreted_lookalikes_are_unchanged():
    from z3 import Var
    x, y = BitVec("dc_bound_x", 8), BitVec("dc_bound_y", 8)
    formulas = [ForAll([x], UDiv(x, y) == 0), Select(Lambda([x], URem(x, y)), y) == 0,
                UDiv(Var(0, BitVecSort(8)), y) == 0]
    for name in ("holiman_udiv", "holiman_udivrem", "bvudiv", "bvurem_i"):
        formulas.append(Function(name, BitVecSort(8), BitVecSort(8), BitVecSort(8))(x, y) == 0)
    for formula in formulas:
        unchanged, changed = be.abstract_divrem_congruence(formula)
        assert not changed and unchanged.eq(formula)


def test_no_builtin_returns_before_forwarding_or_guard_probes(monkeypatch):
    def unexpected(*args, **kwargs):
        raise AssertionError("irrelevant formula ran the division route")
    monkeypatch.setattr(be, "forward_selects", unexpected)
    monkeypatch.setattr(be, "uf_guards", unexpected)
    formula = BitVec("dc_no_div", 8) == 3
    unchanged, answer, records = be.refute_divrem_congruence(formula, 30000)
    assert unchanged.eq(formula) and answer == "unknown" and not records


def test_a_nonconstant_guard_is_not_assumed():
    x, a, b = (BitVec(f"dc_guard_{s}", 8) for s in ("x", "a", "b"))
    formula = And(a == 9, b == 3, If(x == 0, UDiv(a, b), UDiv(a - 1, b)) != UDiv(a - 1, b))
    assert be.solve_query(formula, 1000) == "sat"
    unchanged, answer, records = be.refute_divrem_congruence(formula, 2000)
    assert answer == "unknown" and unchanged.eq(formula) and not records


def captured(name):
    path = Path(__file__).with_name("data") / name
    return And(*parse_smt2_string(gzip.decompress(path.read_bytes()).decode()))


@pytest.fixture(scope="module")
def symbolic_composition():
    records = []
    prover = be.BlockEquivalenceProver([], [], {}, timeout_ms=30000, deadline=monotonic()+600)
    assert prover._check("H2_real_signed_div", captured("h2_19169_symbolic_stack.smt2.gz"), records, split=False)
    record = records[-1]
    assert record.required_lemmas and any(r.name.startswith("store_view_read") for r in record.lemmas)
    assert any(r.name == "divrem_congruence" for r in record.lemmas)
    return record


def test_real_symbolic_memory_case_has_all_checked_dependencies(symbolic_composition):
    assert symbolic_composition.proved
    assert all(r.required_lemmas for r in symbolic_composition.lemmas if r.name.startswith("store_view_read"))


@pytest.mark.parametrize("name", ["h2_19169_concrete_memory_stack.smt2.gz", "h2_16670_gas.smt2.gz"])
def test_the_same_route_refutes_other_captured_instances(name):
    formula = captured(name)
    _, answer, records = be.refute_divrem_congruence(formula, 30000)
    assert answer == "unsat" and records and all(r.proved for r in records)


@pytest.fixture(scope="module")
def genuine_parallel_run():
    options = dict(gas_check="full", gas_budget=1_000_000_000, num_inputs=0, timeout_ms=3000, node_seconds=300,
                   first_pass_node_seconds=None, max_parameter_values=8, max_depth=400, max_instances=2048,
                   wall_seconds=900, summaries=False)
    result = verify_parallel("tests/data/lockstep_counter_loop", options, workers=1)
    assert result.verified
    return result


def _consume_with_extra_checked_lemma(result, composition, mutation=None):
    certificate = result.certificate
    i = next(i for i, node in enumerate(certificate.nodes) if node["edges"])
    node = certificate.nodes[i]
    edge = node["edges"][0]
    # The genuine edge proof remains intact. Adding an independently checked
    # UNSAT lemma exercises transport through the real data-only consumer.
    wrapper = replace(edge.obligation, lemmas=(*edge.obligation.lemmas, composition), required_lemmas=None)
    assert wrapper.required_lemmas is not None
    if mutation is not None:
        wrapper = mutation(wrapper)
    changed = replace(certificate, nodes=certificate.nodes[:i] +
                      (dict(node, edges=(replace(edge, obligation=wrapper), *node["edges"][1:])),) +
                      certificate.nodes[i+1:])
    prover, initial = result._prover, result._initial
    prover._issued_program_certificate = changed
    try:
        return changed.valid(prover, initial)
    finally:
        prover._issued_program_certificate = certificate


def test_slim_and_pickle_preserve_manifest_for_the_actual_parallel_consumer(symbolic_composition,
                                                                         genuine_parallel_run):
    transported = pickle.loads(zlib.decompress(zlib.compress(pickle.dumps(slim(symbolic_composition)))))
    assert transported.required_lemmas == symbolic_composition.required_lemmas
    assert _consume_with_extra_checked_lemma(genuine_parallel_run, transported)


@pytest.mark.parametrize("missing", ["composition_one", "composition_all", "view_one", "view_all",
                                     "subtree", "wrapper_all", "broken_view"])
def test_parallel_consumer_rejects_missing_or_broken_new_dependencies(symbolic_composition,
                                                                   genuine_parallel_run, missing):
    def mutate(wrapper):
        composition = wrapper.lemmas[-1]
        if missing in ("composition_one", "composition_all"):
            composition = replace(composition, lemmas=composition.lemmas[1:] if missing.endswith("one") else ())
        elif missing in ("view_one", "view_all", "broken_view"):
            i = next(i for i, r in enumerate(composition.lemmas) if r.name.startswith("store_view_read"))
            view = composition.lemmas[i]
            children = (replace(view.lemmas[0], answer="unknown"), *view.lemmas[1:]) if missing == "broken_view" else (
                view.lemmas[1:] if missing == "view_one" else ())
            view = replace(view, lemmas=children)
            composition = replace(composition, lemmas=composition.lemmas[:i]+(view,)+composition.lemmas[i+1:])
        elif missing == "subtree":
            return replace(wrapper, lemmas=wrapper.lemmas[:-1])
        else:
            return replace(wrapper, lemmas=())
        return replace(wrapper, lemmas=(*wrapper.lemmas[:-1], composition))
    assert not _consume_with_extra_checked_lemma(genuine_parallel_run, symbolic_composition, mutate)



def conditional_query(label, *, positive=True):
    x, y = BitVec(f"dc_cond_{label}_x", 8), BitVec(f"dc_cond_{label}_y", 8)
    sign = Bool(f"dc_cond_{label}_sign")
    terms = [sign if positive else Not(sign), UDiv(If(sign, x, -x), y) != UDiv(x, y)]
    if not positive:
        terms.extend((x == 7, y == 2))
    return And(*terms)


@pytest.fixture
def conditional_composition(monkeypatch):
    solve, calls = be.solve_query, []

    def miss_first(query, budget, *args, **kwargs):
        calls.append(budget)
        return "unknown" if len(calls) == 1 else solve(query, budget, *args, **kwargs)

    monkeypatch.setattr(be, "solve_query", miss_first)
    formula = conditional_query("entailed")
    _, answer, records = be.refute_divrem_congruence(formula, 5000)
    assert answer == "unsat" and len(records) == 1
    record = records[0]
    assert calls[0] <= be._QUICK_EXACT_MS
    assert record.proved and record.lemmas
    assert record.required_lemmas == tuple(o.name for o in record.lemmas)
    assert all(o.name.startswith("unify_") for o in record.lemmas)
    return record


def test_conditional_congruence_preserves_checked_argument_dependencies(conditional_composition):
    assert conditional_composition.proved


def test_conditional_congruence_does_not_assume_the_other_branch(monkeypatch):
    formula = conditional_query("other", positive=False)
    solve, calls = be.solve_query, []
    assert solve(formula, 1000) == "sat"

    def miss_first(query, budget, *args, **kwargs):
        calls.append(budget)
        return "unknown" if len(calls) == 1 else solve(query, budget, *args, **kwargs)

    monkeypatch.setattr(be, "solve_query", miss_first)
    unchanged, answer, records = be.refute_divrem_congruence(formula, 3000)
    assert unchanged.eq(formula) and answer == "unknown" and not records


def test_conditional_congruence_unknown_or_expired_keeps_original(monkeypatch):
    formula = conditional_query("unknown")
    monkeypatch.setattr(be, "solve_query", lambda *a, **kw: "unknown")
    monkeypatch.setattr(be, "refute_over_bv_abstraction", lambda query, *a, **kw: (query, "unknown"))
    for deadline in (None, monotonic() - 1):
        unchanged, answer, records = be.refute_divrem_congruence(formula, 1000, deadline)
        assert unchanged.eq(formula) and answer == "unknown" and not records


def test_conditional_preprocessing_and_queries_share_original_deadline(monkeypatch):
    formula = conditional_query("deadline")
    now, calls = [100.0], []
    monkeypatch.setattr(be, "monotonic", lambda: now[0])

    def unknown(query, budget, *a, **kw):
        calls.append(budget)
        now[0] += budget / 1000
        return "unknown"

    def exhaust(query, budget, deadline):
        assert budget <= 1000 and deadline <= 105.0
        now[0] = deadline
        return query, ()

    monkeypatch.setattr(be, "solve_query", unknown)
    monkeypatch.setattr(be, "unify_uf_arguments", exhaust)
    monkeypatch.setattr(be, "refute_over_bv_abstraction", lambda *a: pytest.fail("deadline exhausted"))
    unchanged, answer, records = be.refute_divrem_congruence(formula, 30000, 105.0)
    assert unchanged.eq(formula) and answer == "unknown" and not records
    assert calls == [be._QUICK_EXACT_MS]


@pytest.mark.parametrize("missing", ["one", "all", "subtree"])
def test_actual_consumer_rejects_missing_conditional_unification_dependencies(
        conditional_composition, genuine_parallel_run, missing):
    transported = pickle.loads(zlib.decompress(zlib.compress(pickle.dumps(slim(conditional_composition)))))
    assert _consume_with_extra_checked_lemma(genuine_parallel_run, transported)

    def mutate(wrapper):
        if missing == "subtree":
            return replace(wrapper, lemmas=wrapper.lemmas[:-1])
        composition = wrapper.lemmas[-1]
        composition = replace(composition, lemmas=composition.lemmas[1:] if missing == "one" else ())
        return replace(wrapper, lemmas=(*wrapper.lemmas[:-1], composition))

    assert not _consume_with_extra_checked_lemma(genuine_parallel_run, transported, mutate)
