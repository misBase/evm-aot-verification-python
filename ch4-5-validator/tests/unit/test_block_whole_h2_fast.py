"""Bounded exact H2 admission and unchanged certificate rejection boundaries."""
from dataclasses import replace
from pathlib import Path
import time
from types import SimpleNamespace

import pytest
import z3 as z

import verification.block_equivalence as be
import verification.block_parallel as bp
from verification.block_specialization import BlockSpecialization as S
from verification.cutpoint_relation import RelationGoal


@pytest.fixture(autouse=True)
def no_external_proof_cache(monkeypatch):
    monkeypatch.delenv("BLOCK_PROOF_CACHE", raising=False)
    monkeypatch.setenv("BLOCK_PAIR_WORKERS", "1")
    actual = Path(be.__file__).resolve().parent / "block_parallel.py"
    assert Path(bp.__file__).resolve() == actual
    assert Path(bp._quick_whole_h2.__code__.co_filename).resolve() == actual


def goals(condition):
    return [(S(1, 0, 0, 0), (RelationGoal("live_stack_prefix", condition),))]


def test_exact_only_and_empty_target_semantics():
    p = be.BlockEquivalenceProver([], [], {}, timeout_ms=1000, deadline=time.monotonic() + 10)
    x = z.BitVec("whole_exact_x", 8)
    bases = [x == 3, x == 4, z.BoolVal(False), z.BoolVal(True), z.BoolVal(True)]
    targets = [goals(x == 3), goals(x == 3), [], [], [(S(1, 0, 0, 0), ())]]
    records = [None] * len(bases)
    bp._quick_whole_h2(p, [f"H2_{i}" for i in range(len(bases))], bases, targets, records)
    assert [r is not None for r in records] == [True, False, True, False, True]
    for index in (0, 2, 4):
        assert records[index].proved and records[index].name == f"H2_{index}"
        assert records[index].formula.startswith("sha256:")
        assert records[index].provenance == "h2_whole_exact" and records[index].lemmas == ()


@pytest.mark.parametrize("context_seconds,expected_max_ms", [(1.0, 100), (0.025, 25)])
def test_phase_and_context_bound_unknown_without_reclassifying_edges(monkeypatch, context_seconds, expected_max_ms):
    clock, calls = [100.0], []
    monkeypatch.setattr(bp, "monotonic", lambda: clock[0])
    def unknown(formula, timeout_ms):
        calls.append(timeout_ms)
        clock[0] += 0.2
        return "unknown"
    monkeypatch.setattr(be, "solve_query", unknown)
    p = SimpleNamespace(timeout_ms=100, deadline=100.0 + context_seconds)
    records = [None] * 5
    bp._quick_whole_h2(p, [f"H2_{i}" for i in range(5)], [z.BoolVal(True)] * 5,
                       [goals(z.BoolVal(False))] * 5, records)
    assert len(calls) == 1 and 0 < calls[0] <= expected_max_ms
    assert records == [None] * 5 and p.deadline == 100.0 + context_seconds


def test_empty_edges_do_not_query(monkeypatch):
    monkeypatch.setattr(be, "solve_query", lambda *args: pytest.fail("empty edge set queried"))
    bp._quick_whole_h2(SimpleNamespace(timeout_ms=1000, deadline=None), [], [], [], [])


def worker_case(monkeypatch):
    """A local-result protocol fixture; its H2 predicates still use real solvers."""
    x = z.BitVec("whole_worker_x", 8)
    spec, target = S(0, 0, 0, 0), S(1, 0, 0, 0)
    evm = [SimpleNamespace(condition=z.BoolVal(True), state=object(), location=1)]
    machine = [SimpleNamespace(condition=x == i, state=object(), location=1) for i in range(3)]
    node = SimpleNamespace(proved=True, reasons=(), status="proved", queries=0, obligations=(),
        premise=z.BoolVal(True), context=SimpleNamespace(state=object(), memory_snapshot=None),
        evm_outcomes=evm, x86_outcomes=machine,
        theorem=SimpleNamespace(cutpoint_manifest=((0, 0, 1), (0, 1, 1), (0, 2, 1))))
    p = be.BlockEquivalenceProver([], [], {}, timeout_ms=1000)
    p.prove = lambda wanted: node
    p.schema = SimpleNamespace(relation_goals=lambda *args, **kwargs:
                              (RelationGoal("live_stack_prefix", x != 1),))
    monkeypatch.setattr(bp, "_WORKER", dict(setup=SimpleNamespace(prover=p), identity="protocol-test",
                                            targets={1: (target,)}))
    return spec, target, x


def test_only_hard_subset_prepares_and_records_keep_manifest_order(monkeypatch):
    spec, target, x = worker_case(monkeypatch)
    prepare, inspected = bp.prepare_shared, []
    def inspect_subset(prover, bases, targets):
        inspected.append((bases, targets))
        return prepare(prover, bases, targets)
    monkeypatch.setattr(bp, "prepare_shared", inspect_subset)
    node = bp._prove_instance(spec, 10, time.time() + 20, (spec,))
    assert len(inspected) == 1
    bases, targets = inspected[0]
    assert len(bases) == len(targets) == 1 and z.simplify(bases[0]).eq(x == 1)
    assert targets[0][0][0] == target
    assert node["expected"] == ((0, 0), (0, 1), (0, 2))
    assert [e.pair for e in node["edges"]] == [(0, 0), (0, 1), (0, 2)]
    assert [e.obligation.proved for e in node["edges"]] == [True, False, True]
    assert node["reasons"] and bp.final_status(node) == "inconclusive"


def test_all_fast_edges_skip_shared_preparation(monkeypatch):
    spec, _, _ = worker_case(monkeypatch)
    bp._WORKER["setup"].prover.schema.relation_goals = lambda *args, **kwargs: (
        RelationGoal("live_stack_prefix", z.BoolVal(True)),)
    monkeypatch.setattr(bp, "prepare_shared", lambda *args: pytest.fail("proved edges entered shared preparation"))
    node = bp._prove_instance(spec, 10, time.time() + 20, (spec,))
    assert len(node["expected"]) == len(node["edges"]) == 3 and not node["reasons"]
    assert all(e.obligation.proved for e in node["edges"])


def test_no_manifest_edges_skip_preparation_and_keep_empty_expected(monkeypatch):
    spec, _, _ = worker_case(monkeypatch)
    node = bp._WORKER["setup"].prover.prove(spec)
    node.theorem.cutpoint_manifest = ()
    monkeypatch.setattr(bp, "prepare_shared", lambda *args: pytest.fail("empty edges entered shared preparation"))
    result = bp._prove_instance(spec, 10, time.time() + 20, (spec,))
    assert result["expected"] == result["edges"] == () and not result["reasons"]


def test_shared_budget_keeps_completed_fast_edges_and_missing_expected(monkeypatch):
    spec, _, _ = worker_case(monkeypatch)
    def expired(*args):
        raise be.ProofBudgetExceeded("injected shared preparation expiry")
    monkeypatch.setattr(bp, "prepare_shared", expired)
    node = bp._prove_instance(spec, 10, time.time() + 20, (spec,))
    assert node["expected"] == ((0, 0), (0, 1), (0, 2))
    assert [e.pair for e in node["edges"]] == [(0, 0), (0, 2)]
    assert all(e.obligation.proved and e.obligation.provenance == "h2_whole_exact" for e in node["edges"])
    assert any("budget exhausted" in reason for reason in node["reasons"])
    assert bp.final_status(node) == "inconclusive"


def test_fast_phase_abort_keeps_earlier_actual_proof(monkeypatch):
    spec, _, _ = worker_case(monkeypatch)
    solve, calls = be.solve_query, []
    def interrupted(formula, timeout_ms):
        calls.append(True)
        if len(calls) == 2:
            raise be.ProofBudgetExceeded("injected fast phase expiry")
        return solve(formula, timeout_ms)
    monkeypatch.setattr(be, "solve_query", interrupted)
    node = bp._prove_instance(spec, 10, time.time() + 20, (spec,))
    assert len(calls) == 2 and [e.pair for e in node["edges"]] == [(0, 0)]
    assert node["edges"][0].obligation.proved and len(node["expected"]) == 3
    assert bp.final_status(node) == "inconclusive"


@pytest.fixture(scope="module")
def genuine(tmp_path_factory):
    options = dict(gas_check="full", gas_budget=1000000000, num_inputs=0, timeout_ms=3000,
        node_seconds=10, first_pass_node_seconds=10, node_memory_mb=512, max_depth=400,
        max_instances=64, max_parameter_values=32, wall_seconds=40,
        summaries=False, constant_insensitive=True)
    result = bp.verify_parallel(str(Path("tests/data/two_block")), options,
                                workers=1, pair_workers=1, results_dir=tmp_path_factory.mktemp("whole-h2"))
    assert result.verified, result.reasons
    assert any(e.obligation.provenance == "h2_whole_exact"
               for node in result.certificate.nodes for e in node["edges"])
    return result


def test_real_tiny_parallel_certificate_closes(genuine):
    assert genuine.certificate.valid(genuine._prover, genuine._initial)


@pytest.mark.parametrize("mutation", ["answer", "edge_missing", "expected_missing", "target_version"])
def test_real_consumer_still_rejects_tampered_fast_edges(genuine, mutation):
    original = genuine.certificate
    index = next(i for i, node in enumerate(original.nodes) if node["edges"])
    node = dict(original.nodes[index])
    edge, *remaining = node["edges"]
    if mutation == "answer":
        node["edges"] = (replace(edge, obligation=replace(edge.obligation, answer="unknown")), *remaining)
    elif mutation == "edge_missing":
        node["edges"] = tuple(remaining)
    elif mutation == "expected_missing":
        node["expected"] = ()
    else:
        node["edges"] = (replace(edge, target_version="wrong-frozen-set"), *remaining)
    changed = replace(original, nodes=original.nodes[:index] + (node,) + original.nodes[index + 1:])
    prover = genuine._prover
    issued = prover._issued_program_certificate
    prover._issued_program_certificate = changed
    try:
        assert not changed.valid(prover, genuine._initial)
    finally:
        prover._issued_program_certificate = issued
