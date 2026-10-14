"""Diagnostic keep-going mode: every pair-phase failure is reported, the node never proves.

Default (production) behavior is pinned too: the first failure stops the node.
"""
import inspect
import json
from pathlib import Path

import pytest
from z3 import And, BitVec, BoolVal, Not, ULT, UGE

import verification.block_equivalence as be
from tools.probe_block_obligations import build_prover, main, parse_nodes
from verification.block_equivalence import BlockEquivalenceProver, BlockTheorem, Obligation, pair_obligation_names

STEM = "tests/data/muti_block"
NODE = {"pc": 120, "stack_depth": 0, "memory_size": 96, "free_memory_pointer": 128}
BAD = {"pair_0_0", "pair_1_1"}  # the fixture node is a 2x2 full product: pair_0_0 .. pair_1_1


def _fail_pairs(monkeypatch, bad=BAD):
    """_check answers "sat" for the `bad` names (a counterexample); every call is logged."""
    real, checked = BlockEquivalenceProver._check, []

    def check(self, name, formula, records, **kw):
        checked.append(name)
        if name in bad:
            records.append(Obligation(name, formula.sexpr(), "sat", elapsed_seconds=0.25))
            return False
        return real(self, name, formula, records, **kw)
    monkeypatch.setattr(BlockEquivalenceProver, "_check", check)
    return checked


def _prove(keep_going):
    prover = build_prover(STEM, base_addr=0x1000, timeout_ms=10000, node_seconds=60, max_depth=400,
                          summaries=False, keep_going=keep_going)
    return prover.prove(parse_nodes([NODE])[0])


# --- prove(): the whole node ------------------------------------------------------------------

def test_keep_going_reports_both_failures_and_the_node_is_not_proved(monkeypatch):
    checked = _fail_pairs(monkeypatch)
    result = _prove(keep_going=True)
    assert not result.proved and result.status == "inconclusive" and result.theorem is None
    assert {"pair_0_0", "pair_0_1", "pair_1_0", "pair_1_1"} <= set(checked)  # every row was tried
    assert [f["name"] for f in result.kept_failures] == ["pair_0_0", "pair_1_1"]
    assert all(f["answer"] == "sat" and f["seconds"] == 0.25 for f in result.kept_failures)
    reason, = result.reasons
    assert "2 pair obligations, keep-going" in reason and "pair_0_0" in reason and "pair_1_1" in reason
    failed = {o.name: o.answer for o in result.obligations if not o.proved}
    assert failed == {"pair_0_0": "sat", "pair_1_1": "sat"}


def test_default_stops_at_the_first_failure(monkeypatch):
    checked = _fail_pairs(monkeypatch)
    result = _prove(keep_going=False)
    assert not result.proved and result.status == "inconclusive" and result.kept_failures == ()
    assert checked[-1] == "pair_0_0"  # nothing after the first failure is attempted
    assert not {"pair_0_1", "pair_1_0", "pair_1_1"} & set(checked)
    reason, = result.reasons
    assert reason.startswith("ValueError: outcome mismatch pair_0_0: ") and reason.endswith("(solver=sat)")


def test_kept_failures_survive_a_later_budget_abort(monkeypatch):
    real = BlockEquivalenceProver._check

    def check(self, name, formula, records, **kw):
        if name == "pair_0_0":
            records.append(Obligation(name, formula.sexpr(), "unknown", elapsed_seconds=0.5))
            return False
        if name == "pair_0_1":
            raise be.ProofBudgetExceeded("proof wall budget exhausted")
        return real(self, name, formula, records, **kw)
    monkeypatch.setattr(BlockEquivalenceProver, "_check", check)
    result = _prove(keep_going=True)
    assert not result.proved and [f["name"] for f in result.kept_failures] == ["pair_0_0"]
    reason, = result.reasons
    assert reason.startswith("ProofBudgetExceeded")


def test_keep_going_without_failures_still_proves(monkeypatch):
    result = _prove(keep_going=True)
    assert result.proved and result.kept_failures == () and not result.reasons


# --- _pair_phase: proposals and their degraded second round -----------------------------------

_BASE = ["entry_nonempty", "havoc_relation", "model_domain_nonempty", "evm_coverage", "x86_coverage",
         "evm_disjoint_0_1"]


def _node(row1, bad):
    """EVM 0: x < 10, EVM 1: x >= 10. Row 0 maps to 0, row 1 ("all") is proposed 0 by its
    sibling, row 2 maps to 1. Pairs in `bad` fail exactly when their joint is satisfiable."""
    from types import SimpleNamespace
    v = BitVec("kg_x", 8)
    p = lambda c, kind, loc: SimpleNamespace(condition=c, kind=kind, location=loc)
    evm = [p(ULT(v, 10), "exit", 0), p(UGE(v, 10), "terminal", None)]
    x86 = [p(ULT(v, 3), "exit", "A"), p(row1(v), "exit", "A"), p(UGE(v, 10), "terminal", None)]

    def pair(i, j):
        goal = BoolVal((i, j) not in bad)
        return f"pair_{i}_{j}", And(evm[i].condition, x86[j].condition, Not(goal)), f"{i}/{j}"
    return evm, x86, pair


def _pair_phase(keep_going, row1, bad):
    evm, x86, pair = _node(row1, bad)
    prover = BlockEquivalenceProver([], [], {}, timeout_ms=3000, keep_going=keep_going)
    records = [Obligation(name, "f", "unsat") for name in _BASE]
    corr = prover._pair_phase(evm, x86, BoolVal(True), pair, (0, "all", 1), records)
    required = tuple(_BASE[:5]) + tuple(pair_obligation_names(len(evm), len(x86), corr, be.map_arity(evm, corr)))
    theorem = BlockTheorem("id", None, tuple(records), required, "d", len(evm), len(x86), True,
                           correspondence=corr, arity=be.map_arity(evm, corr))
    return prover, records, theorem


def test_pair_phase_keep_going_collects_failures_of_both_rounds():
    # Row 0 fails in round 1; row 1's proposal fails (it lies in EVM 1), is degraded to "all"
    # and its pair_1_1 fails in round 2. Both are reported, the theorem stays incomplete.
    prover, records, theorem = _pair_phase(True, lambda v: And(UGE(v, 10), ULT(v, 20)), {(0, 0), (1, 1)})
    assert [f["name"] for f in prover._kept_failures] == ["pair_0_0", "pair_1_1"]
    assert all(f["answer"] == "sat" for f in prover._kept_failures)
    assert {"pair_0_0", "pair_1_1"} <= {r.name for r in records if not r.proved}
    assert not theorem.complete


def test_pair_phase_keep_going_with_pair_workers(monkeypatch):
    # Same node through the worker pool (_check_all's process path): same failures, same order.
    monkeypatch.setenv("BLOCK_PAIR_WORKERS", "2")
    be._reset_pair_pool()
    try:
        prover, records, theorem = _pair_phase(True, lambda v: And(UGE(v, 10), ULT(v, 20)), {(0, 0), (1, 1)})
        assert be._PAIR_POOL is not None  # the batch really went through worker processes
    finally:
        be._reset_pair_pool()
    assert [f["name"] for f in prover._kept_failures] == ["pair_0_0", "pair_1_1"] and not theorem.complete


def test_pair_phase_default_raises_at_the_first_failure():
    with pytest.raises(ValueError, match="outcome mismatch pair_0_0"):
        _pair_phase(False, lambda v: And(UGE(v, 10), ULT(v, 20)), {(0, 0), (1, 1)})


def test_tolerated_proposal_failure_is_not_a_kept_failure():
    # Only the proposal fails; its degraded row proves: the node proves even with keep_going.
    prover, records, theorem = _pair_phase(True, lambda v: And(UGE(v, 10), ULT(v, 20)), set())
    assert prover._kept_failures == [] and theorem.complete


# --- probe CLI ----------------------------------------------------------------------------------

def _cli(tmp_path, *extra):
    nodes, out = tmp_path / "nodes.json", tmp_path / "probe.json"
    nodes.write_text(json.dumps([NODE]))
    code = main([STEM, str(nodes), "--output", str(out), "--no-summaries", "--timeout-ms", "10000", *extra])
    return code, json.loads(out.read_text())


def test_cli_keep_going_lists_every_failure(tmp_path, monkeypatch):
    _fail_pairs(monkeypatch)
    code, report = _cli(tmp_path, "--keep-going")
    node, = report["nodes"]
    assert code == 1 and report["locally_proved"] == 0 and node["status"] == "inconclusive"
    assert [(f["name"], f["answer"], f["seconds"]) for f in node["keep_going_failures"]] == [
        ("pair_0_0", "sat", 0.25), ("pair_1_1", "sat", 0.25)]
    assert {f["name"] for f in node["failed_obligations"]} == BAD
    assert report["configuration"]["keep_going"] == "True"


def test_cli_environment_switch(tmp_path, monkeypatch):
    _fail_pairs(monkeypatch)
    monkeypatch.setenv("BLOCK_KEEP_GOING", "1")
    code, report = _cli(tmp_path)
    assert code == 1 and len(report["nodes"][0]["keep_going_failures"]) == 2


def test_cli_default_is_off(tmp_path, monkeypatch):
    checked = _fail_pairs(monkeypatch)
    monkeypatch.delenv("BLOCK_KEEP_GOING", raising=False)
    code, report = _cli(tmp_path)
    node, = report["nodes"]
    assert code == 1 and node["keep_going_failures"] == [] and report["configuration"]["keep_going"] == "False"
    assert [f["name"] for f in node["failed_obligations"]] == ["pair_0_0"] and "pair_1_1" not in checked


# --- production paths never enable it ------------------------------------------------------------

def test_production_never_enables_keep_going():
    assert inspect.signature(BlockEquivalenceProver).parameters["keep_going"].default is False
    assert BlockEquivalenceProver([], [], {}).keep_going is False
    for path in ("tools/verify_block_lockstep.py", "verification/block_parallel.py",
                 "verification/block_program.py"):
        source = Path(path).read_text()
        assert "keep_going" not in source and "KEEP_GOING" not in source, path
