"""Failed row grouping leaves every member to its individual proof."""
from types import SimpleNamespace

from z3 import And, BitVec, BoolVal

from verification.block_equivalence import BlockEquivalenceProver, Obligation


def test_unproductive_row_groups_stop_without_discharging_members(monkeypatch):
    x = BitVec("stall_row", 64)
    evm = [SimpleNamespace(condition=And(*(x != k for k in range(64))))]
    x86 = [SimpleNamespace(condition=BoolVal(True)) for _ in range(10)]
    prover = BlockEquivalenceProver([], [], {})
    calls = []
    monkeypatch.setattr(prover, "_group_trial", lambda name, query, until: calls.append(name))
    done = {}
    prover._prove_row_groups(BoolVal(True), evm, x86, (0,) * 10, done, None)
    assert len(calls) == 4
    assert not done


def test_successful_group_resets_the_stall_count(monkeypatch):
    x = BitVec("stall_reset", 64)
    evm = [SimpleNamespace(condition=And(*(x != k for k in range(4))))]
    x86 = [SimpleNamespace(condition=BoolVal(True)) for _ in range(8)]
    prover = BlockEquivalenceProver([], [], {})
    calls = []

    def trial(name, query, until):
        calls.append(name)
        return Obligation(name, query.sexpr(), "unsat") if len(calls) == 3 else None

    monkeypatch.setattr(prover, "_group_trial", trial)
    done = {}
    prover._prove_row_groups(BoolVal(True), evm, x86, (0,) * 8, done, None)
    assert len(calls) == 7
    assert set(done) == {(2, k) for k in range(4)}
