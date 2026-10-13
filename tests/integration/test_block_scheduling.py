"""Worklist scheduling: discovery past failed nodes (A) and deferred retries (B).

Scheduling may change what gets explored and when, never what is certified.
"""
from verification import block_equivalence as be
from verification.block_program import BlockProgramVerifier
from tests.integration.test_block_program import load


def _entry_pc():
    evm, _, _ = load()
    return min(b.pc for b in evm.blocks)


def _patch_prove(monkeypatch, fail):
    """fail(spec, call_index) -> True forces that attempt to come back unproved (unknown)."""
    calls, original = [], be.BlockEquivalenceProver.prove

    def prove(self, spec):
        calls.append((spec, self.node_timeout_seconds))
        result = original(self, spec)
        if fail(spec, sum(1 for s, _ in calls if s == spec)):
            result.status, result.reasons, result._issuer = "inconclusive", ("forced (solver=unknown)",), None
        return result

    monkeypatch.setattr(be.BlockEquivalenceProver, "prove", prove)
    return calls


def test_baseline_explores_every_block_and_verifies():
    r = BlockProgramVerifier(timeout_ms=3000).verify_program_pair(*load())
    assert r.verified, r.message
    assert all(d["status"] == "proved" for d in r.diagnostics.values() if d["instances"])


def test_failed_entry_node_still_discovers_its_successors(monkeypatch):
    entry = _entry_pc()
    _patch_prove(monkeypatch, lambda spec, n: spec.pc == entry)
    r = BlockProgramVerifier(timeout_ms=3000).verify_program_pair(*load())
    assert not r.verified
    visited = {pc for pc, d in r.diagnostics.items() if d["instances"]}
    assert entry in visited and len(visited) > 1          # descendants were reached anyway
    assert any(f"local pc={entry}" in reason for reason in r.reasons)


def test_deferred_node_is_retried_with_the_full_budget(monkeypatch):
    entry = _entry_pc()
    calls = _patch_prove(monkeypatch, lambda spec, n: spec.pc == entry and n == 1)
    r = BlockProgramVerifier(timeout_ms=3000, node_timeout_seconds=60,
                             first_pass_node_seconds=5).verify_program_pair(*load())
    assert r.verified, r.message                           # the retry proved it
    budgets = [t for s, t in calls if s.pc == entry]
    assert budgets == [5, 60]
    assert calls[-1][0].pc == entry                        # retried after the queue drained
    assert all(t == 5 for s, t in calls if s.pc != entry)


def test_a_node_failing_twice_stays_a_failure(monkeypatch):
    entry = _entry_pc()
    calls = _patch_prove(monkeypatch, lambda spec, n: spec.pc == entry)
    r = BlockProgramVerifier(timeout_ms=3000, node_timeout_seconds=60,
                             first_pass_node_seconds=5).verify_program_pair(*load())
    assert not r.verified
    assert [t for s, t in calls if s.pc == entry] == [5, 60]
    statuses = [n["status"] for n in r.diagnostics[entry]["instances"]]
    assert statuses == ["inconclusive"]                    # the deferred record was replaced
