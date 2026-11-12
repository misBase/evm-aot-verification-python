"""Producer dispatch: every node of a block with an instruction-chain hint is first tried by the legacy prover
within the first-pass budget; the attempt after a failed legacy one tries the chain first, then the legacy prover
with the rest of the budget. The scheduler decides per node (_attempt, _retry), not from the budget."""
import json
from hashlib import sha256
from types import SimpleNamespace

import pytest

from verification import block_parallel as bp
from verification import instruction_chain as ic
from verification.block_specialization import BlockSpecialization

SPEC = BlockSpecialization(7, 3, None, None, ())
OTHER = BlockSpecialization(8, 3, None, None, ())
FIRST, FULL = 300.0, 28800.0


def legacy_node(reasons=("legacy: not proved",)):
    return SimpleNamespace(proved=False, reasons=reasons, status="inconclusive", queries=1, obligations=[],
                           theorem=None)


@pytest.fixture
def worker(monkeypatch):
    """A worker whose legacy prover records the budget it was given, and a recording chain producer."""
    calls = dict(legacy=[], chain=[])
    prover = SimpleNamespace(instruction_hints={7: "hint-7"}, deadline=None, node_timeout_seconds=None)

    def prove(spec):
        calls["legacy"].append(prover.node_timeout_seconds)
        return legacy_node()
    prover.prove = prove
    monkeypatch.setattr(bp, "_WORKER", dict(setup=SimpleNamespace(prover=prover), identity="id", targets={}))
    monkeypatch.setattr(bp, "reset_node_caches", lambda p: None)
    outcome = {}

    def prove_node(prover_, spec, contexts, hint, targets, identity, seconds):
        calls["chain"].append(seconds)
        return outcome.get("chain")
    monkeypatch.setattr(ic, "prove_node", prove_node)
    return calls, outcome


def test_legacy_attempt_never_tries_the_chain(worker):
    calls, _ = worker
    node = bp._prove_instance(SPEC, FULL, 1e12, (SPEC,))          # even at the full budget: chain=False
    assert calls["chain"] == [] and calls["legacy"] == [FULL] and node["chain_attempt"] is None


def test_chain_attempt_returns_a_proved_chain(worker):
    calls, outcome = worker
    outcome["chain"] = dict(proved=True, reasons=(), proof_kind=ic.PROOF_KIND)
    node = bp._prove_instance(SPEC, FULL, 1e12, (SPEC,), True)
    assert node is outcome["chain"] and calls["chain"] == [min(FULL, ic.CHAIN_SECONDS)] and calls["legacy"] == []


@pytest.mark.parametrize("chain", [None, dict(proved=False, reasons=("op 3: solver=unknown",)),
                                   dict(proved=True, reasons=("H2 (0,0) not closed",))])
def test_chain_attempt_falls_back_to_legacy_with_the_rest(worker, chain):
    calls, outcome = worker
    outcome["chain"] = chain
    node = bp._prove_instance(SPEC, FULL, 1e12, (SPEC,), True)
    assert calls["chain"] and len(calls["legacy"]) == 1 and 0 < calls["legacy"][0] <= FULL
    assert node["chain_attempt"]["applicable"] is (chain is not None)
    assert node["chain_attempt"]["reasons"] == ([] if chain is None else list(chain["reasons"]))


def test_block_without_hint_never_tries_the_chain(worker):
    calls, _ = worker
    bp._prove_instance(OTHER, FULL, 1e12, (OTHER,), True)
    assert calls["chain"] == [] and calls["legacy"] == [FULL]


def test_attempt_legacy_first_then_chain():
    hinted = frozenset({7})
    # first attempt: legacy within the first-pass budget, even when released at the full budget (review z8g)
    assert bp._attempt(SPEC, FULL, FIRST, hinted, set(), set()) == (FIRST, False)
    assert bp._attempt(SPEC, FIRST, FIRST, hinted, set(), set()) == (FIRST, False)
    # after a legacy attempt: the chain, at the budget it was released at
    assert bp._attempt(SPEC, FULL, FIRST, hinted, {SPEC}, set()) == (FULL, True)
    # after both: legacy as scheduled
    assert bp._attempt(SPEC, FULL, FIRST, hinted, {SPEC}, {SPEC}) == (FULL, False)
    # no hint: exactly as scheduled
    assert bp._attempt(OTHER, FULL, FIRST, hinted, set(), set()) == (FULL, False)


def test_retry_rule():
    schedule = SimpleNamespace(full_start=set())
    node = dict(proved=False, status="inconclusive", reasons=("x",), memory_exceeded=None)
    hinted = frozenset({7})
    assert bp._retry(node, SPEC, schedule)
    assert not bp._retry(dict(node, reasons=("solver=sat",)), SPEC, schedule, hinted, {SPEC})
    stopped = dict(node, memory_exceeded="RSS over budget")
    assert not bp._retry(stopped, SPEC, schedule)                                   # legacy only
    assert bp._retry(stopped, SPEC, schedule, hinted, {SPEC})                       # the chain may take it
    full = SimpleNamespace(full_start={SPEC})
    assert not bp._retry(node, SPEC, full)                                          # already at the full budget
    assert bp._retry(node, SPEC, full, hinted, {SPEC})                              # ...but the chain is untried
    assert not bp._retry(node, SPEC, full, hinted, {SPEC}, {SPEC})                  # both tried


def test_full_trace_hints(tmp_path):
    code = b"\x90" * 8
    rows = [dict(block=7, pc=7, opcode="TAG", start=4096, end=4098, before=None, after=[]),
            dict(block=7, pc=8, opcode="PUSH", start=4098, end=4098, before=[],
                 after=[dict(index=-5, kind="register", register="AX")]),
            dict(block=9, pc=9, opcode="TAG", start=4098, end=4104, before=[], after=None)]
    trace = tmp_path / "trace.json"
    trace.write_text(json.dumps(dict(hex=code.hex(), rows=rows)))
    hints = ic.load_hints(trace, code)
    assert sorted(hints) == [7, 9] and [o.opcode for o in hints[7].ops] == ["TAG", "PUSH"]
    assert hints[7].ops[1].after == ((-5, -2, 3, "register", "AX", 0),)   # index -5: word -2, limb 3
    assert hints[7].code_sha256 == sha256(code).hexdigest()
    assert ic.load_hints(trace, b"\xcc") == {}                            # a trace of other code: no hints
