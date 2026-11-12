"""Cache scheduling metadata; fake local theorem, no mathematical proof issued."""
import time
from types import SimpleNamespace

import pytest

from verification import block_parallel as bp, block_summaries as bs, proof_cache as pc
from verification.block_specialization import BlockSpecialization


@pytest.fixture(autouse=True)
def private_cache(monkeypatch, tmp_path):
    monkeypatch.setenv("BLOCK_PROOF_CACHE", str(tmp_path / "answers.sqlite3"))
    monkeypatch.setattr(pc, "_CONNECTIONS", {})
    monkeypatch.setattr(pc, "_LOCAL_UNKNOWN", {"owner": None, "budgets": {}})
    yield
    for connection in pc._CONNECTIONS.values():
        connection.close()


def worker(monkeypatch, prove):
    prover = SimpleNamespace(prove=prove, _lemma_cache={})
    monkeypatch.setattr(bp, "_WORKER", {"setup": SimpleNamespace(prover=prover), "identity": "metadata-only"})
    return BlockSpecialization(0, 0, 0, 0)


def unproved():
    return SimpleNamespace(proved=False, status="inconclusive", reasons=("synthetic UNKNOWN",),
                           theorem=None, queries=0, obligations=())


def attempt(spec):
    result = bp._prove_instance(spec, 10, time.time() + 30, (spec,))
    assert not result["proved"] and result["theorem"] is None and not result["edges"]
    return result


def test_unknown_is_retried_on_next_worker_attempt(monkeypatch):
    observations = []
    def prove(spec):
        observations.append(pc.cached_answer("same-query", 500))
        pc.record_answer("same-query", "unknown", 1000)
        assert pc.cached_answer("same-query", 500) == "unknown"
        return unproved()
    spec = worker(monkeypatch, prove)
    attempt(spec)
    attempt(spec)
    assert observations == [None, None]
    assert pc.lookup("same-query") == {"unknown": 1000}


@pytest.mark.parametrize("answer", ["sat", "unsat"])
def test_decided_answers_survive_attempt_boundary(monkeypatch, answer):
    pc.record_answer("decided", answer, 1000)
    def prove(spec):
        assert pc.cached_answer("decided", 500) == answer
        return unproved()
    spec = worker(monkeypatch, prove)
    attempt(spec)
    attempt(spec)
    assert pc.lookup("decided") == answer


def test_cold_summary_retry_remains_inside_the_same_attempt(monkeypatch):
    calls, spent = [], [0.0]
    monkeypatch.setattr(bs, "lemma_seconds", lambda: spent[0])
    def prove(spec):
        calls.append(pc.cached_answer("within-attempt", 500))
        pc.record_answer("within-attempt", "unknown", 1000)
        spent[0] = 2.0
        return unproved()
    spec = worker(monkeypatch, prove)
    attempt(spec)
    assert calls == [None, "unknown"]


def test_shared_unknown_from_another_process_is_not_trusted(monkeypatch):
    pc.store("foreign", {"unknown": 60000}, replace=True)
    def prove(spec):
        assert pc.cached_answer("foreign", 1000) is None
        return unproved()
    spec = worker(monkeypatch, prove)
    attempt(spec)
    assert pc.lookup("foreign") == {"unknown": 60000}
