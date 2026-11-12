"""Use a real tiny parallel certificate; no presentation counter creates proof."""
import dataclasses
from pathlib import Path

import pytest

from tools.verify_block_lockstep import _final_report
from verification.block_parallel import ParallelProgramCertificate, verify_parallel


@pytest.fixture(scope="module")
def genuine(tmp_path_factory):
    options = dict(gas_check="full", gas_budget=1000000000, num_inputs=0, timeout_ms=3000,
        node_seconds=10, first_pass_node_seconds=10, node_memory_mb=512, max_depth=400,
        max_instances=64, max_parameter_values=32, wall_seconds=40,
        summaries=True, constant_insensitive=True,
        status_dir=str(tmp_path_factory.mktemp("hb5-parallel-status")))
    result = verify_parallel(str(Path("tests/data/two_block")), options, workers=1, pair_workers=1)
    assert result.verified, result.reasons
    assert isinstance(result.certificate, ParallelProgramCertificate)
    return result


def count_consumer(monkeypatch):
    calls = []
    original = ParallelProgramCertificate.valid
    def recording(self, prover, initial):
        calls.append(self)
        return original(self, prover, initial)
    monkeypatch.setattr(ParallelProgramCertificate, "valid", recording)
    return calls


def test_parallel_report_consumes_once_and_uses_actual_graph_shape(genuine, monkeypatch):
    calls = count_consumer(monkeypatch)
    certificate = genuine.certificate
    report = _final_report(genuine, 2)
    assert calls == [certificate]
    assert report["status"] == "verified"
    assert report["message"].startswith("VERIFIED: closed parallel block lockstep certificate")
    assert "independent full-program rerun" not in report["message"]
    proofs = {node["proof_spec"]:node for node in certificate.nodes}
    assert report["complete_local_theorems"] == len(proofs) > 0
    assert report["entry_certificates"] == 1
    assert report["edge_certificates"] == sum(len(node["edges"]) for node in certificate.nodes)
    assert report["node_seconds"] == [node["seconds"] for node in proofs.values()]
    assert "context H2" in report["node_seconds_basis"]


def test_parallel_lookalike_issuer_token_still_rejected(genuine, monkeypatch):
    calls = count_consumer(monkeypatch)
    issued = genuine.certificate
    genuine.certificate = dataclasses.replace(issued)
    try:
        report = _final_report(genuine, 2)
    finally:
        genuine.certificate = issued
    assert len(calls) == 1
    assert report["status"] == "inconclusive"
    assert report["complete_local_theorems"] == report["entry_certificates"] == report["edge_certificates"] == 0


def test_parallel_tampered_node_cannot_be_promoted_by_report(genuine, monkeypatch):
    calls = count_consumer(monkeypatch)
    node = genuine.certificate.nodes[0]
    original = node["proved"]
    node["proved"] = False
    try:
        report = _final_report(genuine, 2)
    finally:
        node["proved"] = original
    assert len(calls) == 1
    assert report["status"] == "inconclusive"
    assert report["complete_local_theorems"] == report["entry_certificates"] == report["edge_certificates"] == 0
