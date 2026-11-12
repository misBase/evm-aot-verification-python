"""CLI 报告序列化：证书消费者只跑一次，且记录统计不得冒充证据。

守三件事：

1. **报告只消费一次完整证书** —— `result.verified` 会对每个节点重算
   `_proved_for_identity`（内含整程序 identity 与全路径 `paths_digest`），
   再调用 `result.message` 会整个重跑一遍，这正是 600s 软预算的运行在 660s
   硬墙上被打断在报告阶段的原因；
2. **伪造/篡改的证书拿不到 verified** —— 状态字段、诊断里的 `status=proved`
   都不是证据，只有被 prover 签发过的证书经消费者接受才算；
3. **硬超时保留既有局部失败详情**，同时把任何"已证"计数清零。
"""
import contextlib
import dataclasses
from pathlib import Path
from types import SimpleNamespace

import pytest

from tools.verify_block_lockstep import (
    _final_report,
    _interrupted_report,
    _message,
    _progress_report,
)

STEM = "tests/data/lockstep_counter_loop"


@contextlib.contextmanager
def counting():
    """统计证书消费者与逐节点定理检查的调用次数（两者都是重算，不是缓存查询）。"""
    from verification.block_equivalence import BlockProofResult
    from verification.block_program import ProgramCertificate

    counts = {"valid": 0, "node_checks": 0}
    original_valid = ProgramCertificate.valid
    original_node = BlockProofResult._proved_for_identity

    def valid(self, prover, initial):
        counts["valid"] += 1
        return original_valid(self, prover, initial)

    def node_check(self, identity):
        counts["node_checks"] += 1
        return original_node(self, identity)

    ProgramCertificate.valid = valid
    BlockProofResult._proved_for_identity = node_check
    try:
        yield counts
    finally:
        ProgramCertificate.valid = original_valid
        BlockProofResult._proved_for_identity = original_node


@pytest.fixture(scope="module")
def run():
    """真实 fixture 的一次完整块级验证，附带每次 progress 回调的重算增量。"""
    from evm_ir.json_parser import load_ir_from_json
    from evm_ir.program import EVMProgram
    from state.smt_state import SMTState
    from verification.block_program import BlockProgramVerifier
    from verification.program_verifier import GasCheck
    from x86_64.program import X86Program
    from x86_64.summaries import X86SummaryConfig

    evm = EVMProgram(load_ir_from_json(STEM + ".json"))
    x86 = X86Program.from_hex(Path(STEM + ".hex").read_text().strip(), base_addr=0x1000)
    state = SMTState.create_initial_state(num_inputs=0, symbolic_gas=True)
    state.assume_calldata_offset_no_overflow = False
    state.host_gas_uf_enabled = True
    config = X86SummaryConfig.enabled(calldataload="fallback", copy_loop="fallback", mul="fallback")

    deltas = []
    with counting() as counts:
        def progress(result):
            before = dict(counts)
            _progress_report(result)
            deltas.append({k: counts[k] - before[k] for k in counts})

        result = BlockProgramVerifier(
            gas_check=GasCheck.FULL, timeout_ms=3000, max_depth=400, max_instances=2048,
            wall_timeout_seconds=600, summary_config=config, node_timeout_seconds=30,
            fallback="none", progress_callback=progress).verify_program_pair(evm, x86, state)
    assert result.status == "verified", result.reasons
    return result, deltas, len(evm.blocks)


def test_verified_report_consumes_the_certificate_exactly_once(run):
    result, _, blocks = run
    with counting() as counts:
        report = _final_report(result, blocks)
    assert counts["valid"] == 1
    assert counts["node_checks"] == len(result.nodes)  # 一遍，不是两遍
    assert report["status"] == "verified"
    assert report["message"] == (
        f"VERIFIED: closed block lockstep certificate ({len(result.nodes)} instances). {result.scope}")
    assert report["complete_local_theorems"] == len(result.certificate.nodes)
    assert report["entry_certificates"] == 1
    assert report["edge_certificates"] == len(result.certificate.edges)
    assert report["attempted_instances"] == report["recorded_local_theorems"] == len(result.nodes)
    assert report["local_statistics_basis"] and "kind" not in report


def test_progress_reports_never_validate(run):
    _, deltas, _ = run
    assert deltas and all(d == {"valid": 0, "node_checks": 0} for d in deltas)


def test_tampered_node_is_rejected_and_still_validated_once(run):
    """改一条路径出口即破坏 outcome_digest：必须拒绝，且不因拒绝而重跑第二遍。"""
    result, _, blocks = run
    node = result.nodes[0]
    original = node.evm_outcomes
    node.evm_outcomes = original[:-1]
    try:
        with counting() as counts:
            report = _final_report(result, blocks)
    finally:
        node.evm_outcomes = original
    assert counts["valid"] == 1
    assert report["status"] == "inconclusive"
    assert report["message"].startswith("INCONCLUSIVE: incomplete certificate graph.")
    assert report["complete_local_theorems"] == 0
    assert report["entry_certificates"] == 0 and report["edge_certificates"] == 0
    # 诊断仍记着 proved：它是观测，不是证据。
    assert report["recorded_local_theorems"] == len(result.nodes)


def test_forged_lookalike_certificate_is_not_accepted(run):
    """字段完全相同但未被 prover 签发的证书不算证书。"""
    result, _, blocks = run
    genuine = result.certificate
    result.certificate = dataclasses.replace(genuine)
    try:
        report = _final_report(result, blocks)
    finally:
        result.certificate = genuine
    assert report["status"] == "inconclusive" and report["complete_local_theorems"] == 0
    assert report["entry_certificates"] == 0


def test_status_alone_is_not_a_certificate(run):
    result, _, blocks = run
    genuine = result.certificate
    result.certificate = None
    try:
        report = _final_report(result, blocks)
    finally:
        result.certificate = genuine
    assert result.status == "verified"
    assert report["status"] == "inconclusive" and report["complete_local_theorems"] == 0


def test_independent_rerun_keeps_its_own_wording():
    stub = SimpleNamespace(reasons=(), scope="scope", nodes=())
    assert _message(stub, True, None).startswith("VERIFIED: independent full-program rerun certificate")
    assert _message(stub, False, None) == "INCONCLUSIVE: incomplete certificate graph. scope"


def test_interrupted_report_keeps_local_failures_and_claims_nothing():
    latest = dict(kind="progress", status="inconclusive",
                  reasons=["local pc=792 BlockSpecialization(...): solver=unknown"],
                  diagnostics={"792": {"status": "inconclusive", "instances": [{"status": "proved"}]}},
                  timings={"local_theorems_and_discovery": 598.0},
                  attempted_instances=133, recorded_local_theorems=129,
                  complete_local_theorems=7, entry_certificates=1, edge_certificates=3)
    report = _interrupted_report(latest, "outer process wall budget exhausted; no certificate issued")
    assert report["reasons"] == [latest["reasons"][0],
                                 "outer process wall budget exhausted; no certificate issued"]
    assert report["diagnostics"] == latest["diagnostics"] and report["timings"] == latest["timings"]
    assert report["attempted_instances"] == 133 and report["recorded_local_theorems"] == 129
    assert report["complete_local_theorems"] == 0
    assert report["entry_certificates"] == 0 and report["edge_certificates"] == 0
    assert report["status"] == "inconclusive" and "local pc=792" in report["message"]
