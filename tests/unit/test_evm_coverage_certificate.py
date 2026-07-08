#!/usr/bin/env python3
"""P0：EVM 侧 depth 剪枝计数与 terminal path coverage 证书测试。

对齐 x86 侧 `X86SymbolicExecutor.path_coverage_certificate()` 的 fail-closed
语义：策略层 depth 剪枝必须计数；executor 必须能产出证书；`to_z3_paths`
把证书挂到 PathSemantics；`to_z3`（merged 模式）把证书挂到 result dict，
修复 merged 模式被剪路径静默消失的盲点。
"""

from common.path_observation import PathCoverageCertificate
from evm_ir.cfg_state import GlobalState
from evm_ir.cfg_strategies import DFSStrategy
from evm_ir.json_parser import CompilerEVMResult
from evm_ir.models import EVMBlock, EvmOperator
from evm_ir.program import EVMProgram
from state.smt_state import SMTState


def _make_block(pc, ops, is_stop=False):
    block = EVMBlock(
        pc=pc,
        stack_depth=0,
        min_depth=0,
        max_depth=1024,
        static_gas=0,
        is_jump_target=False,
        is_inner_block=False,
        is_stop=is_stop,
        operations=ops,
    )
    for op in ops:
        op.block = block
    return block


def _stop_program() -> EVMProgram:
    stop = EvmOperator(kind="STOP", pc=0)
    return EVMProgram(CompilerEVMResult(blocks=[_make_block(0, [stop], is_stop=True)]))


def _self_loop_program() -> EVMProgram:
    """block 0 静态 JUMP 回自身：符号执行只能靠 depth 剪枝终止。"""
    jump = EvmOperator(kind="JUMP", pc=0, immediate=0, is_static=True)
    return EVMProgram(CompilerEVMResult(blocks=[_make_block(0, [jump])]))


def _tag_only_program() -> EVMProgram:
    """唯一块只含 TAG（过滤后无操作），fallthrough 越过末块被丢弃。"""
    tag = EvmOperator(kind="TAG", pc=0)
    return EVMProgram(CompilerEVMResult(blocks=[_make_block(0, [tag])]))


def test_dfs_strategy_counts_depth_pruned_states():
    state = SMTState.create_initial_state()
    gs = GlobalState(mstate=state, node=None)
    gs.depth = 5
    strategy = DFSStrategy([gs], max_depth=5)

    assert list(strategy) == []
    assert strategy.depth_pruned_count == 1


def test_loop_free_program_certificate_complete():
    paths = _stop_program().to_z3_paths(
        SMTState.create_initial_state(), merge_state=False
    )

    assert paths.coverage.complete
    assert paths.coverage.source == "evm-symbolic-executor"


def test_depth_pruned_loop_certificate_incomplete():
    paths = _self_loop_program().to_z3_paths(
        SMTState.create_initial_state(), merge_state=False, max_depth=10
    )

    assert not paths.coverage.complete
    assert "depth-pruned" in paths.coverage.reason


def test_fallthrough_off_end_marks_incomplete():
    paths = _tag_only_program().to_z3_paths(
        SMTState.create_initial_state(), merge_state=False
    )

    assert not paths.coverage.complete
    assert "fallthrough" in paths.coverage.reason


def test_to_z3_merged_result_carries_certificate():
    _, incomplete_result = _self_loop_program().to_z3(
        SMTState.create_initial_state(), max_depth=10
    )
    cert = incomplete_result["coverage"]
    assert isinstance(cert, PathCoverageCertificate)
    assert not cert.complete

    _, complete_result = _stop_program().to_z3(SMTState.create_initial_state())
    assert complete_result["coverage"].complete


def test_merged_coverage_failure_fail_closed():
    from verification.program_verifier import _merged_coverage_failure

    complete = {"coverage": PathCoverageCertificate.by_construction("ok")}
    incomplete = {
        "coverage": PathCoverageCertificate(
            complete=False, reason="depth-pruned state count: 3"
        )
    }
    missing = {}

    assert _merged_coverage_failure(complete, complete) is None

    msg = _merged_coverage_failure(incomplete, complete)
    assert msg is not None and "EVM" in msg and "depth-pruned" in msg

    msg = _merged_coverage_failure(complete, incomplete)
    assert msg is not None and "x86" in msg

    msg = _merged_coverage_failure(missing, complete)
    assert msg is not None and "no path coverage certificate" in msg
