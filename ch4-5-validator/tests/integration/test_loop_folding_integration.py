#!/usr/bin/env python3
"""循环折叠接线的验收测试(docs/循环处理增强方案.md §4.7)。

折叠的**编排逻辑**在 `verification/loop_folding.py`,由 `tests/unit/test_loop_folding.py`
覆盖;这里验的是**接线**:

- `fold_loops` 与 merged-result 模式互斥,且必须显式拒绝而不是静默切换;
- 折叠计划不成立时,验证必须 fail-closed 并带上具体阻塞原因;
- 截断态落在证书适用域之外时必须拒绝——「执行确实停在 cutpoint 上」不等于「被覆盖」;
- 不启用折叠(默认)时行为与接线前完全一致。
"""

from __future__ import annotations

import dataclasses

import pytest

from evm_ir.json_parser import CompilerEVMResult
from evm_ir.models import EVMBlock, EvmOperator
from evm_ir.program import EVMProgram
from state.smt_state import SMTState
from verification import program_verifier as pv
from verification.loop_folding import FoldedLoop, FoldingPlan
from verification.program_verifier import ProgramEquivalenceChecker
from x86_64.program import X86Program

X86_TRIVIAL_HEX = "c3"  # ret:单块、无循环


def _evm_stop_program() -> EVMProgram:
    block = EVMBlock(
        pc=0, stack_depth=0, min_depth=0, max_depth=1024, static_gas=0,
        is_jump_target=False, is_inner_block=False, is_stop=False,
    )
    op = EvmOperator(kind="STOP", pc=0)
    block.operations = [op]
    op.block = block
    return EVMProgram(CompilerEVMResult([block]))


def _pair():
    return (
        _evm_stop_program(),
        X86Program.from_hex(X86_TRIVIAL_HEX, base_addr=0),
        SMTState.create_initial_state(),
    )


# ---------------------------------------------------------------------------
# 模式互斥
# ---------------------------------------------------------------------------

def test_fold_loops_requires_path_observations():
    """merged 模式把所有路径合成一个公式,截断态无处安放 ⇒ 显式拒绝。

    这里刻意**不**自动切到 path_observations:那会让调用方以为自己验的还是
    merged 语义。对比 gas 检查那处的自动切换——那是同一语义下的等价重写,
    这里不是。
    """
    evm, x86, state = _pair()
    verified, msg = ProgramEquivalenceChecker().verify_program_pair(
        evm, x86, state, path_observations=False, fold_loops=True,
    )
    assert not verified
    assert "LOOP FOLDING UNSUPPORTED" in msg
    assert "path_observations=True" in msg


# ---------------------------------------------------------------------------
# 折叠计划失败 ⇒ fail-closed
# ---------------------------------------------------------------------------

def test_failed_folding_plan_blocks_verification(monkeypatch):
    """有循环拿不到证书时不能"退回不折叠然后照常验过"——调用方显式要了折叠。"""
    monkeypatch.setattr(
        pv, "_format_verdict", pv._format_verdict, raising=False
    )
    from verification import loop_folding

    monkeypatch.setattr(
        loop_folding, "plan_loop_folding",
        lambda *a, **k: FoldingPlan(
            reasons=("loop evm=0x739: depth=2: base query inconclusive",)
        ),
    )
    evm, x86, state = _pair()
    verified, msg = ProgramEquivalenceChecker().verify_program_pair(
        evm, x86, state, path_observations=True, fold_loops=True,
    )
    assert not verified
    assert "LOOP FOLDING FAILED" in msg
    assert "base query inconclusive" in msg


# ---------------------------------------------------------------------------
# 截断态的适用域核对
# ---------------------------------------------------------------------------

class _Outcome:
    proved = True
    depth_classes = (2,)
    unmet_obligations = ()


def _plan_covering(evm_header: int, x86_header: int, depth_classes=(2,)):
    outcome = _Outcome()
    outcome.depth_classes = depth_classes
    return FoldingPlan(
        folded=(
            FoldedLoop(
                evm_header=evm_header, x86_header=x86_header,
                evm_exits=(99,), x86_exits=(0x99,), outcome=outcome,
            ),
        )
    )


def test_cut_state_outside_certified_depth_is_rejected(monkeypatch):
    """执行停在 cutpoint 上 ≠ 被证书覆盖:深度类对不上必须拒绝。

    证书按具体深度类实例化,落在未登记 class 上的到达状态不在任何定理的适用域
    内。放行等于把定理用到证明域之外——假绿方向。
    """
    from verification import loop_folding

    # 计划声称覆盖 pc=0 的循环、深度类只有 {2}
    monkeypatch.setattr(
        loop_folding, "plan_loop_folding",
        lambda *a, **k: _plan_covering(0, 0, depth_classes=(2,)),
    )

    # 让 EVM 侧"截断"在 pc=0、栈深 0 —— 不在已登记的 {2} 里
    class _Node:
        pc = 0

    class _CutState:
        node = _Node()

        def __init__(self, state):
            self.mstate = state

    real_to_z3_paths = EVMProgram.to_z3_paths

    def _fake(self, state, **kwargs):
        # PathSemantics 是 frozen dataclass（截断态一旦产出就不该被改写），
        # 所以造一个带 cut_states 的副本而不是就地赋值。
        result = real_to_z3_paths(self, state, **kwargs)
        return dataclasses.replace(result, cut_states=[_CutState(state)])

    monkeypatch.setattr(EVMProgram, "to_z3_paths", _fake)

    evm, x86, state = _pair()
    verified, msg = ProgramEquivalenceChecker().verify_program_pair(
        evm, x86, state, path_observations=True, fold_loops=True,
    )
    assert not verified
    assert "LOOP FOLDING FAILED" in msg
    assert "outside the certified classes" in msg


# ---------------------------------------------------------------------------
# 默认关闭
# ---------------------------------------------------------------------------

def test_folding_disabled_by_default_keeps_behaviour(monkeypatch):
    """不传 fold_loops 时不得触碰折叠编排——它是分钟级的证书生成开销。"""
    from verification import loop_folding

    def _boom(*a, **k):
        raise AssertionError("plan_loop_folding must not run when fold_loops=False")

    monkeypatch.setattr(loop_folding, "plan_loop_folding", _boom)
    evm, x86, state = _pair()
    # 断言的是 `_boom` 没被触发，而不是结论本身——这对最小程序两侧语义未必
    # 等价，拿 verified 当断言会把"折叠没被触碰"这件事和"程序等价"混在一起。
    ProgramEquivalenceChecker().verify_program_pair(
        evm, x86, state, path_observations=True,
    )
