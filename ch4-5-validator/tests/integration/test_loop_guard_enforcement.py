#!/usr/bin/env python3
"""§6 结构守卫 enforcement 的验收测试（docs/循环处理增强方案.md §6）。

守卫的**判据**在 `verification/loop_pairing.analyze_program_pair`，由
`tests/unit/test_loop_pairing.py` 覆盖；这里验的是**接线**：

- 守卫开启时，判据判失败必须让 `verify_program_pair` 返回 False 并带上具体原因；
- 守卫必须跑在完整路径枚举**之前**（§6：它的输出决定 cutpoint 与 Tier 2 summary）；
- 守卫关闭（默认）时行为与接线前一致，但成功消息必须**声明未启用**，
  不能让读者把一条没查过循环结构的 VERIFIED 当成查过；
- `LoopGuardReport.notes()` 是信息性的，不影响结论但要留在报告里。
"""

from __future__ import annotations

import os

import pytest

from evm_ir.json_parser import CompilerEVMResult, load_ir_from_json
from evm_ir.models import EVMBlock, EvmOperator
from evm_ir.program import EVMProgram
from state.smt_state import SMTState
from verification.program_verifier import ProgramEquivalenceChecker
from x86_64.program import X86Program


_DATA_DIR = os.path.join(os.path.dirname(__file__), "..", "data")

# `jmp $`（自跳转，机器码 eb fe）：一条 x86 natural loop，循环头没有 TAG 序言 ⇒
# 不是 Tier 1 候选；指令序列也命不中任何已证 Tier 2 模板 ⇒ 落进 unpaired_x86。
# 用它而不是真实合约，是因为仓库里所有 fixture 都能通过守卫（实测 48/49），
# 拒绝路径没有现成素材。
X86_SELF_LOOP_HEX = "ebfe"

# `ret`：单块、无循环、无跳转，守卫无话可说的最小 x86 程序。
X86_TRIVIAL_HEX = "c3"


def _evm_block(pc: int, ops: list[EvmOperator]) -> EVMBlock:
    block = EVMBlock(
        pc=pc, stack_depth=0, min_depth=0, max_depth=1024, static_gas=0,
        is_jump_target=False, is_inner_block=False, is_stop=False,
    )
    block.operations = ops
    for op in ops:
        op.block = block
    return block


def _evm_stop_program() -> EVMProgram:
    """最小 EVM 程序：单块 STOP，无循环、无跳转。"""
    return EVMProgram(CompilerEVMResult([
        _evm_block(0, [EvmOperator(kind="STOP", pc=0)]),
    ]))


def _evm_dynamic_jump_program() -> EVMProgram:
    """带 dynamic_unresolved JUMP（既无 immediate 也无 immediate_set）的 EVM 程序。

    这种跳转会被编译成中央 jumpCode dispatcher，本项目不建模 ⇒ 守卫必须拒绝。
    """
    return EVMProgram(CompilerEVMResult([
        _evm_block(0, [EvmOperator(kind="JUMP", pc=0)]),
        _evm_block(10, [EvmOperator(kind="STOP", pc=10)]),
    ]))


def _load_fixture_pair(name: str) -> tuple[EVMProgram, X86Program]:
    evm_program = EVMProgram(load_ir_from_json(os.path.join(_DATA_DIR, f"{name}.json")))
    with open(os.path.join(_DATA_DIR, f"{name}.hex"), encoding="utf-8") as handle:
        x86_program = X86Program.from_hex(handle.read().strip(), base_addr=0)
    return evm_program, x86_program


# ---------------------------------------------------------------------------
# 守卫开启：必须 fail-closed
# ---------------------------------------------------------------------------


def test_unpaired_x86_loop_is_rejected_when_guard_enabled():
    """没有 Tier-1 配对、也没命中已证 Tier-2 引理的 x86 natural loop ⇒ 拒验。"""
    verified, msg = ProgramEquivalenceChecker().verify_program_pair(
        _evm_stop_program(),
        X86Program.from_hex(X86_SELF_LOOP_HEX, base_addr=0),
        SMTState.create_initial_state(),
        loop_guard=True,
    )

    assert not verified
    assert "LOOP GUARD REJECTED" in msg
    # 消息必须点名**具体原因**，而不是只说"守卫失败"——否则拿到结论的人无从下手
    assert "x86 natural loops without Tier-1 pair / Tier-2 lemma" in msg
    assert "0x0" in msg


def test_dynamic_unresolved_jump_is_rejected_when_guard_enabled():
    """IR 里出现 dynamic_unresolved JUMP（jumpCode dispatcher，不建模）⇒ 拒验。"""
    verified, msg = ProgramEquivalenceChecker().verify_program_pair(
        _evm_dynamic_jump_program(),
        X86Program.from_hex(X86_TRIVIAL_HEX, base_addr=0),
        SMTState.create_initial_state(),
        loop_guard=True,
    )

    assert not verified
    assert "LOOP GUARD REJECTED" in msg
    assert "dynamic_unresolved JUMP/JUMPI" in msg
    assert "pc=[0]" in msg


def test_guard_runs_before_any_path_enumeration(monkeypatch):
    """§6 要求守卫在完整路径枚举**之前**跑：拒绝时两侧都不该被符号执行过。

    顺序反了不会体现在结论上（照样拒绝），只会白跑一遍本不该展开的循环，
    并且让"守卫输出决定 cutpoint / Tier 2 summary"这条依赖失效——只有直接
    盯执行入口才守得住。
    """
    evm_program = _evm_stop_program()
    x86_program = X86Program.from_hex(X86_SELF_LOOP_HEX, base_addr=0)

    def _forbidden(*_args, **_kwargs):
        raise AssertionError("symbolic execution ran before the loop guard")

    for program in (evm_program, x86_program):
        monkeypatch.setattr(program, "to_z3", _forbidden, raising=False)
        monkeypatch.setattr(program, "to_z3_paths", _forbidden, raising=False)

    verified, msg = ProgramEquivalenceChecker().verify_program_pair(
        evm_program, x86_program, SMTState.create_initial_state(),
        loop_guard=True,
    )

    assert not verified
    assert "LOOP GUARD REJECTED" in msg


def test_guard_without_static_blocks_fails_closed():
    """守卫开着却拿不到静态块表 ⇒ 判据根本没机会作用，必须拒绝而不是放行。"""

    class _NoBlocks:
        """duck-typed 程序对象：没有 blocks / instructions。"""

    verified, msg = ProgramEquivalenceChecker().verify_program_pair(
        _evm_stop_program(),
        _NoBlocks(),
        SMTState.create_initial_state(),
        loop_guard=True,
    )

    assert not verified
    assert "LOOP GUARD UNAVAILABLE" in msg
    assert "fail-closed" in msg


def test_guard_reads_blocks_the_way_the_executor_does():
    """守卫必须按执行期口径取 x86 块表（from_hex 程序的 `.blocks` 恒为空）。

    这是接线里最容易 fail-open 的一处：只读 `x86_program.blocks` 的话，生产
    主用法（`X86Program.from_hex`）会让守卫永远"无块可查"，上面那些拒绝用例
    全都会变成 UNAVAILABLE 或（更糟）静默放行。
    """
    x86_program = X86Program.from_hex(X86_SELF_LOOP_HEX, base_addr=0)
    assert x86_program.blocks == [], "前提变了：from_hex 现在会填 blocks，本测试需重写"

    blocks = ProgramEquivalenceChecker._x86_static_blocks(x86_program)
    assert [block.start_addr for block in blocks] == [0]


# ---------------------------------------------------------------------------
# 守卫关闭（默认）：行为不变，但结论必须自曝其短
# ---------------------------------------------------------------------------


def test_guard_disabled_by_default_lets_rejected_pair_through():
    """守卫默认关闭：同一个会被守卫拒绝的程序对，默认路径下不因守卫失败。

    这里的 x86 自环会撞深度剪枝 → coverage 证书 incomplete → 照旧 fail-closed，
    但失败原因必须来自**原有**的覆盖检查，不是守卫。
    """
    verified, msg = ProgramEquivalenceChecker().verify_program_pair(
        _evm_stop_program(),
        X86Program.from_hex(X86_SELF_LOOP_HEX, base_addr=0),
        SMTState.create_initial_state(),
        max_depth=8,
    )

    assert not verified
    assert "LOOP GUARD" not in msg


def test_verified_message_declares_guard_not_enforced():
    """守卫关闭时的 VERIFIED 必须自曝"循环结构没查"，否则会被读成查过了。"""
    evm_program, x86_program = _load_fixture_pair("two_block")
    verified, msg = ProgramEquivalenceChecker(timeout_ms=600000).verify_program_pair(
        evm_program, x86_program, SMTState.create_initial_state(),
    )

    assert verified, msg
    assert "loop guard: NOT ENFORCED" in msg
    # 说清没查的是什么，而不是含糊一句"未启用"
    assert "x86 natural loops lacking a Tier-1 pair" in msg


def test_verified_message_declares_guard_enforced():
    """同一个程序对开着守卫也必须通过，且结论里换成"已启用"的措辞。"""
    evm_program, x86_program = _load_fixture_pair("two_block")
    verified, msg = ProgramEquivalenceChecker(timeout_ms=600000).verify_program_pair(
        evm_program, x86_program, SMTState.create_initial_state(),
        loop_guard=True,
    )

    assert verified, msg
    assert "loop guard: ENFORCED (structural)" in msg
    assert "NOT ENFORCED" not in msg
    # 措辞不得越界成"循环已被归纳证明"：证书消费端尚未落地（§9 路线图第 9 项）
    assert "not by induction certificates" in msg


# ---------------------------------------------------------------------------
# notes()：信息性，不影响结论，但要保留在报告里
# ---------------------------------------------------------------------------

_CERC20 = os.path.join(_DATA_DIR, "ext_contracts", "compound_cerc20", "CErc20")


@pytest.mark.skipif(not os.path.exists(_CERC20 + ".hex"), reason="CErc20 fixture missing")
def test_guard_passes_cerc20_and_keeps_informational_notes():
    """CErc20：守卫通过（9 Tier-1 配对 + 全部 Tier 2 命中已证引理），

    且 `immediate_set` 过近似造成的残环作为 note 保留——它是"守卫为什么放行"
    的旁证，被吞掉的话报告就只剩一句结论。
    """
    evm_program, x86_program = (
        EVMProgram(load_ir_from_json(_CERC20 + ".json")),
        X86Program.from_hex(open(_CERC20 + ".hex", encoding="utf-8").read().strip()),
    )

    outcome = ProgramEquivalenceChecker()._evaluate_loop_guard(
        evm_program, x86_program, enabled=True,
    )

    assert outcome.failure is None
    assert outcome.enforced
    notes = [line for line in outcome.lines if "loop guard note:" in line]
    assert any("residual cycles" in note for note in notes), outcome.lines
