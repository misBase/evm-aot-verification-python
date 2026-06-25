"""阶段3 gas 一致性:status code 终态等价（3A）。

EVM 派生 status（终止类型 STOP→2/RETURN→0/REVERT→1，映射 aot_profile.status_codes）
与 x86 callengine_status_code 逐终止路径一致。check_gas=True 时一并检查（status 与
gas 同属 gas 验证维度，均需 symbolic_gas）。

3B（OOG 路径放开）:check_oog 模式下 EVM block 入口在 gas<static 时分叉 OOG
终止路径（status=12），与 x86 逐路径配对（见 test_oog_*）。仅 block 入口 OOG
已实现;含内存动态 gas 点的程序开 check_oog 会 fail-closed（SAT）。
"""

import os

import pytest

from verification.program_verifier import ProgramEquivalenceChecker
from evm_ir.json_parser import load_ir_from_json
from evm_ir.program import EVMProgram
from x86_64.program import X86Program
from state.smt_state import SMTState


def _load_pair(name):
    test_dir = os.path.dirname(__file__)
    ir_path = os.path.join(test_dir, "..", "data", f"{name}.json")
    hex_path = os.path.join(test_dir, "..", "data", f"{name}.hex")
    if not (os.path.exists(ir_path) and os.path.exists(hex_path)):
        pytest.skip(f"fixture {name} not generated (run Go TestGenGasFixtures)")
    evm = EVMProgram(load_ir_from_json(ir_path))
    x86 = X86Program.from_hex(open(hex_path, encoding="utf-8").read().strip(), base_addr=0)
    return evm, x86


@pytest.mark.parametrize("name,expected_status", [
    ("gas_mload", 2),   # 末尾 STOP → stopped(2)
    ("gas_sha3", 2),    # STOP
    ("gas_revert", 1),  # REVERT → reverted(1)
    ("gas_mstore8", 2),
    ("gas_codecopy", 2),
])
def test_status_code_consistency_passes(name, expected_status):
    """终止路径 status code 两侧一致（check_gas=True 一并验 gas+status）。"""
    evm, x86 = _load_pair(name)
    verified, msg = ProgramEquivalenceChecker(
        timeout_ms=180000, check_gas=True
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(symbolic_gas=True), stack_check=None
    )
    assert verified, f"{name} status code consistency should hold, got: {msg}"


def test_tampered_status_code_caught(monkeypatch):
    """防假绿:篡改 EVM 终止 status（STOP 2→9）→ status code 应 SAT。"""
    import evm_ir.semantics as sem
    orig = sem.evm_operator_to_z3

    def patched(op, state):
        r = orig(op, state)
        if op.kind.upper() == "STOP":
            r.termination_status = 9
        return r

    monkeypatch.setattr(sem, "evm_operator_to_z3", patched)

    evm, x86 = _load_pair("gas_mload")
    verified, msg = ProgramEquivalenceChecker(
        timeout_ms=120000, check_gas=True
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(symbolic_gas=True), stack_check=None
    )
    assert not verified, "tampered status must be caught"
    assert "status" in msg.lower(), f"expected status counterexample, got: {msg}"


# --- 3B: OOG 路径一致性 ---

def _load_add_with_push():
    from tests.integration.test_refinement_checker import (
        X86_ADD_FULL_HEX_SEQUENCE, X86_ADD_FULL_BASE_ADDR,
    )
    test_dir = os.path.dirname(__file__)
    ir_path = os.path.join(test_dir, "..", "data", "add_with_push.json")
    evm = EVMProgram(load_ir_from_json(ir_path))
    x86 = X86Program.from_hex(X86_ADD_FULL_HEX_SEQUENCE, base_addr=X86_ADD_FULL_BASE_ADDR)
    return evm, x86


def test_oog_path_status_consistency_passes():
    """3B:check_oog 放开 OOG 分叉,EVM/x86 各产生正常(status 2)+OOG(status 12)
    路径,逐路径 status code 一致。add_with_push 单 block(只 block 入口 static gas)。"""
    evm, x86 = _load_add_with_push()
    verified, msg = ProgramEquivalenceChecker(
        timeout_ms=180000, check_oog=True
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(symbolic_gas=True),
        stack_check=None, path_observations=True,
    )
    assert verified, f"OOG path status consistency should hold, got: {msg}"


def test_oog_tampered_status_caught(monkeypatch):
    """防假绿:check_oog 下篡改 EVM 正常路径 status(STOP 2→13)→ SAT。"""
    import evm_ir.semantics as sem
    orig = sem.evm_operator_to_z3

    def patched(op, state):
        r = orig(op, state)
        if op.kind.upper() == "STOP":
            r.termination_status = 13
        return r

    monkeypatch.setattr(sem, "evm_operator_to_z3", patched)
    evm, x86 = _load_add_with_push()
    verified, msg = ProgramEquivalenceChecker(
        timeout_ms=120000, check_oog=True
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(symbolic_gas=True),
        stack_check=None, path_observations=True,
    )
    assert not verified and "status" in msg.lower()


# --- Review 修复回归（防再退化）---

def test_merged_status_is_not_none_for_multipath():
    """Fix#1:多终止类型程序 merged status 必须是 BitVec（非 None），否则
    merged-result 模式下 status 检查被静默跳过（false green）。"""
    from z3 import is_bv
    test_dir = os.path.dirname(__file__)
    for name in ("jumpi_2block_ok", "muti_block"):
        p = os.path.join(test_dir, "..", "data", f"{name}.json")
        if not os.path.exists(p):
            continue
        evm = EVMProgram(load_ir_from_json(p))
        st = SMTState.create_initial_state(symbolic_gas=True)
        _, res = evm.to_z3(st)
        s = res.get("status")
        assert s is not None and is_bv(s), (
            f"{name} merged status must be a BitVec If-chain, got {s!r}"
        )


def test_check_oog_rejects_unmodeled_dynamic_gas():
    """Fix#3:check_oog 也要走 unsupported-dynamic-gas guard（含 EXP/SSTORE/CALL/
    LOG 等），否则 OOG 一致性被放大到未建模指令 → 假绿/误报。"""
    from evm_ir.json_parser import CompilerEVMResult
    from evm_ir.models import EVMBlock, EvmOperator
    block = EVMBlock(pc=0, stack_depth=0, min_depth=0, max_depth=1024,
                     static_gas=3, is_jump_target=False, is_inner_block=False,
                     is_stop=False)
    block.operations = [
        EvmOperator(kind=k, pc=i, block=block)
        for i, k in enumerate(["PUSH1", "EXP", "STOP"])
    ]
    evm = EVMProgram(CompilerEVMResult([block]))
    verified, message = ProgramEquivalenceChecker(check_oog=True).verify_program_pair(
        evm, object(), SMTState.create_initial_state(symbolic_gas=True),
    )
    assert not verified
    assert "dynamic gas operators are not modeled yet" in message


def test_status_check_parallel_workers_cross_context():
    """Fix#6:并行 path_pair_workers>1 时，EVM 单路径 status(Python int)与 worker
    私有 context 的 x86 status 比较，BitVecVal 必须建在 x86_status 的 context，
    否则跨 context 混用触发 z3 错误。用 gas_mload + path_pair_workers=2 触发。"""
    evm, x86 = _load_pair("gas_mload")
    verified, msg = ProgramEquivalenceChecker(
        timeout_ms=180000, check_gas=True
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(symbolic_gas=True),
        stack_check=None, path_observations=True, path_pair_workers=2,
    )
    assert verified, f"parallel-worker status check should hold, got: {msg}"


def test_evm_derived_status_matches_aot_profile_codes():
    """#10 防 codegen profile 漂移:EVM 派生 status 的硬编码值（semantics.py /
    cfg_executor.py）必须与 x86 aot_profile.status_codes 一致。若 Go codegen 改了
    status 数值而这里没跟，两侧会各用「自己的对值」漂移 → 假绿。此测试在漂移时
    失败提醒（EVM 语义层不直接 import aot_profile 以保持分层，靠此测试守护）。"""
    from x86_64.aot_profile import GO_HPC_EVM_PROFILE
    codes = GO_HPC_EVM_PROFILE.status_codes
    # 与 evm_ir/semantics.py + cfg_executor.py 里 termination_status 的硬编码对应
    assert codes["returned"] == 0
    assert codes["reverted"] == 1
    assert codes["stopped"] == 2
    assert codes["invalid"] == 3
    assert codes["out_of_gas"] == 12
