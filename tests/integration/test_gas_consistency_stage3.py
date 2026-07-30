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
    """防假绿:篡改 EVM 终止 status（STOP STOPPED→INVALID_RETSUB(9)）→ status code 应 SAT。"""
    import evm_ir.semantics as sem
    from z3 import BitVecVal
    orig = sem.evm_operator_to_z3

    def patched(op, state):
        r = orig(op, state)
        if op.kind.upper() == "STOP":
            r.error_code = BitVecVal(9, 8)
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
    """防假绿:check_oog 下篡改 EVM 正常路径 status(STOP STOPPED→GAS_UINT_OVERFLOW(13))→ SAT。"""
    import evm_ir.semantics as sem
    from z3 import BitVecVal
    orig = sem.evm_operator_to_z3

    def patched(op, state):
        r = orig(op, state)
        if op.kind.upper() == "STOP":
            r.error_code = BitVecVal(13, 8)
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
        s = res.get("status_code")
        assert s is not None and is_bv(s), (
            f"{name} merged status must be a BitVec If-chain, got {s!r}"
        )


def test_check_oog_rejects_unmodeled_dynamic_gas():
    """Fix#3:check_oog 也要走 unsupported-dynamic-gas guard，否则 OOG 一致性被
    放大到未建模指令 → 假绿/误报。

    注意:EXP/SLOAD/CALL 等已转 host-gas UF 兜底、移出拒绝集；CREATE 仍 fail-closed
    （x86 可见内存扩展 + InitCodeWordGas 未对齐），用它验证 guard 仍生效。"""
    from evm_ir.json_parser import CompilerEVMResult
    from evm_ir.models import EVMBlock, EvmOperator
    block = EVMBlock(pc=0, stack_depth=0, min_depth=0, max_depth=1024,
                     static_gas=3, is_jump_target=False, is_inner_block=False,
                     is_stop=False)
    block.operations = [
        EvmOperator(kind=k, pc=i, block=block)
        for i, k in enumerate(["CREATE", "STOP"])
    ]
    evm = EVMProgram(CompilerEVMResult([block]))
    verified, message = ProgramEquivalenceChecker(check_oog=True).verify_program_pair(
        evm, object(), SMTState.create_initial_state(symbolic_gas=True),
    )
    assert not verified
    assert "dynamic gas operators are not modeled yet" in message


def test_oog_precedes_stack_underflow_in_tag_guard():
    """TAG 序言里 gas 检查必须先于栈深度检查，对齐 Go compileEVMTag：

        1. makeStaticUseGas → OUT_OF_GAS
        2. CMP MinDepth     → STACK_UNDERFLOW
        3. CMP MaxDepth+1   → STACK_REACHED_LIMIT

    构造一个 gas 不足**且**栈下溢的块（static_gas=100 而 SP=0 < min_depth=5）：
    两个错误条件同时成立，Go 侧先跳 OOG，所以 gas < static_gas 时状态码只能是
    OUT_OF_GAS。若哪天把 OOG 挪到栈检查之后（或忘了给 underflow 带上 ¬oog），
    这里会出现一条 gas<100 且 status=STACK_UNDERFLOW 的可满足路径而失败。
    """
    from z3 import Solver, ULT, BitVecVal, And, unsat
    from evm_ir.json_parser import CompilerEVMResult
    from evm_ir.models import EVMBlock, EvmOperator
    from evm_ir.status_code import EvmStatusCode

    block = EVMBlock(pc=0, stack_depth=0, min_depth=5, max_depth=1024,
                     static_gas=100, is_jump_target=False, is_inner_block=False,
                     is_stop=False)
    block.operations = [
        EvmOperator(kind="TAG", pc=0, block=block),
        EvmOperator(kind="STOP", pc=1, block=block),
    ]
    evm = EVMProgram(CompilerEVMResult([block]))

    st = SMTState.create_initial_state(symbolic_gas=True)
    st.oog_modeling_enabled = True
    st.gas_modeling_enabled = True
    gas = st.evm_gas.Gas

    semantics = evm.to_z3_paths(st, use_reachability_check=False)
    observations = semantics.observations
    assert observations, "TAG guard should produce terminal paths"

    gas_short = ULT(gas, BitVecVal(100, 64))
    underflow_code = BitVecVal(int(EvmStatusCode.STACK_UNDERFLOW), 8)

    # gas 不足时，任何一条路径都不允许报 STACK_UNDERFLOW。
    for obs in observations:
        solver = Solver()
        solver.add(And(gas_short, obs.condition, obs.status_code == underflow_code))
        assert solver.check() == unsat, (
            "gas < static_gas 时状态码必须是 OUT_OF_GAS，不能是 STACK_UNDERFLOW："
            "TAG 守卫的检查次序与 Go compileEVMTag 不一致"
        )

    # 反向：gas 不足确实产出了一条 OUT_OF_GAS 路径（否则上面的断言会因为
    # 根本没有可满足路径而空洞地通过）。
    oog_code = BitVecVal(int(EvmStatusCode.OUT_OF_GAS), 8)
    reachable = []
    for obs in observations:
        solver = Solver()
        solver.add(And(gas_short, obs.condition, obs.status_code == oog_code))
        reachable.append(solver.check())
    assert any(r != unsat for r in reachable), (
        "check_oog 下应当分叉出一条 OUT_OF_GAS 终止路径"
    )


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
    from evm_ir.status_code import EvmStatusCode
    codes = GO_HPC_EVM_PROFILE.status_codes
    # EVM 侧写入 error_code 用的是 EvmStatusCode（semantics.py / cfg_executor.py
    # 经 set_terminal_status），x86 侧从 aot_profile 读，两者必须同值。
    assert codes["returned"] == EvmStatusCode.RETURNED == 0
    assert codes["reverted"] == EvmStatusCode.REVERTED == 1
    assert codes["stopped"] == EvmStatusCode.STOPPED == 2
    assert codes["invalid"] == EvmStatusCode.INVALID == 3
    assert codes["out_of_gas"] == EvmStatusCode.OUT_OF_GAS == 12


# --- Branch-review fixes（合并前修复，防再退化）---

def test_check_oog_rejects_host_dynamic_gas_ops():
    """Fix #2:check_oog 模式下，host 动态 gas 指令（SLOAD/EXP/CALL 等）的
    **host 动态 OOG 分叉尚未建模**（host UF 只两侧钳零、继续执行，不分叉 OOG
    终止路径）。EVM 仅对 block 静态 gas 分叉 OOG，故这些指令的 host 动态 OOG
    一致性根本没验证；放行 = 假绿。check_oog 必须把 HOST_GAS_UF_KINDS 也纳入
    unsupported guard，fail-closed 拒绝。

    用 gas_sload（PUSH 7 → SLOAD → STOP）触发:修复前返回 VERIFIED（假绿），
    修复后必须被 guard 拒绝。"""
    evm, x86 = _load_pair("gas_sload")
    verified, message = ProgramEquivalenceChecker(
        timeout_ms=120000, check_oog=True
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(symbolic_gas=True),
        stack_check=None,
    )
    assert not verified, (
        "check_oog must reject SLOAD (host dynamic-gas OOG not modeled), "
        f"got VERIFIED: {message}"
    )
    assert "dynamic gas operators are not modeled yet" in message


def test_check_gas_still_allows_host_dynamic_gas_ops():
    """对照 Fix #2:check_gas（阶段 0，非 OOG）下 host 指令仍应放行（gas 恒足前提
    剪 OOG，host UF 相消即可）。确保 #2 的 OOG 拒绝不误伤 check_gas 通道。"""
    evm, x86 = _load_pair("gas_sload")
    verified, message = ProgramEquivalenceChecker(
        timeout_ms=180000, check_gas=True
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(symbolic_gas=True),
        stack_check=None,
    )
    assert verified, f"check_gas should still verify gas_sload, got: {message}"


def test_check_oog_requires_symbolic_gas():
    """Fix #4:check_oog 只设开关、不校验初始 gas 是否符号化。传默认
    create_initial_state()（gas 固定 1e9）会让 ULT(1e9, static_gas) 恒假、
    所有 OOG 分叉被剪，OOG 一致性根本没验却返回 VERIFIED（假绿）。

    check_oog 必须 fail-closed 要求 symbolic gas。"""
    evm, x86 = _load_add_with_push()
    verified, message = ProgramEquivalenceChecker(
        timeout_ms=120000, check_oog=True
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(),  # 默认非符号 gas
        stack_check=None, path_observations=True,
    )
    assert not verified, (
        "check_oog with concrete (non-symbolic) gas must fail-closed, "
        f"got VERIFIED: {message}"
    )
    assert "symbolic gas" in message.lower()
