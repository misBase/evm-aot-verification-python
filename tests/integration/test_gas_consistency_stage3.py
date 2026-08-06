"""阶段3 gas 一致性:status code 终态等价（3A）。

EVM 派生 status（终止类型 STOP→2/RETURN→0/REVERT→1，映射 aot_profile.status_codes）
与 x86 callengine_status_code 逐终止路径一致；status 与 gas 同属 gas 验证维度，
gas_check != OFF 时一并检查。

OOG 路径部分用 GasCheck.FULL（符号 gas）：block 入口在 gas<static 时分叉 OOG 终止路径
（status=12），与 x86 逐路径配对（见 test_oog_*）。FIXED_BUDGET 的具体预算会把这些
常量成本的 OOG 条件在 simplify 阶段折死，验不到。
"""

import os

import pytest

from verification.program_verifier import GasCheck, ProgramEquivalenceChecker
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
    """终止路径 status code 两侧一致（gas_check=GasCheck.FIXED_BUDGET 一并验 gas+status）。"""
    evm, x86 = _load_pair(name)
    verified, msg = ProgramEquivalenceChecker(
        timeout_ms=180000, gas_check=GasCheck.FIXED_BUDGET
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(), stack_check=None
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
        timeout_ms=120000, gas_check=GasCheck.FIXED_BUDGET
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(), stack_check=None
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
    """FULL 下 OOG 分叉可行,EVM/x86 各产生正常(status 2)+OOG(status 12) 路径,
    逐路径 status code 一致。add_with_push 单 block(只 block 入口 static gas)。"""
    evm, x86 = _load_add_with_push()
    verified, msg = ProgramEquivalenceChecker(
        timeout_ms=180000, gas_check=GasCheck.FULL
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(symbolic_gas=True),
        stack_check=None, path_observations=True,
    )
    assert verified, f"OOG path status consistency should hold, got: {msg}"


def test_oog_tampered_status_caught(monkeypatch):
    """防假绿:FULL 下篡改 EVM 正常路径 status(STOP STOPPED→GAS_UINT_OVERFLOW(13))→ SAT。"""
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
        timeout_ms=120000, gas_check=GasCheck.FULL
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(symbolic_gas=True),
        stack_check=None, path_observations=True,
    )
    assert not verified and "status" in msg.lower()


# --- 动态 gas 的 OOG 路径一致性（E4）---
#
# 这批 fixture 含可见的内存扩展/word gas。IR 侧现在会在 dynamicCost > 剩余 gas 时
# 分叉一条 OUT_OF_GAS 终态（镜像 x86 makeUseGas 的 JCS，gas_dynamic_amd64.go:402-408），
# 于是两侧的动态 OOG 路径可以逐路径比状态码。此前 IR 侧只是钳零续跑、不分叉，
# 这些用例在 FULL 下必然报 mismatch。
#
# 注意只有 GasCheck.FULL 能验到它：FIXED_BUDGET 的具体预算会把这些常量 fee 的 OOG
# 条件在 simplify 阶段折成 False，路径根本不建。
@pytest.mark.parametrize("name", [
    "gas_mload",     # 内存扩展（pureMemoryGascost）
    "gas_mstore8",   # 内存扩展，access_size=1
    "gas_revert",    # 内存扩展，calcMemSize64(offset, length)
    "gas_sha3",      # 内存扩展 + Sha3WordGas
    "gas_codecopy",  # 内存扩展 + CopyGas
    "gas_mcopy",     # max(dst,src) + CopyGas
    "gas_log1",      # 内存扩展 + LogGas + TopicGas + 每字节 LogDataGas
])
def test_dynamic_oog_path_status_consistency(name):
    evm, x86 = _load_pair(name)
    verified, msg = ProgramEquivalenceChecker(
        timeout_ms=180000, gas_check=GasCheck.FULL
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(symbolic_gas=True),
        stack_check=None, path_observations=True,
    )
    assert verified, f"{name} 动态 OOG 路径状态码应一致，got: {msg}"


def test_dynamic_oog_tampered_status_caught(monkeypatch):
    """防假绿：把 E4 分支的状态码从 OUT_OF_GAS(12) 篡改成 GAS_UINT_OVERFLOW(13) → SAT。

    这两个码在 gas 语义里是真实区分的：memorySize 阶段的溢出给 13，而
    dynamicGas 阶段（含 UseGas 失败与 memoryGasCost 的 cap）经
    interpreter.go:204-205 塌缩成 12。搞混了必须被抓到。
    """
    import dataclasses

    import evm_ir.semantics_gas as gas_sem
    from evm_ir.status_code import EvmStatusCode

    orig = gas_sem.charge_dynamic_gas

    def patched(state, requested, branches, extra_fees=(), **kwargs):
        out = orig(state, requested, branches, extra_fees, **kwargs)
        if out.pending_errors:
            last = out.pending_errors[-1]
            if last.status_code == EvmStatusCode.OUT_OF_GAS:
                out.pending_errors[-1] = dataclasses.replace(
                    last, status_code=EvmStatusCode.GAS_UINT_OVERFLOW
                )
        return out

    monkeypatch.setattr(gas_sem, "charge_dynamic_gas", patched)
    evm, x86 = _load_pair("gas_mload")
    verified, msg = ProgramEquivalenceChecker(
        timeout_ms=180000, gas_check=GasCheck.FULL
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(symbolic_gas=True),
        stack_check=None, path_observations=True,
    )
    assert not verified and "status" in msg.lower(), (
        f"E4 状态码 12→13 的篡改必须被抓到，got verified={verified} msg={msg}"
    )


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
        st = SMTState.create_initial_state()
        _, res = evm.to_z3(st)
        s = res.get("status_code")
        assert s is not None and is_bv(s), (
            f"{name} merged status must be a BitVec If-chain, got {s!r}"
        )


def test_full_rejects_unmodeled_dynamic_gas(monkeypatch):
    """FULL 也要走 unsupported-dynamic-gas guard，否则 OOG 一致性被
    放大到未建模指令 → 假绿/误报。

    allowlist 的差集当前为空（登记的动态 gas 指令全部已建模），所以这里把 CREATE 从
    已建模集里临时摘掉来触发 guard——验的是「guard 在 FULL 下同样生效」这条性质，
    而不是 CREATE 本身的状态（它已放行，见 test_gas_consistency_host_uf.py）。"""
    import verification.program_verifier as pv
    monkeypatch.setattr(
        pv, "_MODELED_DYNAMIC_GAS_KINDS", pv._MODELED_DYNAMIC_GAS_KINDS - {"CREATE"}
    )

    from evm_ir.json_parser import CompilerEVMResult
    from evm_ir.models import EVMBlock, EvmOperator
    block = EVMBlock(pc=0, stack_depth=0, min_depth=0, max_depth=1024,
                     static_gas=3, is_jump_target=False, is_inner_block=False,
                     is_stop=False)
    block.operations = [
        EvmOperator(kind=k, pc=i, block=block)
        for i, k in enumerate(["TAG", "CREATE", "STOP"])
    ]
    evm = EVMProgram(CompilerEVMResult([block]))
    verified, message = ProgramEquivalenceChecker(gas_check=GasCheck.FULL).verify_program_pair(
        evm, object(), SMTState.create_initial_state(symbolic_gas=True),
    )
    assert not verified
    assert "outside the currently provable gas scope" in message


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

    # OOG 分叉无条件建模，不需要开关；符号 gas 是让它成为可行路径的前提
    # （具体预算会把 ULT(budget, static_gas) 折成 False，分支根本不建）。
    st = SMTState.create_initial_state(symbolic_gas=True)
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
        "符号 gas 下应当分叉出一条 OUT_OF_GAS 终止路径"
    )


def test_status_check_parallel_workers_cross_context():
    """Fix#6:并行 path_pair_workers>1 时，EVM 单路径 status(Python int)与 worker
    私有 context 的 x86 status 比较，BitVecVal 必须建在 x86_status 的 context，
    否则跨 context 混用触发 z3 错误。用 gas_mload + path_pair_workers=2 触发。"""
    evm, x86 = _load_pair("gas_mload")
    verified, msg = ProgramEquivalenceChecker(
        timeout_ms=180000, gas_check=GasCheck.FIXED_BUDGET
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(),
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

@pytest.mark.parametrize("mode", [GasCheck.FIXED_BUDGET, GasCheck.FULL])
def test_host_dynamic_gas_ops_allowed_in_both_gas_modes(mode):
    """host 指令（HOST_GAS_UF_KINDS）在**两个** gas 模式下都放行，两侧 host UF 相消。

    FULL 曾把整个 HOST_GAS_UF_KINDS 纳入拒绝集，理由是"host 动态 OOG 两侧没验，放行即
    假绿"——不成立：host gas 耗尽后的终止没有生成代码，没有 x86 行为可以不一致
    （见 state/host_gas.py 模块 docstring）。它实际只防"把 FULL 的 VERIFIED 读成*所有*
    OOG 都验过"，而那一层由成功消息的范围声明承担（下面对 FULL 的断言即钉住这点）。

    用 gas_sload（PUSH 7 → SLOAD → STOP）。"""
    evm, x86 = _load_pair("gas_sload")
    initial_state = SMTState.create_initial_state(
        symbolic_gas=mode is GasCheck.FULL
    )
    verified, message = ProgramEquivalenceChecker(
        timeout_ms=180000, gas_check=mode
    ).verify_program_pair(evm, x86, initial_state, stack_check=None)
    assert verified, f"{mode} should verify gas_sload, got: {message}"
    if mode is GasCheck.FULL:
        # 替代旧拒绝的"别把结论读过头"守卫：范围必须写在消息里，不靠文档口头声明。
        assert "over all initial gas values" in message, message
        assert "NOT proven here" in message, message
        assert "host-exhaustion termination" in message, message


def test_fixed_budget_rejects_symbolic_gas():
    """FIXED_BUDGET + 符号 gas 必须 fail-closed。

    符号 gas 下每个 block 的 OOG 分支都保持可行，该模式承诺的路径规模不再成立；
    要对所有初始 gas 量化应当改用 GasCheck.FULL。
    """
    evm, x86 = _load_pair("gas_sload")
    verified, msg = ProgramEquivalenceChecker(
        timeout_ms=120000, gas_check=GasCheck.FIXED_BUDGET
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(symbolic_gas=True), stack_check=None,
    )
    assert not verified, "FIXED_BUDGET + 符号 gas 必须被拒"
    assert "concrete initial gas budget" in msg, f"错误信息应指明缺具体预算，got: {msg}"


def test_fixed_budget_honours_explicit_budget():
    """--gas-budget 一路透传：换一个具体预算，结论仍成立且仍是单点结论。"""
    evm, x86 = _load_pair("gas_sload")
    verified, msg = ProgramEquivalenceChecker(
        timeout_ms=120000, gas_check=GasCheck.FIXED_BUDGET
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(gas_budget=50_000), stack_check=None,
    )
    assert verified, f"gas_sload 在预算 50000 下应通过，got: {msg}"


def test_check_gas_forces_host_gas_uf_on():
    """verifier 自己置位 host_gas_uf_enabled，不依赖调用方经 factory 间接打开。

    即使调用方显式关掉它，gas_check != OFF 时也必须重新打开——否则 host gas 整段被
    跳过而结论照常是 VERIFIED。
    """
    evm, x86 = _load_pair("gas_sload")
    state = SMTState.create_initial_state()
    state.host_gas_uf_enabled = False          # 调用方手动关掉
    verified, msg = ProgramEquivalenceChecker(
        timeout_ms=120000, gas_check=GasCheck.FIXED_BUDGET
    ).verify_program_pair(evm, x86, state, stack_check=None)

    assert state.host_gas_uf_enabled, "verifier 必须把 host gas UF 重新打开"
    assert verified, f"重新打开后 gas_sload 应通过，got: {msg}"


def test_full_rejects_concrete_gas():
    """FULL + 具体 gas 必须 fail-closed。

    具体预算会把 ULT(budget, static_gas) 折成 False、所有 OOG 分叉被剪 —— OOG 一致性
    根本没验却返回 VERIFIED（假绿）。要用具体预算请改 GasCheck.FIXED_BUDGET。
    """
    evm, x86 = _load_add_with_push()
    verified, message = ProgramEquivalenceChecker(
        timeout_ms=120000, gas_check=GasCheck.FULL
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(),   # 具体预算
        stack_check=None, path_observations=True,
    )
    assert not verified, (
        f"FULL with a concrete gas budget must fail-closed, got VERIFIED: {message}"
    )
    assert "requires symbolic gas" in message


def test_full_rejects_gas_that_simplifies_to_a_constant():
    """`is_bv_value` 只看语法形式：`BitVecVal(1,64)+BitVecVal(2,64)` 语义上就是 3 却
    返回 False。不先 simplify 的话 FULL 会把这种"语义具体"的 gas 当符号量接受，
    实际只验了单点却声称量化所有初始 gas。"""
    from z3 import BitVecVal
    from state.evm_gas_state import EVMGasState

    evm, x86 = _load_add_with_push()
    state = SMTState.create_initial_state()
    folded = BitVecVal(1, 64) + BitVecVal(2, 64)
    state.evm_gas = EVMGasState(initial_gas=folded)
    state.callengine_gas_remaining = folded

    verified, message = ProgramEquivalenceChecker(
        timeout_ms=120000, gas_check=GasCheck.FULL
    ).verify_program_pair(evm, x86, state, stack_check=None)
    assert not verified, "可化简为常量的 gas 必须被 FULL 拒绝"
    assert "simplifies to the constant" in message


def test_fixed_budget_accepts_gas_that_simplifies_to_a_constant():
    """同一个表达式在 FIXED_BUDGET 下应被规范化后接受（预算 = 3 会让程序 OOG，
    这里只断言不被 gas 配置校验拦下）。"""
    from z3 import BitVecVal
    from state.evm_gas_state import EVMGasState

    evm, x86 = _load_add_with_push()
    state = SMTState.create_initial_state()
    folded = BitVecVal(1_000_000, 64) + BitVecVal(2, 64)
    state.evm_gas = EVMGasState(initial_gas=folded)
    state.callengine_gas_remaining = folded

    verified, message = ProgramEquivalenceChecker(
        timeout_ms=120000, gas_check=GasCheck.FIXED_BUDGET
    ).verify_program_pair(evm, x86, state, stack_check=None)
    assert "GAS CHECK UNSUPPORTED" not in (message or ""), message
    assert verified, message
    assert "fixed initial budget 1000002" in message, (
        f"成功消息必须带上规范化后的预算，got: {message}"
    )


def test_mismatched_initial_gas_between_sides_is_rejected():
    """IR 与 AOT 必须从同一个初始 gas 出发。调用方改了任一侧而模式校验只看 EVM 侧的话，
    比的就不是同一件事，却照常返回 VERIFIED。"""
    from z3 import BitVecVal

    evm, x86 = _load_pair("gas_sload")
    state = SMTState.create_initial_state()
    state.callengine_gas_remaining = BitVecVal(12345, 64)   # 只改 AOT 侧

    verified, message = ProgramEquivalenceChecker(
        timeout_ms=120000, gas_check=GasCheck.FIXED_BUDGET
    ).verify_program_pair(evm, x86, state, stack_check=None)
    assert not verified, "两侧初始 gas 不一致必须 fail-closed"
    assert "initial gas differs between the two sides" in message


def test_success_message_carries_gas_scope():
    """库调用方只有这个 message：必须能读出模式、预算与 host-OOG 不在范围内。"""
    evm, x86 = _load_pair("gas_sload")
    verified, message = ProgramEquivalenceChecker(
        timeout_ms=120000, gas_check=GasCheck.FIXED_BUDGET
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(gas_budget=777_000), stack_check=None,
    )
    assert verified, message
    assert "fixed initial budget 777000" in message
    assert "NOT proven here" in message
    assert "host-exhaustion termination" in message


def test_off_rejects_symbolic_gas():
    """GasCheck.OFF + 符号 gas 必须 fail-closed。

    OFF 下 host gas UF 是关的，两侧都不扣 host cost H。后续可见 gas 检查因此判的是
    `S > G` 而不是真实的 `S > G-H`，`S ≤ G < H+S` 这片真实可达的 OOG 区域被漏掉 ——
    符号 gas 下这是实打实的 under-approximation。具体预算把缺口压成空集。
    """
    evm, x86 = _load_pair("gas_sload")
    verified, msg = ProgramEquivalenceChecker(
        timeout_ms=120000, gas_check=GasCheck.OFF
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(symbolic_gas=True), stack_check=None,
    )
    assert not verified, "OFF + 符号 gas 必须被拒（host gas 未建模）"
    assert "GasCheck.OFF requires a concrete initial gas budget" in msg


def test_mismatched_initial_gas_rejected_in_every_mode():
    """两侧初始 gas 同源是**所有模式**的前提：gas 无条件参与控制流，起点不同就不是在比
    同一个输入程序，OFF 也不例外。"""
    from z3 import BitVecVal

    evm, x86 = _load_pair("gas_sload")
    for mode in (GasCheck.OFF, GasCheck.FIXED_BUDGET):
        state = SMTState.create_initial_state()
        state.callengine_gas_remaining = BitVecVal(4242, 64)   # 只改 AOT 侧
        verified, msg = ProgramEquivalenceChecker(
            timeout_ms=120000, gas_check=mode
        ).verify_program_pair(evm, x86, state, stack_check=None)
        assert not verified, f"{mode}: 两侧初始 gas 不一致必须 fail-closed"
        assert "initial gas differs between the two sides" in msg, mode


def test_off_still_verifies_with_concrete_budget():
    """对照：OFF + 具体预算（正常配置）不受上面两条守卫影响。"""
    evm, x86 = _load_pair("gas_sload")
    verified, msg = ProgramEquivalenceChecker(
        timeout_ms=120000, gas_check=GasCheck.OFF
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(), stack_check=None,
    )
    assert verified, msg


def test_off_success_message_discloses_unmodeled_host_gas():
    """OFF 的结论是**条件性**的，前提必须出现在每条 VERIFIED 消息里。

    OFF 刻意不建模 host gas（它是最便宜的功能等价筛查、根本不比较 gas），后续可见 gas
    检查判的是 `S > G` 而非 `S > G-H`；要求具体预算只关掉了符号 G 那类反例，
    `G=1e9, H=999999998, S=3` 仍是具体预算下的反例。调用方只有这条 message，不写前提
    就会把条件性结论读成无条件的，所以还要指出关缺口的出路（另两档）。
    """
    evm, x86 = _load_pair("gas_sload")
    verified, msg = ProgramEquivalenceChecker(
        timeout_ms=120000, gas_check=GasCheck.OFF
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(gas_budget=555_000), stack_check=None,
    )
    assert verified, msg
    assert "fixed initial gas budget 555000" in msg
    assert "host gas: NOT modeled in this mode" in msg
    assert "GasCheck.FIXED_BUDGET or FULL" in msg, "要给出关掉这个缺口的出路"


def _fixed_budget_message(name):
    evm, x86 = _load_pair(name)
    verified, msg = ProgramEquivalenceChecker(
        timeout_ms=120000, gas_check=GasCheck.FIXED_BUDGET
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(), stack_check=None,
    )
    assert verified, msg
    return msg


def test_gas_modes_do_not_overclaim_bounds():
    """比较 gas 的两档不能把"受上界约束"说成"按协议扣数"，且必须交代上界的外部前提。

    上界是对 go-hpc-evm **人工审计**得来的 assume，不是本验证器证出来的定理；而且没有
    任何机制核对被验产物是不是同一版编译器产出的（docs/关键问题记录.md #20）。这两点
    都得出现在结论里，否则调用方会把它读成"gas 已按协议验过"。
    """
    msg = _fixed_budget_message("gas_sload")

    assert "manually audited upper bounds" in msg
    assert "hand-synced" in msg, "必须交代上界是手工同步的"
    assert "nothing checks that" in msg, "必须交代没有机制核对编译器版本"
    assert "NOT proven here" in msg


def test_scope_message_names_unbounded_host_ops_present():
    """含无界 host op 的程序，结论必须**点名**它们没有上界。

    CALL/CREATE 系只扣无约束 UF（HOST_GAS_UNBOUNDED_KINDS）。笼统写"host gas 受上界
    约束"对这类程序是事实性过度声明——`gas_call` 就是反例，所以这条必须用它验，不能只
    用全都有界的 `gas_sload`。
    """
    msg = _fixed_budget_message("gas_call")

    assert "none exists for CALL" in msg, (
        f"含 CALL 的程序必须点名它无上界，实际消息：{msg}"
    )
    assert "unconstrained" in msg


def test_scope_message_says_so_when_everything_is_bounded():
    """反过来，全都有界的程序不该被扣上"有 opcode 没上界"的帽子。"""
    msg = _fixed_budget_message("gas_sload")

    assert "all bounded here" in msg
    assert "none exists for" not in msg
    assert "UNKNOWN" not in msg
