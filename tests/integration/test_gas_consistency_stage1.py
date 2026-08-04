"""阶段1 gas 一致性:内存扩展动态 gas 端到端（MSTORE + RETURN）。

mstore_return:单 block，MSTORE(offset=0) 扩内存到 32B 扣 gas，RETURN 同范围
不再扩容（lastGasCost 增量为 0）。验证 EVM 侧 memoryGasCost 建模与真实 x86
codegen(mul/mul/div + lastGasCost 增量)逐路径终值一致;div_bridge 让 Z3 收敛。
"""

import os

import pytest

from verification.program_verifier import GasCheck, ProgramEquivalenceChecker
from evm_ir.json_parser import load_ir_from_json
from evm_ir.program import EVMProgram
from x86_64.program import X86Program
from state.smt_state import SMTState


def _load_mstore_return_pair():
    test_dir = os.path.dirname(__file__)
    ir_path = os.path.join(test_dir, "..", "data", "mstore_return.json")
    hex_path = os.path.join(test_dir, "..", "data", "mstore_return.hex")
    evm_program = EVMProgram(load_ir_from_json(ir_path))
    x86_program = X86Program.from_hex(
        open(hex_path, encoding="utf-8").read().strip(), base_addr=0
    )
    return evm_program, x86_program


def test_mstore_return_memory_gas_consistency_passes():
    """MSTORE+RETURN 内存扩展动态 gas:EVM memoryGasCost == x86 mul/mul/div 链。"""
    evm_program, x86_program = _load_mstore_return_pair()

    checker = ProgramEquivalenceChecker(timeout_ms=120000, gas_check=GasCheck.FIXED_BUDGET)
    initial_state = SMTState.create_initial_state()
    verified, msg = checker.verify_program_pair(
        evm_program, x86_program, initial_state, stack_check=None
    )

    assert verified, f"memory expansion gas consistency should hold, got: {msg}"


def test_mstore_return_tampered_memory_gas_caught(monkeypatch):
    """防假绿:篡改 EVM 侧 MemoryGas 常量(3→9) → gas 检查必须 SAT。"""
    import state.evm_gas_state as gas_state
    monkeypatch.setattr(gas_state, "_MEMORY_GAS", 9)

    evm_program, x86_program = _load_mstore_return_pair()
    checker = ProgramEquivalenceChecker(timeout_ms=120000, gas_check=GasCheck.FIXED_BUDGET)
    initial_state = SMTState.create_initial_state()
    verified, msg = checker.verify_program_pair(
        evm_program, x86_program, initial_state, stack_check=None
    )

    assert not verified, "tampered MemoryGas must be caught (false green otherwise)"
    assert "gas" in msg.lower(), f"expected gas counterexample, got: {msg}"


def test_mstore_return_gas_check_off_unaffected():
    """check_gas 默认关时,mstore_return 功能等价不受 gas 建模影响(回归保护)。"""
    evm_program, x86_program = _load_mstore_return_pair()
    checker = ProgramEquivalenceChecker(timeout_ms=120000)  # check_gas 默认 False
    initial_state = SMTState.create_initial_state()  # symbolic_gas 默认 False
    verified, msg = checker.verify_program_pair(
        evm_program, x86_program, initial_state, stack_check=None
    )
    assert verified, f"functional equivalence should hold with gas off: {msg}"


def _load_pair(name):
    test_dir = os.path.dirname(__file__)
    ir_path = os.path.join(test_dir, "..", "data", f"{name}.json")
    hex_path = os.path.join(test_dir, "..", "data", f"{name}.hex")
    if not (os.path.exists(ir_path) and os.path.exists(hex_path)):
        pytest.skip(f"fixture {name} not generated (run Go TestGenGasFixtures)")
    evm = EVMProgram(load_ir_from_json(ir_path))
    x86 = X86Program.from_hex(open(hex_path, encoding="utf-8").read().strip(), base_addr=0)
    return evm, x86


def test_mload_memory_gas_consistency_passes():
    """纯 MLOAD 内存扩展动态 gas(gas_mload fixture,Go 编译器生成)。"""
    evm, x86 = _load_pair("gas_mload")
    verified, msg = ProgramEquivalenceChecker(
        timeout_ms=120000, gas_check=GasCheck.FIXED_BUDGET
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(), stack_check=None
    )
    assert verified, f"MLOAD memory gas consistency should hold, got: {msg}"


def test_mload_tampered_memory_gas_caught(monkeypatch):
    """防假绿:篡改 MemoryGas → gas_mload 应 SAT。"""
    import state.evm_gas_state as gas_state
    monkeypatch.setattr(gas_state, "_MEMORY_GAS", 9)
    evm, x86 = _load_pair("gas_mload")
    verified, msg = ProgramEquivalenceChecker(
        timeout_ms=120000, gas_check=GasCheck.FIXED_BUDGET
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(), stack_check=None
    )
    assert not verified and "gas" in msg.lower()


def test_sha3_word_gas_consistency_passes():
    """SHA3 内存扩展 + word gas(每 word 6)+ host bridge(gas_sha3 fixture)。"""
    evm, x86 = _load_pair("gas_sha3")
    verified, msg = ProgramEquivalenceChecker(
        timeout_ms=180000, gas_check=GasCheck.FIXED_BUDGET
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(), stack_check=None
    )
    assert verified, f"SHA3 word+memory gas consistency should hold, got: {msg}"


def test_sha3_tampered_word_gas_caught(monkeypatch):
    """防假绿:篡改 SHA3 word gas(6→9)→ gas_sha3 应 SAT。"""
    import state.evm_gas_state as gas_state
    orig = gas_state.word_fee
    monkeypatch.setattr(
        gas_state, "word_fee",
        lambda word_len, _const: orig(word_len, 9),
    )
    evm, x86 = _load_pair("gas_sha3")
    verified, msg = ProgramEquivalenceChecker(
        timeout_ms=180000, gas_check=GasCheck.FIXED_BUDGET
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(), stack_check=None
    )
    assert not verified and "gas" in msg.lower()


def test_calldatacopy_word_gas_consistency_passes():
    """CALLDATACOPY 内存扩展 + copy word gas(每 word 3)(gas_calldatacopy fixture)。"""
    evm, x86 = _load_pair("gas_calldatacopy")
    verified, msg = ProgramEquivalenceChecker(
        timeout_ms=180000, gas_check=GasCheck.FIXED_BUDGET
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(), stack_check=None
    )
    assert verified, f"CALLDATACOPY copy+memory gas consistency should hold, got: {msg}"


# 阶段 1d 全系列内存扩展动态 gas（Go 生成器 fixture）。
@pytest.mark.parametrize("name", [
    "gas_codecopy",    # 内存扩展 + copy word gas(3)
    "gas_mstore8",     # 内存扩展(access_size=1)
    "gas_revert",      # 内存扩展(仅, 同 RETURN)
    "gas_mcopy",       # 内存扩展 max(dst,src)+len + copy word gas(3)
])
def test_stage1d_memory_dynamic_gas_consistency(name):
    """逐指令内存扩展动态 gas 一致性(CODECOPY/MSTORE8/REVERT/MCOPY)。"""
    evm, x86 = _load_pair(name)
    verified, msg = ProgramEquivalenceChecker(
        timeout_ms=180000, gas_check=GasCheck.FIXED_BUDGET
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(), stack_check=None
    )
    assert verified, f"{name} memory gas consistency should hold, got: {msg}"


# --- A 类 LOG gas（内存扩展 + LogGas + n*TopicGas + size*DataGas，x86 全程可见）---

def test_log_gas_consistency_passes():
    """LOG1 动态 gas:EVM charge_log_gas == x86 memoryLogGas codegen 链。

    A 类真证明:LogGas(375)+TopicGas(375)+size*DataGas(8) + 内存扩展，全部在
    x86 checkMemoryAndCalcDynamicGasLog/memoryLogGas 机器码可见。"""
    evm, x86 = _load_pair("gas_log1")
    verified, msg = ProgramEquivalenceChecker(
        timeout_ms=180000, gas_check=GasCheck.FIXED_BUDGET
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(), stack_check=None
    )
    assert verified, f"LOG gas consistency should hold, got: {msg}"


def test_log_tampered_data_gas_caught(monkeypatch):
    """防假绿:篡改 LOG **每字节** data gas(8→99) → gas 检查必须 SAT。"""
    import state.evm_gas_state as gas_state
    monkeypatch.setattr(gas_state, "_LOG_DATA_GAS", 99)

    evm, x86 = _load_pair("gas_log1")
    verified, msg = ProgramEquivalenceChecker(
        timeout_ms=180000, gas_check=GasCheck.FIXED_BUDGET
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(), stack_check=None
    )
    assert not verified, "tampered LOG data gas must be caught (false green otherwise)"
    assert "gas" in msg.lower(), f"expected gas counterexample, got: {msg}"


def test_log_tampered_flat_gas_caught(monkeypatch):
    """防假绿:篡改 LOG 常量 gas(LogGas 375→111) → gas 检查必须 SAT。"""
    import state.evm_gas_state as gas_state
    monkeypatch.setattr(gas_state, "_LOG_GAS", 111)

    evm, x86 = _load_pair("gas_log1")
    verified, msg = ProgramEquivalenceChecker(
        timeout_ms=180000, gas_check=GasCheck.FIXED_BUDGET
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(), stack_check=None
    )
    assert not verified, "tampered LogGas must be caught (false green otherwise)"
    assert "gas" in msg.lower(), f"expected gas counterexample, got: {msg}"


def test_log_tampered_topic_gas_caught(monkeypatch):
    """防假绿:篡改 LOG 每 topic gas(TopicGas 375→111) → gas 检查必须 SAT。

    gas_log1 是 LOG1（1 个 topic），独立验证 n*TopicGas 项;_LOG_TOPIC_GAS 与
    _LOG_GAS 同为 375，单独篡改 TopicGas 可抓出把两者混淆/常量折叠的 bug。"""
    import state.evm_gas_state as gas_state
    monkeypatch.setattr(gas_state, "_LOG_TOPIC_GAS", 111)

    evm, x86 = _load_pair("gas_log1")
    verified, msg = ProgramEquivalenceChecker(
        timeout_ms=180000, gas_check=GasCheck.FIXED_BUDGET
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(), stack_check=None
    )
    assert not verified, "tampered LogTopicGas must be caught (false green otherwise)"
    assert "gas" in msg.lower(), f"expected gas counterexample, got: {msg}"


def test_log_gas_check_off_unaffected():
    """check_gas 默认关时,LOG 功能等价不受 gas 建模影响(回归保护)。"""
    evm, x86 = _load_pair("gas_log1")
    verified, msg = ProgramEquivalenceChecker(timeout_ms=180000).verify_program_pair(
        evm, x86, SMTState.create_initial_state(), stack_check=None
    )
    assert verified, f"functional equivalence should hold with gas off: {msg}"


# --- 并行 path_observations 模式回归（worker 私有 solver 未 reset → gas 假绿 bug）---

def test_memory_gas_parallel_pathobs_passes():
    """阶段1 内存扩展 gas 在并行 path_observations 模式下正确通过。"""
    evm, x86 = _load_pair("gas_mload")
    verified, msg = ProgramEquivalenceChecker(
        timeout_ms=180000, gas_check=GasCheck.FIXED_BUDGET
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(),
        stack_check=None, path_observations=True, path_pair_workers=2,
    )
    assert verified, f"MLOAD gas should verify in parallel mode, got: {msg}"


def test_memory_gas_parallel_pathobs_tamper_caught(monkeypatch):
    """**核心回归**:篡改内存 gas 常量后，并行 path_observations 模式**必须** SAT。

    曾有 bug:worker 私有 solver 在 gas 检查处不 reset，继承前序 memory 检查的累积
    UNSAT 断言 → gas 查询 vacuous UNSAT → 假绿。此测试覆盖既有 stage1 路径（非仅
    B 类 host UF），确保根因修复对所有 gas 检查生效。"""
    import state.evm_gas_state as gas_state
    monkeypatch.setattr(gas_state, "_MEMORY_GAS", 9)

    evm, x86 = _load_pair("gas_mload")
    verified, msg = ProgramEquivalenceChecker(
        timeout_ms=180000, gas_check=GasCheck.FIXED_BUDGET
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(),
        stack_check=None, path_observations=True, path_pair_workers=2,
    )
    assert not verified, "parallel-mode memory-gas mismatch must be caught (false green bug)"
    assert "gas" in msg.lower(), f"expected gas counterexample, got: {msg}"
