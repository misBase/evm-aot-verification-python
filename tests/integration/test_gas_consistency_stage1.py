"""阶段1 gas 一致性:内存扩展动态 gas 端到端（MSTORE + RETURN）。

mstore_return:单 block，MSTORE(offset=0) 扩内存到 32B 扣 gas，RETURN 同范围
不再扩容（lastGasCost 增量为 0）。验证 EVM 侧 memoryGasCost 建模与真实 x86
codegen(mul/mul/div + lastGasCost 增量)逐路径终值一致;div_bridge 让 Z3 收敛。
"""

import os

import pytest

from verification.program_verifier import ProgramEquivalenceChecker
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

    checker = ProgramEquivalenceChecker(timeout_ms=120000, check_gas=True)
    initial_state = SMTState.create_initial_state(symbolic_gas=True)
    verified, msg = checker.verify_program_pair(
        evm_program, x86_program, initial_state, stack_check=None
    )

    assert verified, f"memory expansion gas consistency should hold, got: {msg}"


def test_mstore_return_tampered_memory_gas_caught(monkeypatch):
    """防假绿:篡改 EVM 侧 MemoryGas 常量(3→9) → gas 检查必须 SAT。"""
    import state.evm_gas_state as gas_state
    monkeypatch.setattr(gas_state, "_MEMORY_GAS", 9)

    evm_program, x86_program = _load_mstore_return_pair()
    checker = ProgramEquivalenceChecker(timeout_ms=120000, check_gas=True)
    initial_state = SMTState.create_initial_state(symbolic_gas=True)
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
        timeout_ms=120000, check_gas=True
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(symbolic_gas=True), stack_check=None
    )
    assert verified, f"MLOAD memory gas consistency should hold, got: {msg}"


def test_mload_tampered_memory_gas_caught(monkeypatch):
    """防假绿:篡改 MemoryGas → gas_mload 应 SAT。"""
    import state.evm_gas_state as gas_state
    monkeypatch.setattr(gas_state, "_MEMORY_GAS", 9)
    evm, x86 = _load_pair("gas_mload")
    verified, msg = ProgramEquivalenceChecker(
        timeout_ms=120000, check_gas=True
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(symbolic_gas=True), stack_check=None
    )
    assert not verified and "gas" in msg.lower()


def test_sha3_word_gas_consistency_passes():
    """SHA3 内存扩展 + word gas(每 word 6)+ host bridge(gas_sha3 fixture)。"""
    evm, x86 = _load_pair("gas_sha3")
    verified, msg = ProgramEquivalenceChecker(
        timeout_ms=180000, check_gas=True
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(symbolic_gas=True), stack_check=None
    )
    assert verified, f"SHA3 word+memory gas consistency should hold, got: {msg}"


def test_sha3_tampered_word_gas_caught(monkeypatch):
    """防假绿:篡改 SHA3 word gas(6→9)→ gas_sha3 应 SAT。"""
    import state.evm_gas_state as gas_state
    orig = gas_state.charge_word_gas
    monkeypatch.setattr(
        gas_state, "charge_word_gas",
        lambda state, word_len, _const: orig(state, word_len, 9),
    )
    evm, x86 = _load_pair("gas_sha3")
    verified, msg = ProgramEquivalenceChecker(
        timeout_ms=180000, check_gas=True
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(symbolic_gas=True), stack_check=None
    )
    assert not verified and "gas" in msg.lower()


def test_calldatacopy_word_gas_consistency_passes():
    """CALLDATACOPY 内存扩展 + copy word gas(每 word 3)(gas_calldatacopy fixture)。"""
    evm, x86 = _load_pair("gas_calldatacopy")
    verified, msg = ProgramEquivalenceChecker(
        timeout_ms=180000, check_gas=True
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(symbolic_gas=True), stack_check=None
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
        timeout_ms=180000, check_gas=True
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(symbolic_gas=True), stack_check=None
    )
    assert verified, f"{name} memory gas consistency should hold, got: {msg}"
