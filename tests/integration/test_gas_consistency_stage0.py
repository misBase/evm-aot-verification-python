"""阶段0 gas 一致性:端到端程序对验证（静态 gas 终值等式）。

验证锚点:真实编译产物含 makeStaticUseGas 的 gas prologue
（mov rax,[r13+0x70]; cmp; jb OOG; sub; mov [r13+0x70],rax）。

使用 add_with_push（纯静态 gas，无动态 gas 指令）+ 含完整 gas prologue 的
X86_ADD_FULL_HEX_SEQUENCE。gas_check=GasCheck.FIXED_BUDGET：具体预算让静态 gas 的
OOG 条件在 simplify 阶段折死，只验充足路径的 gas 终值。

注意:含动态 gas 指令（MSTORE/RETURN/CALL...）的程序属阶段 1，本阶段不覆盖。
"""

import os

import pytest

from verification.program_verifier import GasCheck, ProgramEquivalenceChecker
from evm_ir.json_parser import load_ir_from_json
from evm_ir.program import EVMProgram
from x86_64.program import X86Program
from state.smt_state import SMTState
from tests.integration.test_equivalence_checker import (
    X86_ADD_FULL_HEX_SEQUENCE,
    X86_ADD_FULL_BASE_ADDR,
)


def _load_add_with_push_pair():
    test_dir = os.path.dirname(__file__)
    ir_path = os.path.join(test_dir, "..", "data", "add_with_push.json")
    evm_program = EVMProgram(load_ir_from_json(ir_path))
    x86_program = X86Program.from_hex(
        X86_ADD_FULL_HEX_SEQUENCE, base_addr=X86_ADD_FULL_BASE_ADDR
    )
    return evm_program, x86_program


def test_gas_consistency_static_only_passes():
    """纯静态 gas 程序:EVM 扣 block.static_gas == x86 makeStaticUseGas 扣 gas。"""
    evm_program, x86_program = _load_add_with_push_pair()

    checker = ProgramEquivalenceChecker(timeout_ms=60000, gas_check=GasCheck.FIXED_BUDGET)
    initial_state = SMTState.create_initial_state()
    verified, msg = checker.verify_program_pair(
        evm_program, x86_program, initial_state, stack_check=None
    )

    assert verified, f"static gas consistency should hold, got: {msg}"


def test_gas_consistency_tampered_static_gas_caught():
    """防假绿:篡改 EVM block.static_gas → gas 检查必须 SAT（抓到反例）。"""
    evm_program, x86_program = _load_add_with_push_pair()
    # x86 仍扣真实 static_gas(6)；EVM 改成 99 → 两侧 gas 终值必不同。
    for block in evm_program.blocks:
        block.static_gas = 99

    checker = ProgramEquivalenceChecker(timeout_ms=60000, gas_check=GasCheck.FIXED_BUDGET)
    initial_state = SMTState.create_initial_state()
    verified, msg = checker.verify_program_pair(
        evm_program, x86_program, initial_state, stack_check=None
    )

    assert not verified, "tampered static_gas must be caught (false green otherwise)"
    assert "gas" in msg.lower(), f"expected gas counterexample, got: {msg}"


def test_gas_check_off_by_default_ignores_gas():
    """check_gas 默认关闭时,gas 差异不影响功能等价结论（即便篡改 static_gas）。

    保证 gas 检查是 opt-in，不污染既有功能等价验证（symbolic_gas 也默认关，
    OOG 分支不可达）。
    """
    evm_program, x86_program = _load_add_with_push_pair()
    for block in evm_program.blocks:
        block.static_gas = 99  # 篡改也无所谓——gas 检查未开

    checker = ProgramEquivalenceChecker(timeout_ms=60000)  # check_gas 默认 False
    initial_state = SMTState.create_initial_state()  # symbolic_gas 默认 False
    verified, msg = checker.verify_program_pair(
        evm_program, x86_program, initial_state, stack_check=None
    )

    assert verified, f"functional equivalence should hold with gas check off: {msg}"
