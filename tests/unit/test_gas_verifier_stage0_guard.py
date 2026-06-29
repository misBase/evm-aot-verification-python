"""Stage-0 gas verifier guard tests."""

import sys

import main
from evm_ir.json_parser import CompilerEVMResult
from evm_ir.models import EVMBlock, EvmOperator
from evm_ir.program import EVMProgram
from state.smt_state import SMTState
from verification.program_verifier import (
    ProgramEquivalenceChecker,
    _find_unsupported_dynamic_gas_ops,
)


def _program_with_ops(*kinds: str) -> EVMProgram:
    block = EVMBlock(
        pc=0,
        stack_depth=0,
        min_depth=0,
        max_depth=1024,
        static_gas=3,
        is_jump_target=False,
        is_inner_block=False,
        is_stop=False,
    )
    block.operations = [
        EvmOperator(kind=kind, pc=i, block=block)
        for i, kind in enumerate(kinds)
    ]
    return EVMProgram(CompilerEVMResult([block]))


def test_stage0_gas_guard_allows_static_gas_ops():
    evm_program = _program_with_ops("PUSH1", "GAS", "ADD", "STOP")

    assert _find_unsupported_dynamic_gas_ops(evm_program) == []


def test_stage0_gas_guard_rejects_dynamic_gas_ops_before_x86_execution():
    # CREATE 仍 fail-closed（x86 可见的 returnGas 链 + 内存扩展尚未对齐）。
    # guard 应在 x86 执行前就拒绝（故传 object() 假 x86 也不会被触碰）。
    # 注意:EXP/SLOAD 等已转 UF 兜底、移出拒绝集，不再触发此 guard。
    evm_program = _program_with_ops("PUSH1", "CREATE", "STOP")
    checker = ProgramEquivalenceChecker(check_gas=True)

    verified, message = checker.verify_program_pair(
        evm_program,
        object(),
        SMTState.create_initial_state(symbolic_gas=True),
    )

    assert not verified
    assert "dynamic gas operators are not modeled yet" in message
    assert "CREATE@pc=0x1" in message


def test_stage0_gas_guard_allows_log():
    """LOG 已转正为 A 类（memoryLogGas codegen x86 全程可见，EVM 侧 _charge_log_gas
    建真实公式），不再 fail-closed 拒绝。

    注意:真实 IR 的 LOG kind 就是 "LOG"（topic 数在 op.immediate），不是
    "LOG0".."LOG4"。guard 用精确匹配，故旧的 startswith("LOG") 已移除。"""
    evm_program = _program_with_ops("LOG")
    assert _find_unsupported_dynamic_gas_ops(evm_program) == [], (
        "LOG should be allowed (A 类, real gas proof)"
    )


def test_stage0_gas_guard_allows_host_uf_ops():
    """已转 UF 兜底的 B 类 op（EVM charge_host_gas_uf + x86 _deduct_host_gas_uf
    两侧相消）不再 fail-closed。CALL 系列的 returnGas 链是可见机器码净 0、无可见
    内存扩展，故也在此列。"""
    uf_ops = (
        "EXP",  # builtin
        "SLOAD", "SSTORE", "BALANCE", "EXTCODESIZE", "EXTCODEHASH", "SELFDESTRUCT",
        "CALL", "CALLCODE", "DELEGATECALL", "STATICCALL",
    )
    for kind in uf_ops:
        evm_program = _program_with_ops(kind)
        assert _find_unsupported_dynamic_gas_ops(evm_program) == [], (
            f"{kind} should be allowed (host-gas UF wired on both sides)"
        )


def test_stage0_gas_guard_still_rejects_visible_memory_part_ops():
    """仍 fail-closed 的 op:除 host UF 外 x86 还有**可见内存扩展** gas
    （memoryCreateGasN / ExtCodeCopy）尚未在 EVM 侧对齐。逐一覆盖防误移出。"""
    still_rejected = (
        "EXTCODECOPY",
        "CREATE", "CREATE2",
    )
    for kind in still_rejected:
        evm_program = _program_with_ops(kind)
        unsupported = _find_unsupported_dynamic_gas_ops(evm_program)
        assert unsupported == [f"{kind}@pc=0x0"], (
            f"{kind} should still be fail-closed, got {unsupported}"
        )


def test_cli_parse_args_exposes_check_gas(monkeypatch):
    monkeypatch.setattr(sys, "argv", ["main.py", "ir.json", "90", "--check-gas"])

    args = main.parse_args()

    assert args.check_gas is True


def test_verify_programs_enables_symbolic_gas_when_check_gas(monkeypatch):
    captured = {}

    class FakeEVMProgram:
        def __init__(self, compiler_result):
            captured["compiler_result"] = compiler_result

    class FakeX86Program:
        @classmethod
        def from_hex(cls, hex_sequence, base_addr=0):
            captured["hex_sequence"] = hex_sequence
            captured["base_addr"] = base_addr
            return cls()

    class FakeChecker:
        def __init__(self, timeout_ms=60000, verbose=False, check_gas=False):
            captured["timeout_ms"] = timeout_ms
            captured["verbose"] = verbose
            captured["check_gas"] = check_gas

        def verify_program_pair(self, evm_program, x86_program, initial_state):
            captured["gas_symbol"] = initial_state.evm_gas.Gas.decl().name()
            return True, "ok"

    monkeypatch.setattr(main, "load_ir_from_json", lambda _path: "compiler-result")
    monkeypatch.setattr(main, "EVMProgram", FakeEVMProgram)
    monkeypatch.setattr(main, "X86Program", FakeX86Program)
    monkeypatch.setattr(main, "ProgramEquivalenceChecker", FakeChecker)

    verified, message = main.verify_programs(
        "ir.json",
        "90",
        base_addr=0x6C,
        timeout_ms=123,
        verbose=True,
        check_gas=True,
    )

    assert verified
    assert message == "ok"
    assert captured["check_gas"] is True
    assert captured["gas_symbol"] == "GasRemaining"
    assert captured["base_addr"] == 0x6C
