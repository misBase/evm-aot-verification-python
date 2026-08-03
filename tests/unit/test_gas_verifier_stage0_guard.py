"""Stage-0 gas verifier guard tests."""

import sys

import pytest

import main
from evm_ir.json_parser import CompilerEVMResult
from evm_ir.models import EVMBlock, EvmOperator
from evm_ir.program import EVMProgram
from state.smt_state import SMTState
from verification.program_verifier import (
    GasCheck,
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
    # 补 TAG：verifier 入口有 IR 不变量校验「有 static_gas 的 block 必须带 TAG」，
    # 真实编译器 IR 恒满足，合成 program 也要对齐。
    block.operations = [
        EvmOperator(kind=kind, pc=i, block=block)
        for i, kind in enumerate(("TAG",) + kinds)
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
    checker = ProgramEquivalenceChecker(gas_check=GasCheck.FIXED_BUDGET)

    verified, message = checker.verify_program_pair(
        evm_program,
        object(),
        SMTState.create_initial_state(),
    )

    assert not verified
    assert "outside the currently provable gas scope" in message
    assert "CREATE@pc=0x2" in message  # TAG 占了 pc=0，PUSH1 占 pc=1


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
    两侧相消）不再 fail-closed，**与 gas_check 模式无关**。CALL 系列无可见内存扩展，
    returnGas 链是可见机器码且两侧同序建模（host-success 路径上相消），故也在此列。"""
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
        assert unsupported == [f"{kind}@pc=0x1"], (  # pc=0 是 TAG
            f"{kind} should still be fail-closed, got {unsupported}"
        )


def test_cli_parse_args_exposes_gas_check(monkeypatch):
    monkeypatch.setattr(
        sys, "argv", ["main.py", "ir.json", "90", "--gas-check", "fixed-budget"]
    )
    args = main.parse_args()
    assert args.gas_check == "fixed-budget"
    assert args.gas_budget is None


def test_cli_gas_check_defaults_to_off(monkeypatch):
    monkeypatch.setattr(sys, "argv", ["main.py", "ir.json", "90"])
    args = main.parse_args()
    assert args.gas_check == GasCheck.OFF.value


def test_cli_gas_check_rejects_unknown_mode(monkeypatch):
    """非法模式必须被 argparse 挡下，而不是一路漂到 GasCheck() 之外。"""
    monkeypatch.setattr(sys, "argv", ["main.py", "ir.json", "90", "--gas-check", "bogus"])
    with pytest.raises(SystemExit):
        main.parse_args()


def test_verify_programs_wires_gas_mode_to_matching_initial_gas(monkeypatch):
    """CLI 层必须给每个模式配上它要求的那种初始 gas，否则 verifier 入口会 fail-closed
    拒绝自己的调用方（FIXED_BUDGET 要具体、FULL 要符号）。"""
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
        def __init__(self, timeout_ms=60000, verbose=False, gas_check=GasCheck.OFF):
            captured["timeout_ms"] = timeout_ms
            captured["verbose"] = verbose
            captured["gas_check"] = gas_check

        def verify_program_pair(self, evm_program, x86_program, initial_state):
            from z3 import is_bv_value
            gas = initial_state.evm_gas.Gas
            captured["gas_is_concrete"] = is_bv_value(gas)
            captured["gas_value"] = gas.as_long() if is_bv_value(gas) else None
            return True, "ok"

    monkeypatch.setattr(main, "load_ir_from_json", lambda _path: "compiler-result")
    monkeypatch.setattr(main, "EVMProgram", FakeEVMProgram)
    monkeypatch.setattr(main, "X86Program", FakeX86Program)
    monkeypatch.setattr(main, "ProgramEquivalenceChecker", FakeChecker)

    def _run(mode, **kw):
        captured.clear()
        return main.verify_programs(
            "ir.json", "90", base_addr=0x6C, timeout_ms=123, verbose=True,
            gas_check=mode, **kw,
        )

    verified, message = _run(GasCheck.FIXED_BUDGET)
    assert verified
    assert message == "ok"
    assert captured["gas_check"] is GasCheck.FIXED_BUDGET
    assert captured["gas_is_concrete"], "FIXED_BUDGET 必须配具体 gas"
    assert captured["gas_value"] == 1_000_000_000
    assert captured["base_addr"] == 0x6C

    _run(GasCheck.FIXED_BUDGET, gas_budget=4321)
    assert captured["gas_value"] == 4321, "--gas-budget 必须透传到初始 state"

    _run(GasCheck.FULL)
    assert not captured["gas_is_concrete"], "FULL 必须配符号 gas"

    _run(GasCheck.OFF)
    assert captured["gas_check"] is GasCheck.OFF
    assert captured["gas_is_concrete"]


# --- IR 不变量：有 static_gas 的 block 必须带 TAG ---------------------------------
#
# 静态 gas 的 OOG 守卫挂在 TAG 序言上，而扣减是无条件的纯减法（consume_static 不钳零）。
# 无 TAG 时 gas 不足会回绕成 2^64 附近的大数并静默继续 —— 这是 fail-open，必须在 verifier
# 入口挡下。守卫**不能**下沉到 SymbolicExecutor：仓库里大量合成 EVMBlock（static_gas 非零、
# 无 TAG）直接驱动执行器来测裸 CFG 行为，那些是合法用法。


def _program_without_tag(static_gas: int) -> EVMProgram:
    block = EVMBlock(
        pc=0, stack_depth=0, min_depth=0, max_depth=1024,
        static_gas=static_gas, is_jump_target=False, is_inner_block=False,
        is_stop=False,
    )
    block.operations = [EvmOperator(kind="STOP", pc=0, block=block)]
    return EVMProgram(CompilerEVMResult([block]))


def test_static_gas_without_tag_is_rejected():
    verified, message = ProgramEquivalenceChecker().verify_program_pair(
        _program_without_tag(3), object(), SMTState.create_initial_state(),
    )
    assert not verified, "static_gas>0 且无 TAG 的 block 必须 fail-closed 拒绝"
    assert "IR INVARIANT VIOLATED" in message
    assert "pc=0x0" in message


def test_zero_static_gas_without_tag_is_allowed():
    """static_gas==0 时不扣减、无回绕风险，无 TAG 不该被拦。"""
    program = _program_without_tag(0)
    assert not [
        b for b in program.blocks
        if getattr(b, "static_gas", 0)
        and not any(op.kind.upper() == "TAG" for op in b.operations)
    ]


def test_ir_invariant_applies_regardless_of_gas_mode():
    """这是 IR 良构性检查，不是 gas 检查，GasCheck.OFF 下同样生效。"""
    for mode in (GasCheck.OFF, GasCheck.FIXED_BUDGET):
        verified, message = ProgramEquivalenceChecker(gas_check=mode).verify_program_pair(
            _program_without_tag(3), object(), SMTState.create_initial_state(),
        )
        assert not verified and "IR INVARIANT VIOLATED" in message, mode
