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
    _find_unbounded_host_gas_ops,
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


def test_stage0_gas_guard_rejects_dynamic_gas_ops_before_x86_execution(monkeypatch):
    """未建模的动态 gas 指令必须在 x86 执行**之前**被拒（故传 object() 假 x86）。

    拒绝集当前为空（所有登记在 _DYNAMIC_GAS_KINDS 的指令都已建模），所以这里把
    CREATE 从已建模集里临时摘掉来触发 guard——这同时验证了 allowlist 的核心承诺：
    「登记了但没建模」会被自动拦下，不依赖有人手工维护黑名单。
    """
    import verification.program_verifier as pv

    monkeypatch.setattr(
        pv, "_MODELED_DYNAMIC_GAS_KINDS", pv._MODELED_DYNAMIC_GAS_KINDS - {"CREATE"}
    )

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
    """LOG 已转正为 A 类（memoryLogGas codegen x86 全程可见，EVM 侧 charge_log_gas
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


def test_stage0_gas_guard_allows_create_family():
    """EXTCODECOPY/CREATE/CREATE2 已在 gas 检查范围内，不再 fail-closed。

    可见 fee（memoryCreate{,2}GasN / memoryCopierGas(3)）与 host UF 两侧都已接好；
    MAX_INIT_CODE_SIZE_EXCEEDED(16) 经核对在 amd64 codegen 里根本不产生。
    专用 fixture: gas_create / gas_create_returngas / gas_create2 /
    gas_extcodecopy（+ 两个符号版）。"""
    for kind in ("EXTCODECOPY", "CREATE", "CREATE2"):
        evm_program = _program_with_ops(kind)
        assert _find_unsupported_dynamic_gas_ops(evm_program) == [], (
            f"{kind} should be allowed (visible fee + host UF both wired)"
        )


def test_dynamic_gas_allowlist_has_no_gap():
    """allowlist 不变量:登记在 _DYNAMIC_GAS_KINDS 的指令必须全部已建模。

    差集非空 = 有指令需要 gas 建模却没接上，此时它会被 guard 拒绝受理（fail-closed，
    不是假绿），但仍属于覆盖缺口，应当显式暴露而不是等某个合约撞上才发现。
    """
    import verification.program_verifier as pv

    gap = pv._DYNAMIC_GAS_KINDS - pv._MODELED_DYNAMIC_GAS_KINDS
    assert gap == set(), f"这些动态 gas 指令尚未建模: {sorted(gap)}"
    # 反向：已建模集不应出现全表之外的 kind，否则说明 _DYNAMIC_GAS_KINDS 漏登记
    # （漏登记的指令不会被 guard 检查，是真正的 fail-open 风险）。
    stray = pv._MODELED_DYNAMIC_GAS_KINDS - pv._DYNAMIC_GAS_KINDS
    assert stray == set(), f"_DYNAMIC_GAS_KINDS 漏登记: {sorted(stray)}"


def test_dynamic_gas_allowlist_rejects_unmodeled_kind(monkeypatch):
    """把某个 kind 从已建模集里摘掉，它必须立刻被拒——证明 allowlist 真的在起作用，
    而不只是两张常量表看着好看。"""
    import verification.program_verifier as pv

    monkeypatch.setattr(
        pv, "_MODELED_DYNAMIC_GAS_KINDS", pv._MODELED_DYNAMIC_GAS_KINDS - {"SHA3"}
    )
    evm_program = _program_with_ops("SHA3")
    assert _find_unsupported_dynamic_gas_ops(evm_program) == ["SHA3@pc=0x1"]


def test_manual_reject_hook_still_works(monkeypatch):
    """人工拒绝钩子（当前为空）仍可临时挡下某个已建模的 kind。"""
    import verification.program_verifier as pv

    monkeypatch.setattr(pv, "_MANUAL_REJECT_KINDS", frozenset({"CREATE"}))
    evm_program = _program_with_ops("CREATE")
    assert _find_unsupported_dynamic_gas_ops(evm_program) == ["CREATE@pc=0x1"]


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


# --- CLI 输出：结论前提不得被 --verbose 门控掉 ---


def _run_cli(monkeypatch, capsys, argv, verifier_message):
    """跑 main.main()，返回 (exit_code, stdout)。verify_programs 打桩，不真验证。"""
    monkeypatch.setattr(sys, "argv", argv)
    monkeypatch.setattr(
        main, "verify_programs",
        lambda *a, **kw: (True, verifier_message),
    )
    code = main.main()
    return code, capsys.readouterr().out


def test_cli_prints_full_scope_message_without_verbose(monkeypatch, capsys):
    """默认（非 verbose）输出必须原样带上 verifier 的范围与强度边界。

    曾经 message 藏在 `if args.verbose` 后面，默认只打印一句本地拼装的
    "Programs are semantically equivalent"——条件性结论被读成无条件的。
    """
    annotated = (
        "✓ VERIFIED: x86 ≡ EVM [functional equivalence at the fixed initial gas "
        "budget 555000; host gas is NOT modeled in this mode]"
    )
    code, out = _run_cli(
        monkeypatch, capsys,
        ["main.py", "ir.json", "90", "--gas-budget", "555000"],
        annotated,
    )

    assert code == 0
    assert annotated in out, f"结论前提被吞掉了：{out!r}"


def test_cli_does_not_synthesize_its_own_verdict_text(monkeypatch, capsys):
    """CLI 不得自己拼结论文案——两套文案会各自演化并对不上。"""
    code, out = _run_cli(
        monkeypatch, capsys,
        ["main.py", "ir.json", "90", "--gas-check", "fixed-budget"],
        "✓ VERIFIED: from the verifier [scope here]",
    )

    assert code == 0
    assert "from the verifier" in out
    assert "Programs are semantically equivalent" not in out, (
        "CLI 又开始自己拼结论文案了"
    )


def test_cli_fails_closed_when_success_has_no_scope_message(monkeypatch, capsys):
    """verified=True 但没有 message ⟹ 拒绝输出结论，退出码非 0。

    那意味着某条成功路径绕过了 `_annotate_gas_scope`，唯一"安全"的补救恰恰是打印一句
    无前提的 VERIFIED——正是要避免的东西。当前生产路径都带 message，这条是防回归。
    """
    code, out = _run_cli(monkeypatch, capsys, ["main.py", "ir.json", "90"], None)

    assert code == 1, "无范围声明的成功不该以 0 退出"
    assert "INCONCLUSIVE" in out
    assert "Programs are semantically equivalent" not in out


# --- 上界覆盖面：扫不动 IR 不得伪装成"全都有界" ---


def test_unbounded_scan_names_the_ops_without_a_bound():
    """有界的 SLOAD 不进结果，无界的 CALL/CREATE 进（判据派生自上界表）。"""
    program = _program_with_ops("SLOAD", "CALL", "CREATE", "ADD")

    assert _find_unbounded_host_gas_ops(program) == ["CALL", "CREATE"]


def test_unbounded_scan_returns_empty_when_every_host_op_is_bounded():
    program = _program_with_ops("SLOAD", "SSTORE", "EXP")

    assert _find_unbounded_host_gas_ops(program) == []


@pytest.mark.parametrize("broken", [
    object(),                                       # 连 blocks 都没有
    type("P", (), {"blocks": [object()]})(),        # block 没有 operations
    type("P", (), {"blocks": [type("B", (), {"operations": [object()]})()]})(),  # op 没有 kind
])
def test_unbounded_scan_fails_closed_when_the_ir_cannot_be_walked(broken):
    """扫不动 ⇒ None，**不是**空 list。

    两者都写成 `[]` 的话，"本程序 host op 全都有界"这句最强的话会在 IR 字段改名时被
    静默说出口——那正是这个扫描要防的过度声明。
    """
    assert _find_unbounded_host_gas_ops(broken) is None


def test_scope_message_says_unknown_when_coverage_cannot_be_determined():
    """覆盖面未知时，结论必须写 UNKNOWN，不许落到"全都有界"那句。"""
    checker = ProgramEquivalenceChecker(gas_check=GasCheck.FIXED_BUDGET)

    msg = checker._annotate_gas_scope(True, "✓ VERIFIED", 500000, object())

    assert "UNKNOWN" in msg
    assert "all bounded here" not in msg
    assert "none exists for" not in msg, "扫不出来就不能点名，那是编出来的"
