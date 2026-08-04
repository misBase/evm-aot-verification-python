"""B 类 host/builtin gas UF 兜底:端到端两侧相消验证。

SLOAD/SSTORE/BALANCE/EXTCODESIZE/EXTCODEHASH/SELFDESTRUCT（host）+ EXP（builtin）的
gas 在 Go runtime 不可见。EVM 侧 charge_host_gas_uf 与 x86 侧 _deduct_host_gas_uf
扣**同名 host_gas_uf(opcode, 栈参数)**，两侧栈值已被功能等价证明相等 → UF 相消，
gas 终值等价 UNSAT。

强度边界:这证明「两侧扣了同一个 host gas + 传给 host 的栈参数一致」，**不证明**
host gas 公式本身正确（host 公式是 assume）。防假绿靠:篡改 x86 侧 UF 的 opcode /
参数 → UF 不相消 → SAT（见 test_*_tamper）。
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
        pytest.skip(f"fixture {name} not generated (run Go TestGenGasFixtures with GOARCH=amd64)")
    evm = EVMProgram(load_ir_from_json(ir_path))
    x86 = X86Program.from_hex(open(hex_path, encoding="utf-8").read().strip(), base_addr=0)
    return evm, x86


def _verify(name, *, mode=GasCheck.FIXED_BUDGET, **kw):
    evm, x86 = _load_pair(name)
    # 模式与初始 gas 形态必须匹配，否则被 verify_program_pair 的配置校验 fail-closed 拒绝。
    initial_state = SMTState.create_initial_state(symbolic_gas=mode is GasCheck.FULL)
    return ProgramEquivalenceChecker(
        timeout_ms=180000, gas_check=mode
    ).verify_program_pair(
        evm, x86, initial_state,
        stack_check=None, **kw
    )


@pytest.mark.parametrize("name", [
    # account-access host / builtin（无可见 gas 部分，纯 UF）
    "gas_sload",
    "gas_two_sload",  # 多 host-op:两个 SLOAD 不同 key → 逐站点 UF 相消
    "gas_sstore",
    "gas_balance",
    "gas_extcodesize",
    "gas_extcodehash",
    "gas_selfdestruct",
    "gas_exp",
    # CALL 系列（returnGas 链 + host UF）
    "gas_call",            # returnGas == 0（CALL 是块末 gas-op）
    "gas_call_returngas",  # returnGas != 0（CALL 后还有 POP/ADD 等静态 gas）
    "gas_callcode",
    "gas_staticcall",
    "gas_delegatecall",
])
def test_host_gas_uf_consistency_passes(name):
    """两侧同名 host_gas_uf 相消 → gas 终值等价（UNSAT）。

    CALL 系列额外验证:EVM 侧 charge_host_gas_uf_with_return_gas 镜像 x86 的
    dealWithAddGas/SubGas returnGas 链（plain +=/-=），让 host 调用点两侧 gas
    实参一致、UF 相消。gas_call_returngas 专门覆盖 returnGas≠0（否则会假 SAT）。"""
    verified, msg = _verify(name)
    assert verified, f"{name} host-gas UF should cancel and verify, got: {msg}"


@pytest.mark.parametrize("name", [
    "gas_sload",           # 普通 host function
    "gas_exp",             # builtin（gas 在 dealWithExp 内）
    "gas_call_returngas",  # CALL 系且 returnGas != 0
])
def test_host_gas_uf_consistency_passes_under_full(name):
    """FULL（符号 gas，量化所有初始预算）下 host 指令同样放行且 UF 相消。

    FULL 曾把整个 HOST_GAS_UF_KINDS 纳入拒绝集，删除后这里是持续回归证据。三个 fixture
    覆盖三条不同接线：纯 host UF / builtin UF / returnGas 链（add → UF → sub）。"""
    verified, msg = _verify(name, mode=GasCheck.FULL)
    assert verified, f"{name} host-gas UF should cancel under FULL, got: {msg}"


def test_host_gas_uf_tampered_opcode_caught_under_full(monkeypatch):
    """防假绿:FULL 通道的 gas observable 非 vacuous——篡改 x86 侧 UF opcode 必须 SAT。

    正向用例全绿只说明两侧相消，不排除 FULL 下 gas 根本没进比较。"""
    import x86_64.go_function_semantics as gfs
    orig = gfs.GoFunctionSemantics._deduct_host_gas_uf

    def tampered(self, mstate, opcode, args):
        return orig(self, mstate, "WRONGOP" if opcode == "SLOAD" else opcode, args)

    monkeypatch.setattr(gfs.GoFunctionSemantics, "_deduct_host_gas_uf", tampered)
    verified, msg = _verify("gas_sload", mode=GasCheck.FULL)
    assert not verified, "tampered x86 UF opcode must be caught under FULL"
    assert "gas" in msg.lower(), f"expected gas counterexample, got: {msg}"


def test_host_gas_uf_tampered_opcode_caught(monkeypatch):
    """防假绿:x86 侧 UF 用错 opcode → 与 EVM 不同名 → 不相消 → SAT。"""
    import x86_64.go_function_semantics as gfs
    orig = gfs.GoFunctionSemantics._deduct_host_gas_uf

    def tampered(self, mstate, opcode, args):
        # SLOAD 的 x86 UF 改成错误 opcode → 两侧不相消
        return orig(self, mstate, "WRONGOP" if opcode == "SLOAD" else opcode, args)

    monkeypatch.setattr(gfs.GoFunctionSemantics, "_deduct_host_gas_uf", tampered)
    verified, msg = _verify("gas_sload")
    assert not verified, "tampered x86 UF opcode must be caught (false green otherwise)"
    assert "gas" in msg.lower(), f"expected gas counterexample, got: {msg}"


def test_host_gas_uf_tampered_arg_order_caught(monkeypatch):
    """防假绿:x86 侧 UF 参数次序错（SSTORE [key,val]→[val,key]）→ 不相消 → SAT。

    这正是 UF 按栈参数绑定带来的额外价值:抓「传给 host 的参数传错」的 codegen bug。"""
    import x86_64.go_function_semantics as gfs
    orig = gfs.GoFunctionSemantics._deduct_host_gas_uf

    def tampered(self, mstate, opcode, args):
        if opcode == "SSTORE" and len(args) == 2:
            args = [args[1], args[0]]
        return orig(self, mstate, opcode, args)

    monkeypatch.setattr(gfs.GoFunctionSemantics, "_deduct_host_gas_uf", tampered)
    verified, msg = _verify("gas_sstore")
    assert not verified, "tampered x86 UF arg order must be caught"
    assert "gas" in msg.lower(), f"expected gas counterexample, got: {msg}"


def test_host_gas_uf_missing_x86_charge_caught(monkeypatch):
    """防假绿:x86 侧完全不扣 host gas（漏掉）→ EVM 扣了 UF、x86 没扣 → SAT。"""
    import x86_64.go_function_semantics as gfs

    def noop(self, mstate, opcode, args):
        return None  # x86 侧不扣任何 host gas

    monkeypatch.setattr(gfs.GoFunctionSemantics, "_deduct_host_gas_uf", noop)
    verified, msg = _verify("gas_sload")
    assert not verified, "missing x86 host-gas charge must be caught"
    assert "gas" in msg.lower(), f"expected gas counterexample, got: {msg}"


def test_host_gas_uf_tampered_return_gas_caught(monkeypatch):
    """防假绿:EVM 侧 returnGas 算错（+1）→ 与 x86 dealWithAddGas/SubGas 不匹配 → SAT。

    用 returnGas≠0 的 fixture，证明 returnGas 链对齐是非空的（不是恒成立）。"""
    import evm_ir.semantics_gas as gas_sem
    orig = gas_sem.return_gas_for
    monkeypatch.setattr(gas_sem, "return_gas_for", lambda op: orig(op) + 1)

    verified, msg = _verify("gas_call_returngas")
    assert not verified, "tampered EVM returnGas must be caught"
    assert "gas" in msg.lower(), f"expected gas counterexample, got: {msg}"


# --- CREATE / CREATE2 / EXTCODECOPY：可见 fee + host UF 混合 ---
#
# 这三个 opcode 曾整体 fail-closed 拒绝（_DYNAMIC_GAS_UNSUPPORTED_KINDS），理由是
# 「缺专用 fixture」与「MAX_INIT_CODE_SIZE_EXCEEDED(16) 未核对」。下面的 fixture 补上了
# 前者；后者经核对在 amd64 codegen 里根本不产生该状态码（`evmNativeCallStatus-
# MaxInitCodeSizeExceeded` 全包只出现在 engine_evm.go:260 枚举与 :280 的 error 映射，
# memoryGasCreate 的 `// check if codeSize > MaxInitCodeSize` 注释下没有比较指令），
# 与 host gas 耗尽同类：Go host 内 error 终止、无生成代码可验。
#
# 与纯 host op 的区别：它们同时有**可见**动态 fee（memoryCreate{,2}GasN /
# memoryCopierGas(3)）和**不可见**的 host cost，两段都必须对上才会 UNSAT。

@pytest.mark.parametrize("name", [
    "gas_create",            # 内存扩展 + InitCodeWordGas(2)，returnGas=0
    "gas_create_returngas",  # 同上但 returnGas=13：可见 fee 落在 add/sub 窗口内
    "gas_create2",           # word 常量是 InitCodeWordGas+Sha3WordGas(8)
    "gas_extcodecopy",       # calcMemSize64(Back(1),Back(3)) + CopyGas(3)
])
@pytest.mark.parametrize("mode", [GasCheck.FIXED_BUDGET, GasCheck.FULL])
def test_create_family_gas_consistency_passes(name, mode):
    """CREATE/CREATE2/EXTCODECOPY 的可见 fee 与 host UF 在两种模式下都一致。

    FULL 不能省：FIXED_BUDGET 的具体预算会把常量 fee 的 OOG 条件在 simplify 阶段
    折成 False，那些分支根本不建，只证明了正常路径的 gas 终值。"""
    verified, msg = _verify(name, mode=mode)
    assert verified, f"{name} [{mode.value}] gas consistency should hold, got: {msg}"


def test_create_tampered_init_code_word_gas_caught(monkeypatch):
    """防假绿:CREATE 的 InitCodeWordGas 2→9 必须 SAT。

    patch 目标是 **evm_ir.semantics** 上的名字：semantics.py 用模块级
    `from state.evm_gas_state import INIT_CODE_WORD_GAS` 绑定，改
    state.evm_gas_state 上的同名常量对已绑定的引用无效（会得到假绿的绿）。"""
    import evm_ir.semantics as sem
    monkeypatch.setattr(sem, "INIT_CODE_WORD_GAS", 9)

    verified, msg = _verify("gas_create")
    assert not verified, "tampered InitCodeWordGas must be caught"
    assert "COUNTEREXAMPLE FOUND" in msg, f"expected a counterexample, got: {msg}"
    assert "gas differs" in msg, f"expected the gas observable to differ, got: {msg}"


def test_create2_tampered_word_gas_caught(monkeypatch):
    """防假绿:CREATE2 的 word 常量 8→2（= CREATE 的 InitCodeWordGas）必须 SAT。

    改成 CREATE 的常量而不是随便一个数，直接证明两者**被区分**——memoryCreate2GasN
    比 memoryCreateGasN 多算一次 keccak 的 Sha3WordGas，混用不会被这条测试放过。"""
    import evm_ir.semantics as sem
    monkeypatch.setattr(sem, "CREATE2_WORD_GAS", 2)

    verified, msg = _verify("gas_create2")
    assert not verified, "tampered CREATE2 word gas must be caught"
    assert "COUNTEREXAMPLE FOUND" in msg, f"expected a counterexample, got: {msg}"
    assert "gas differs" in msg, f"expected the gas observable to differ, got: {msg}"


def test_extcodecopy_tampered_copy_word_gas_caught(monkeypatch):
    """防假绿:EXTCODECOPY 的 copy word gas 3→9 必须 SAT。

    EXTCODECOPY 的 `3` 在 semantics.py 里是字面量、没有具名常量可改，但
    semantics_gas.charge_memory_and_word_gas 走的是 `gas_state.word_fee(...)`
    模块属性访问，patch state.evm_gas_state.word_fee 即可生效。"""
    import state.evm_gas_state as gas_state
    orig = gas_state.word_fee
    monkeypatch.setattr(
        gas_state, "word_fee", lambda word_len, _const: orig(word_len, 9)
    )

    verified, msg = _verify("gas_extcodecopy")
    assert not verified, "tampered EXTCODECOPY copy word gas must be caught"
    assert "COUNTEREXAMPLE FOUND" in msg, f"expected a counterexample, got: {msg}"
    assert "gas differs" in msg, f"expected the gas observable to differ, got: {msg}"


@pytest.mark.parametrize("name,word_gas_const", [
    ("gas_create", 2),        # InitCodeWordGas
    ("gas_create2", 8),       # InitCodeWordGas + Sha3WordGas
    ("gas_extcodecopy", 3),   # CopyGas
])
def test_create_family_visible_fee_actually_charged(name, word_gas_const, monkeypatch):
    """正向用例不是 vacuous 的:可见 fee 确实被扣了，且 word 常量是预期的那个。

    「VERIFIED」本身不排除「这条指令压根没被执行到」——路径被剪掉时两侧同样不扣，
    gas 照样相等。这里在 EVM 侧的扣费入口装计数器，确认符号执行真的走到了该指令，
    并顺带钉死它用的 word gas 常量（三个 opcode 各不相同，混用会被这里抓到）。
    """
    import evm_ir.semantics_gas as gas_sem

    seen = []
    orig = gas_sem.charge_memory_and_word_gas

    def spy(state, offset_bv, length_bv, const):
        seen.append(const)
        return orig(state, offset_bv, length_bv, const)

    monkeypatch.setattr(gas_sem, "charge_memory_and_word_gas", spy)

    verified, msg = _verify(name)
    assert verified, f"{name} should verify, got: {msg}"
    assert seen, f"{name}: 可见 fee 从未被扣 —— 该指令没有被执行到，正例是 vacuous 的"
    assert set(seen) == {word_gas_const}, (
        f"{name}: word gas 常量应为 {word_gas_const}，实际 {sorted(set(seen))}"
    )


def test_create_tampered_return_gas_caught(monkeypatch):
    """防假绿:CREATE 的 returnGas 算错（+1）必须 SAT。

    用 returnGas=13 的 fixture。CREATE 与 CALL 系的区别是它在 add/sub 窗口**内**还有
    可见 fee（顺序 add rg → fee → host → sub rg），窗口错位不改 gas 终值（加减相消）
    但会让可见 fee 的 OOG 阈值少算一个 rg，所以这条链必须有非空的端到端覆盖。"""
    import evm_ir.semantics_gas as gas_sem
    orig = gas_sem.return_gas_for
    monkeypatch.setattr(gas_sem, "return_gas_for", lambda op: orig(op) + 1)

    verified, msg = _verify("gas_create_returngas")
    assert not verified, "tampered CREATE returnGas must be caught"
    assert "COUNTEREXAMPLE FOUND" in msg, f"expected a counterexample, got: {msg}"
    assert "gas differs" in msg, f"expected the gas observable to differ, got: {msg}"


# --- 符号操作数：cap / SafeMul / SafeAdd 溢出与动态 OOG 的 IR↔x86 对照 ---
#
# 常量 fixture 只能证明正常路径上的扣费。要让 memoryGasCost 的 cap 支、
# makeSafeMul/SafeAdd 的溢出支（→ GAS_UINT_OVERFLOW 13）与动态 OOG（→ 12）在**端到端**
# 层面真实可达，offset/size 必须是符号量。
#
# 这套配置是让它跑得动的关键，缺一不可（实测）：
#   - abstract_calldataload_words + summary_config：**必须成对**。抽象在 EVM 侧无条件
#     生效（semantics.py），x86 侧只在 CALLDATALOAD summary 路径里生效
#     （x86_64/summaries/calldataload.py）。只开抽象不给 summary_config，两侧
#     CALLDATALOAD 取值不同 → 1.2s 就"抓到"一个 status code 反例，**那是配置不对称
#     造成的假反例**，不是建模缺陷。
#   - enable_merge=False + x86_reachability_timeout_ms=250：把 x86 终止路径从 17 压到
#     8。不加这两项时 7×17=119 对 pair，实测 >40min 未完成（且 skip_feasibility 也救
#     不回来——瓶颈是每对约 6s 的固定开销，不是求解不动：逐对检查全是毫秒级 unsat
#     且无一 unknown）。
#   - 固定 calldata_size_bytes：符号 calldatasize 会再乘一层路径。
_SYMBOLIC_KWARGS = dict(
    path_observations=True,
    path_pair_workers=4,
    enable_merge=False,
    x86_reachability_timeout_ms=250,
)


def _verify_symbolic(name, *, mode=GasCheck.FIXED_BUDGET):
    """符号操作数 fixture 的验证入口（配置见上方注释）。"""
    from x86_64.summaries import TRUSTED_SUMMARY_CONFIG

    evm, x86 = _load_pair(name)
    initial_state = SMTState.create_initial_state(
        symbolic_gas=mode is GasCheck.FULL, calldata_size_bytes=64,
    )
    initial_state.abstract_calldataload_words = True
    return ProgramEquivalenceChecker(
        timeout_ms=600000, gas_check=mode
    ).verify_program_pair(
        evm, x86, initial_state, stack_check=None,
        summary_config=TRUSTED_SUMMARY_CONFIG, **_SYMBOLIC_KWARGS,
    )


_FULL_MODE_SKIP = pytest.mark.skip(reason=(
    "符号操作数 + 符号 gas 的组合当前不稳定/跑不完，**FIXED_BUDGET 两格已覆盖同一批"
    "错误分支**（12/13 由符号 offset/size 触发，与 gas 是否符号无关——见 "
    "test_symbolic_fixture_error_branches_reachable 对两种 gas 形态的断言），FULL 只额外"
    "提供「对所有初始 gas 量化」。实测：\n"
    "  - gas_extcodecopy_sym FULL：>420s 未完成。\n"
    "  - gas_create_sym FULL：**单独跑 86s 通过**，但同进程里先跑过它自己的 "
    "    FIXED_BUDGET 那格之后会退化到 >600s。这是跨测试状态污染（两个测试顺序跑即可"
    "    复现，与 CPU 竞争无关；排在其后的 gas_extcodecopy_sym 仍是 62s，所以是同一"
    "    fixture 第二次执行的问题，疑似 Z3 全局 context 累积——effect_id 取自 op.pc，"
    "    两次执行符号名相同）。根因未定位，属既有基础设施问题、非本次改动引入。\n"
    "注意这是**性能**问题不是健全性问题：超时走 fail-closed，报 TIMEOUT 失败而非假绿。"
))


@pytest.mark.parametrize("name,mode", [
    ("gas_create_sym", GasCheck.FIXED_BUDGET),        # ~12s
    ("gas_extcodecopy_sym", GasCheck.FIXED_BUDGET),   # ~62s
    pytest.param("gas_create_sym", GasCheck.FULL, marks=_FULL_MODE_SKIP),
    pytest.param("gas_extcodecopy_sym", GasCheck.FULL, marks=_FULL_MODE_SKIP),
])
def test_create_family_symbolic_operand_gas_consistency(name, mode):
    """符号 offset/size 下 CREATE/EXTCODECOPY 的 gas 与终止状态逐路径一致。

    这是 cap / SafeMul / SafeAdd 溢出分支唯一的 IR↔x86 对照（EVM 侧单测在
    tests/unit/test_gas_error_codes.py，但那没有 x86 侧对照）。"""
    verified, msg = _verify_symbolic(name, mode=mode)
    assert verified, f"{name} [{mode.value}] symbolic-operand gas check failed: {msg}"


@pytest.mark.parametrize("name", ["gas_create_sym", "gas_extcodecopy_sym"])
@pytest.mark.parametrize("symbolic_gas", [False, True])
def test_symbolic_fixture_error_branches_reachable(name, symbolic_gas):
    """符号 fixture 的正例非 vacuous:12/13 两类错误分支都**真的可满足**。

    上面的用例返回 VERIFIED 只说明两侧一致，不排除那些错误路径根本不可达（路径条件
    恒假时等价检查 vacuously 通过）。这里直接枚举 EVM 终止路径并逐条判可满足性，
    钉死 GAS_UINT_OVERFLOW(13，来自 calcMemSize64 / SafeMul 溢出）与 OUT_OF_GAS(12，
    来自 memoryGasCost 的 cap 支与 UseGas 失败）都在被验证的路径集合里。
    """
    from z3 import Solver, is_bv_value, sat, simplify

    evm, _ = _load_pair(name)
    state = SMTState.create_initial_state(
        symbolic_gas=symbolic_gas, calldata_size_bytes=64,
    )
    state.abstract_calldataload_words = True
    semantics = evm.to_z3_paths(state, merge_state=False)

    reachable = set()
    for obs in semantics.as_result_dicts():
        status = simplify(obs["status_code"])
        if not is_bv_value(status):
            continue
        solver = Solver()
        solver.set("timeout", 10000)
        solver.add(obs["condition"])
        if solver.check() == sat:
            reachable.add(status.as_long())

    assert 13 in reachable, (
        f"{name}: GAS_UINT_OVERFLOW(13) 分支不可达，符号边界其实没被验到；"
        f"实际可达状态码 {sorted(reachable)}"
    )
    assert 12 in reachable, (
        f"{name}: OUT_OF_GAS(12) 分支不可达；实际可达状态码 {sorted(reachable)}"
    )


def test_host_gas_uf_check_off_unaffected():
    """check_gas 默认关时,host 指令功能等价不受 UF 影响（回归保护）。"""
    evm, x86 = _load_pair("gas_sload")
    verified, msg = ProgramEquivalenceChecker(timeout_ms=180000).verify_program_pair(
        evm, x86, SMTState.create_initial_state(), stack_check=None
    )
    assert verified, f"functional equivalence should hold with gas off: {msg}"


# --- 并行 path_observations 模式回归（修复 gas 假绿 bug：worker 私有 solver 未
#     reset → gas/status 检查继承前序检查的累积 UNSAT 断言 → vacuous 假绿）---

@pytest.mark.parametrize("name,workers", [
    ("gas_sload", 2),
    ("gas_call_returngas", 2),
    ("gas_two_sload", 2),
])
def test_host_gas_uf_parallel_pathobs_passes(name, workers):
    """并行 path_observations 模式下 host UF 仍正确相消（正向）。"""
    verified, msg = _verify(name, path_observations=True, path_pair_workers=workers)
    assert verified, f"{name} parallel host-gas UF should verify, got: {msg}"


def test_host_gas_uf_parallel_pathobs_tamper_caught(monkeypatch):
    """**核心回归**:并行 path_observations 模式下篡改 gas **必须** SAT。

    曾有严重 bug:worker 私有 solver 在 gas/status 检查处不 reset（只有共享 solver
    才 reset），继承前序 memory 检查累积的 UNSAT 断言 → gas 查询 vacuous UNSAT →
    gas 不一致被假绿。此测试在 workers=2 下篡改 host UF opcode，必须抓到 SAT。"""
    import x86_64.go_function_semantics as gfs
    orig = gfs.GoFunctionSemantics._deduct_host_gas_uf
    monkeypatch.setattr(
        gfs.GoFunctionSemantics, "_deduct_host_gas_uf",
        lambda self, m, op, a: orig(self, m, "WRONGOP" if op == "SLOAD" else op, a),
    )
    verified, msg = _verify("gas_sload", path_observations=True, path_pair_workers=2)
    assert not verified, "parallel-mode gas mismatch must be caught (false green bug)"
    assert "gas" in msg.lower(), f"expected gas counterexample, got: {msg}"
