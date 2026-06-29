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
        pytest.skip(f"fixture {name} not generated (run Go TestGenGasFixtures with GOARCH=amd64)")
    evm = EVMProgram(load_ir_from_json(ir_path))
    x86 = X86Program.from_hex(open(hex_path, encoding="utf-8").read().strip(), base_addr=0)
    return evm, x86


def _verify(name, **kw):
    evm, x86 = _load_pair(name)
    return ProgramEquivalenceChecker(
        timeout_ms=180000, check_gas=True
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(symbolic_gas=True),
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
    import evm_ir.semantics as sem
    orig = sem._return_gas_for
    monkeypatch.setattr(sem, "_return_gas_for", lambda op: orig(op) + 1)

    verified, msg = _verify("gas_call_returngas")
    assert not verified, "tampered EVM returnGas must be caught"
    assert "gas" in msg.lower(), f"expected gas counterexample, got: {msg}"


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
