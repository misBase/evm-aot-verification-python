"""host-gas UF 框架单测（state/host_gas.py）。

验证 UF 兜底的 soundness 核心性质:
- 同 opcode + 同参 ⟹ UF 相消（evm_gas == x86_gas 可 UNSAT）。
- 同 opcode + 不同参 ⟹ 不相消（存在反例 → 安全，不会假绿）。
- 不同 opcode ⟹ 不相消（SLOAD 的 UF 不等于 SSTORE 的 UF）。
- host_gas_uf_enabled 关时 charge_host_gas_uf 不动 gas（不污染功能等价）。
"""

from z3 import BitVec, BitVecVal, Solver, sat, unsat

from state.host_gas import (
    HOST_GAS_UF_KINDS,
    HOST_GAS_HOST_KINDS,
    HOST_GAS_BUILTIN_KINDS,
    charge_host_gas_uf,
    host_gas_uf,
)
from state.smt_state import SMTState


def test_same_opcode_same_args_cancel():
    """同 opcode + 同参 + **同序号** → 两次 UF 求值恒相等（相消）。

    SLOAD 在 HOST_GAS_SEQ_KINDS 里，序号是 UF 签名的一部分，所以「同参」现在意味着
    栈参数与序号都相同——两侧对同一次调用取到同一个序号时才该相消。"""
    a = BitVec("a", 256)
    seq = BitVecVal(0, 256)
    u1 = host_gas_uf("SLOAD", [a], seq)
    u2 = host_gas_uf("SLOAD", [a], seq)
    s = Solver()
    s.add(u1 != u2)
    assert s.check() == unsat, "same opcode + same args + same seq must cancel"


def test_same_opcode_diff_args_not_cancel():
    """同 opcode + 不同参 → 可不等（不假相消，安全）。"""
    a = BitVec("a", 256)
    b = BitVec("b", 256)
    seq = BitVecVal(0, 256)
    u1 = host_gas_uf("SLOAD", [a], seq)
    u2 = host_gas_uf("SLOAD", [b], seq)
    s = Solver()
    s.add(u1 != u2)
    assert s.check() == sat, "different args must be allowed to differ"


def test_same_args_diff_seq_not_cancel():
    """**本次修复的核心性质**：同 key 的两次 SLOAD 可以扣不同的 gas。

    AOT 的 SLoad（host.go:71）首次返回 cold(2100)、之后 warm(100)。加序号前这两次是同一个
    term、必然同值，真实轨迹在模型里不存在；加序号后它们是独立符号。"""
    a = BitVec("a", 256)
    u_first = host_gas_uf("SLOAD", [a], BitVecVal(0, 256))
    u_second = host_gas_uf("SLOAD", [a], BitVecVal(1, 256))
    s = Solver()
    s.add(u_first != u_second)
    assert s.check() == sat, (
        "consecutive SLOADs on the same key must be allowed to cost differently "
        "(cold 2100 then warm 100)"
    )


def test_seq_kind_opcode_requires_seq():
    """fail-closed：HOST_GAS_SEQ_KINDS 里的指令漏传 seq 必须抛错。

    漏传会生成一元 host_gas_sload(key)——两侧都误用旧接口时照样相消，seq 静默失效
    而测试全绿。"""
    import pytest

    a = BitVec("a", 256)
    with pytest.raises(ValueError, match="seq"):
        host_gas_uf("SLOAD", [a])


def test_different_opcode_not_cancel():
    """不同 opcode → 不同 UF 符号，不假相消。用**同 arity 同参**的 BALANCE vs
    EXTCODESIZE（都 1 个 addr 参数）精确隔离「名字不同」这一条性质，避免与
    「arity 不同」混淆。"""
    a = BitVec("a", 256)
    seq = BitVecVal(0, 256)          # 两者都在 HOST_GAS_SEQ_KINDS 里，序号也取同一个
    u_balance = host_gas_uf("BALANCE", [a], seq)
    u_extcodesize = host_gas_uf("EXTCODESIZE", [a], seq)
    s = Solver()
    s.add(u_balance != u_extcodesize)
    assert s.check() == sat, "distinct opcode names must not share a UF symbol"


def test_uf_preserves_full_256bit_identity():
    """Fix #1:UF 必须承载完整 256 位栈值，不能截到低 64 位。

    旧实现把 256 位参数 Extract(63,0) 截成低 64 位作 identity，导致两个仅高
    192 位不同的栈值产出**恒等** UF。对 EXP 这类 gas 真依赖完整 exponent
    （aotGasExpEIP158 = 50*byteLen(exponent)）的指令，高位传错的 codegen bug
    会同时逃过 gas 检查（UF 相消）与功能检查（结果被 POP 丢弃时不约束高位）→ 假绿。

    修复后:仅高位不同的两个栈值必须产出**不同** UF（可被 SAT 区分）。"""
    from z3 import Concat, BitVecVal
    low = BitVecVal(5, 64)
    exp_hi0 = Concat(BitVecVal(0, 192), low)   # 高位=0
    exp_hi7 = Concat(BitVecVal(7, 192), low)   # 高位=7，低 64 位相同
    u0 = host_gas_uf("EXP", [exp_hi0])
    u7 = host_gas_uf("EXP", [exp_hi7])
    s = Solver()
    s.add(u0 != u7)
    assert s.check() == sat, (
        "UF must distinguish stack values that differ only in high bits "
        "(EXP gas depends on the full 256-bit exponent)"
    )


def test_uf_same_full_value_still_cancels():
    """对照 Fix #1:完整 256 位值相等时 UF 仍恒等（相消性质不被破坏）。"""
    a = BitVec("a", 256)
    seq = BitVecVal(0, 256)
    u1 = host_gas_uf("SLOAD", [a], seq)
    u2 = host_gas_uf("SLOAD", [a], seq)
    s = Solver()
    s.add(u1 != u2)
    assert s.check() == unsat, "same full 256-bit value must still cancel"


def test_charge_off_when_host_gas_uf_disabled():
    """host_gas_uf_enabled=False 时 charge_host_gas_uf 不改 evm_gas。

    注意这个开关只管 host gas UF；gas **状态语义**（静态/动态扣减、bookkeeping）
    始终建模，不受它控制。
    """
    state = SMTState.create_initial_state()  # symbolic_gas 默认 False
    assert not getattr(state, "host_gas_uf_enabled", False)
    before = state.evm_gas.Gas
    charge_host_gas_uf(state, "SLOAD", [BitVec("k", 256)])
    assert state.evm_gas.Gas is before, "gas must be untouched when UF disabled"


def test_charge_on_when_host_gas_uf_enabled():
    """host_gas_uf_enabled=True 时 charge_host_gas_uf 扣减 evm_gas。

    必须显式置位：唯一写入方是 program_verifier，create_initial_state 不再跟着
    symbolic_gas 一起打开它（那是第二个事实源）。
    """
    state = SMTState.create_initial_state(symbolic_gas=True)
    state.host_gas_uf_enabled = True
    before = state.evm_gas.Gas
    charge_host_gas_uf(state, "SLOAD", [BitVec("k", 256)])
    assert state.evm_gas.Gas is not before, "gas must change when UF enabled"


def test_host_and_builtin_kinds_partition():
    """B 类 host 与 builtin 集合不重叠，并集 = HOST_GAS_UF_KINDS。"""
    assert HOST_GAS_HOST_KINDS.isdisjoint(HOST_GAS_BUILTIN_KINDS)
    assert HOST_GAS_HOST_KINDS | HOST_GAS_BUILTIN_KINDS == HOST_GAS_UF_KINDS
    # EXP 是 builtin（dealWithExp），不是 host function。
    assert "EXP" in HOST_GAS_BUILTIN_KINDS
    assert "SLOAD" in HOST_GAS_HOST_KINDS
