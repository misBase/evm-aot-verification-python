"""回归测试：terminal-paths 单指令等价性里 x86 path-local assumption 必须 path-guard。

背景：x86 CFG 分叉后，每条终止路径有各自独立的 `mstate.assumptions`
（分叉走 `X86GlobalState.__deepcopy__` → `mstate.copy()` 深拷贝 assumptions list）。
某条路径产生的 assumption 正确含义是 `condition => assumption`，只在走这条路径时成立。

曾经的实现把所有路径的 assumptions 收集后**无条件全局**喂给 solver，于是某条路径
（限制输入空间的）assumption 会越界约束 sibling 路径，把 sibling 路径在被排除输入区
的真实 mismatch 藏成假绿。

本测试用最小桩 monkeypatch 掉 EVM/x86 状态构建，跑真实的 `assert_instruction_equivalent`
端到端装配（mismatch 收集 + assumption 注入 + solver 求解），复现并锁定该机制：

构造（与已验证的 POC 同构）：
- sym：一个 256-bit 符号输入；
- path A：condition C=`Extract(0,0,sym)==1`，挂 path-local 限制 assumption
  `Extract(255,64,sym)==0`（非恒真，排除高位非零输入），且本路径无 mismatch；
- path B：condition Not(C)，无 assumption，且在被 A 的 assumption 排除的输入区
  （`Extract(255,64,sym)!=0`）存在 storage mismatch。

正确行为：`assert_instruction_equivalent` 必须捕获 path B 的反例并抛 AssertionError。
旧的无条件全局实现会让 path A 的 `Extract(255,64,sym)==0` 越界，把这个反例藏掉
→ `assert_instruction_equivalent` 不抛（假绿）。
"""

from z3 import BitVec, BitVecVal, Concat, Extract

from tests.support import instruction_equivalence
from tests.support.instruction_equivalence import (
    InstructionEquivalenceCase,
    assert_instruction_equivalent,
)


_SYM = BitVec("path_assumption_sym", 256)
_C = Extract(0, 0, _SYM) == BitVecVal(1, 1)  # path A 条件
_NOT_C = Extract(0, 0, _SYM) == BitVecVal(0, 1)  # path B 条件
_RESTRICT = Extract(255, 64, _SYM) == BitVecVal(0, 192)  # path A 的限制 assumption


class _StubConstraints:
    def __init__(self, cond):
        self._cond = cond

    def as_bool(self):
        return self._cond


class _StubStorage:
    """sload(key) 返回固定表达式，用来制造受控 mismatch。"""

    def __init__(self, value_expr):
        self._value_expr = value_expr

    def sload(self, _key):
        return self._value_expr


class _StubMState:
    def __init__(self, storage_value_expr, assumptions):
        self.evm_storage = _StubStorage(storage_value_expr)
        self.assumptions = assumptions


class _StubGlobalState:
    def __init__(self, condition, storage_value_expr, assumptions):
        self._constraints = _StubConstraints(condition)
        self.mstate = _StubMState(storage_value_expr, assumptions)

    def get_constraints(self):
        return self._constraints


def _case():
    # storage_check_keys 触发 _storage_mismatches（requires_state_comparison=True）；
    # expected_stack_height=None 保证 evm_state 只经 storage 被访问（不碰栈/SP）。
    return InstructionEquivalenceCase(
        name="PATH_ASSUMPTION_GUARD",
        evm_kind="STOP",
        arity=0,
        x86_core_hex="00",
        base_addr=0x1000,
        storage_check_keys=(0,),
        x86_execution_mode="cfg",
        x86_compare_terminal_paths=True,
        solver_timeout_ms=10_000,
    )


def test_path_local_assumption_does_not_leak_to_sibling_path(monkeypatch):
    """path A 的限制 assumption 不得越界约束 path B：assert 必须捕获 path B 反例。"""
    case = _case()

    # EVM 参照：storage[0] == 0（mstate 风格 stub；assumptions=None 表示无全局假设）。
    evm_state = _StubMState(storage_value_expr=BitVecVal(0, 256), assumptions=None)

    # path A：condition C，挂限制 assumption，storage 与 EVM 一致（本路径无 mismatch）。
    path_a = _StubGlobalState(
        condition=_C,
        storage_value_expr=BitVecVal(0, 256),
        assumptions=[_RESTRICT],
    )
    # path B：condition Not(C)，无 assumption；storage[0] 的高 192 位 = sym 高位、
    # 低 64 位恒为 0，故与 EVM 的 0 不等 ⟺ sym 高位非零 ⟺ **恰好**落在 path A 的
    # _RESTRICT（高位为 0）所排除的输入区。这样旧的全局加才会把 path B 的唯一反例
    # 区整片排除（假绿），而正确的 path-guard 不会。
    path_b_storage = Concat(Extract(255, 64, _SYM), BitVecVal(0, 64))
    path_b = _StubGlobalState(
        condition=_NOT_C,
        storage_value_expr=path_b_storage,
        assumptions=None,
    )

    monkeypatch.setattr(
        instruction_equivalence,
        "_build_evm_final_state",
        lambda *a, **k: evm_state,
    )
    monkeypatch.setattr(
        instruction_equivalence,
        "_build_x86_final_global_states",
        lambda *a, **k: [path_a, path_b],
    )

    try:
        assert_instruction_equivalent(case)
    except AssertionError:
        return  # 正确：path B 的反例被捕获

    raise AssertionError(
        "path B 的真实 mismatch 被藏成假绿：path A 的 path-local 限制 assumption "
        "越界约束了 sibling 路径，assert_instruction_equivalent 未能捕获反例。"
    )
