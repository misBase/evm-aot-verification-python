"""host-gas 调用序号在 x86 合流点的合并（`_merge_at_confluence`）。

两条路径的 host 调用次数可以不同（一支执行过 SLOAD、另一支没有），合流后必须如实保留
成 `If(cond, 1, 0)`——直接取某一条会让后续序号对另一条路径是错的。

这条路径**现有 fixture 覆盖不到**：实测 perf_erc20_lite 的 143 次合并里只有 6 次是多
路径，且那 6 次两支 gas 逐位相同（绝大多数合流点是 uint256 多 limb 运算在 EVM block
内部的微观分支，不影响 host 调用次数）。所以只能直接构造状态测合并逻辑本身。
"""

from z3 import Bool, BitVecVal, If, Solver, simplify, unsat

from state.host_gas import next_host_gas_seq
from state.smt_state import SMTState
from x86_64.cfg_executor import X86SymbolicExecutor
from x86_64.cfg_state import X86GlobalState, X86WorldState


def _state_with_seq(cond, sload_calls: int) -> X86GlobalState:
    """造一个执行过 `sload_calls` 次 SLOAD、路径条件为 cond 的 x86 状态。"""
    mstate = SMTState.create_initial_state()
    mstate.host_gas_uf_enabled = True
    for _ in range(sload_calls):
        next_host_gas_seq(mstate, "SLOAD")
    world = X86WorldState()
    world.constraints.add(cond)
    return X86GlobalState(mstate=mstate, world_state=world)


def _merge(states):
    """只调合并逻辑本身，不跑符号执行（executor 只为拿到 _merge_at_confluence）。"""
    executor = X86SymbolicExecutor.__new__(X86SymbolicExecutor)

    class _Cfg:
        @staticmethod
        def get_or_create_node(_addr):
            return None

    executor.cfg = _Cfg()
    return X86SymbolicExecutor._merge_at_confluence(executor, 0x1000, states)


def _assert_semantically_eq(actual, expected):
    """按语义等价断言，不比 AST 外形——simplify 会改变形状。"""
    solver = Solver()
    solver.add(actual != expected)
    assert solver.check() == unsat, f"expected {expected}, got {actual}"


def test_divergent_seq_merges_into_if_chain():
    """一支执行过 SLOAD（seq→1）、一支没有（seq→0）→ 合流后是 If(cond, 1, 0)。"""
    cond = Bool("path_a")
    merged = _merge([
        _state_with_seq(cond, sload_calls=1),
        _state_with_seq(Bool("path_b"), sload_calls=0),
    ])

    _assert_semantically_eq(
        merged.mstate.host_gas_seq["SLOAD"],
        If(cond, BitVecVal(1, 256), BitVecVal(0, 256)),
    )


def test_seq_after_divergent_merge_keeps_advancing_per_branch():
    """合流之后再来一次 SLOAD：两支分别用序号 1 / 0，各自递增到 2 / 1。

    合并只是把两条历史装进一个表达式，后续计数必须在各自分支上继续、不能塌成具体值。"""
    cond = Bool("path_a")
    merged = _merge([
        _state_with_seq(cond, sload_calls=1),
        _state_with_seq(Bool("path_b"), sload_calls=0),
    ])

    used = next_host_gas_seq(merged.mstate, "SLOAD")
    _assert_semantically_eq(used, If(cond, BitVecVal(1, 256), BitVecVal(0, 256)))
    _assert_semantically_eq(
        merged.mstate.host_gas_seq["SLOAD"],
        If(cond, BitVecVal(2, 256), BitVecVal(1, 256)),
    )


def test_identical_seq_folds_to_constant():
    """两支序号相同 → 折成常量，不留 If。

    Z3 不会自动把 `If(c, 1, 1)` 折成 `1`，不折的话每个合流点都会无谓地堆一层。"""
    merged = _merge([
        _state_with_seq(Bool("path_a"), sload_calls=2),
        _state_with_seq(Bool("path_b"), sload_calls=2),
    ])

    seq = merged.mstate.host_gas_seq["SLOAD"]
    assert seq.eq(simplify(BitVecVal(2, 256))), (
        f"相同序号应折成常量 2，实际是 {seq}（simplify 漏了？）"
    )


def test_merge_without_any_seq_is_empty():
    """没有任何 host 调用时合并出空表，不会凭空造出计数器。"""
    merged = _merge([
        _state_with_seq(Bool("path_a"), sload_calls=0),
        _state_with_seq(Bool("path_b"), sload_calls=0),
    ])
    assert merged.mstate.host_gas_seq == {}
