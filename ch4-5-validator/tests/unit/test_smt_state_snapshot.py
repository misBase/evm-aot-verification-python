"""`SMTState.snapshot_for_error_branch()` 的契约测试。

这是 `SMTState.copy()` 的 `pending_errors` fail-closed 守卫的**唯一合法豁免**，
所以豁免本身要证明三件事：守卫没被削弱、异常路径也能还原队列、还回去的是原对象。

队列内容为空、连续快照互不共享对象这两条已由
`tests/unit/test_gas_error_codes.py` 的 `TestChargeDynamicGasE4` 覆盖，这里不重复。
"""

import pytest
from z3 import BoolVal

from evm_ir.status_code import EvmStatusCode
from state.smt_state import PendingErrorBranch, SMTState
from utils.exceptions import LogicError


def _state_with_pending_error():
    state = SMTState.create_initial_state()
    state.pending_errors.append(
        PendingErrorBranch(
            condition=BoolVal(True),
            status_code=EvmStatusCode.OUT_OF_GAS,
            terminal_state=SMTState.create_initial_state(),
        )
    )
    return state


def test_copy_guard_still_fails_closed():
    """豁免存在不代表守卫可以放松：普通 copy() 遇到未消费队列仍必须抛。"""
    state = _state_with_pending_error()
    with pytest.raises(LogicError, match="unconsumed"):
        state.copy()


def test_snapshot_bypasses_guard():
    state = _state_with_pending_error()
    snapshot = state.snapshot_for_error_branch()
    assert isinstance(snapshot, SMTState)
    assert snapshot is not state


def test_queue_restored_as_the_same_list_object():
    """必须还回**原列表对象**，不能是等值的新列表。

    调用方（charge_dynamic_gas / RETURNDATACOPY errPoint）在拍完快照后继续
    `state.pending_errors.append(...)`；若这里换成新列表，此前别处持有的引用就会
    指向一个再也不会被消费的队列——错误路径静默消失，正是守卫要防的事。
    """
    state = _state_with_pending_error()
    original_list = state.pending_errors
    original_contents = list(original_list)

    state.snapshot_for_error_branch()

    assert state.pending_errors is original_list
    assert state.pending_errors == original_contents


def test_queue_restored_even_if_copy_raises(monkeypatch):
    """copy() 内部抛异常时，finally 仍要把队列还回去。

    否则一次失败的快照就会把 state 洗成空队列，后续 copy() 不再报错——
    fail-closed 守卫被一个异常悄悄绕过。
    """
    state = _state_with_pending_error()
    original_list = state.pending_errors

    def boom(self):
        raise RuntimeError("copy exploded")

    monkeypatch.setattr(SMTState, "copy", boom)

    with pytest.raises(RuntimeError, match="copy exploded"):
        state.snapshot_for_error_branch()

    assert state.pending_errors is original_list
    assert len(state.pending_errors) == 1
