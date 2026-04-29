#!/usr/bin/env python3
"""RefinementChecker 当前 return-data 抽象边界的 characterization tests。"""

from z3 import Array, BitVecSort, BitVecVal, BoolVal, Store

from verification.refinement_checker import RefinementChecker


def _make_checker() -> RefinementChecker:
    return RefinementChecker(timeout_ms=10000, verbose=False)


def _make_result(*, offset: int, length: int, memory, base_addr: int | None, has_return_data: bool) -> dict:
    result = {
        "offset": BitVecVal(offset, 64),
        "length": BitVecVal(length, 64),
        "memory": memory,
        "base_addr": None if base_addr is None else BitVecVal(base_addr, 64),
        "has_return_data": BoolVal(has_return_data),
    }
    return result


def test_return_and_revert_with_same_return_data_are_equivalent_under_current_abstraction():
    """当前抽象只看非空 return data，不区分 RETURN 与 REVERT。"""
    checker = _make_checker()
    evm_memory = Store(
        Array("return_vs_revert_evm_mem", BitVecSort(64), BitVecSort(8)),
        BitVecVal(0, 64),
        BitVecVal(0xAB, 8),
    )
    x86_memory = Store(
        Array("return_vs_revert_x86_mem", BitVecSort(64), BitVecSort(8)),
        BitVecVal(0, 64),
        BitVecVal(0xAB, 8),
    )

    # 在更完整的语义里，这两边可以分别来自 RETURN 和 REVERT。
    # 当前 checker 只观察 (offset, length, bytes) 元组，因此会判等价。
    evm_result = _make_result(
        offset=0,
        length=1,
        memory=evm_memory,
        base_addr=None,
        has_return_data=True,
    )
    x86_result = _make_result(
        offset=0,
        length=1,
        memory=x86_memory,
        base_addr=0,
        has_return_data=True,
    )

    verified, msg = checker.check_refinement(evm_result, x86_result)

    assert verified, msg


def test_stop_and_zero_length_return_are_equivalent_under_current_abstraction():
    """当前抽象把 STOP 与 RETURN(0, 0) 都视为“不暴露非空 return data”。"""
    checker = _make_checker()
    evm_memory = Array("stop_vs_zero_return_evm_mem", BitVecSort(64), BitVecSort(8))
    x86_memory = Array("stop_vs_zero_return_x86_mem", BitVecSort(64), BitVecSort(8))

    # 在更完整的语义里，这两边可以分别来自 RETURN(0, 0) 和 STOP。
    # 当前 checker 只观察 length != 0，因此会判等价。
    evm_result = _make_result(
        offset=0,
        length=0,
        memory=evm_memory,
        base_addr=None,
        has_return_data=False,
    )
    x86_result = _make_result(
        offset=0,
        length=0,
        memory=x86_memory,
        base_addr=0,
        has_return_data=False,
    )

    verified, msg = checker.check_refinement(evm_result, x86_result)

    assert verified, msg
