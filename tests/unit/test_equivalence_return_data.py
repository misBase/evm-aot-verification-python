#!/usr/bin/env python3
"""刻画 EquivalenceChecker 当前 return-data 抽象边界的测试。"""

from z3 import Array, BitVec, BitVecSort, BitVecVal, BoolVal, K, Store

from evm_ir.status_code import EvmStatusCode
from verification.equivalence_checker import EquivalenceChecker


def _make_checker() -> EquivalenceChecker:
    return EquivalenceChecker(timeout_ms=10000, verbose=False)


def _make_result(
    *,
    offset: int,
    length: int,
    memory,
    base_addr: int | None,
    has_return_data: bool,
    status_code: int | None = EvmStatusCode.RETURNED,
) -> dict:
    result = {
        "offset": BitVecVal(offset, 64),
        "length": BitVecVal(length, 64),
        "memory": memory,
        "base_addr": None if base_addr is None else BitVecVal(base_addr, 64),
        "has_return_data": BoolVal(has_return_data),
    }
    # status_code=None 用来构造"producer 漏传"的场景，验证 fail-closed。
    if status_code is not None:
        result["status_code"] = BitVecVal(status_code, 8)
    return result


def test_return_and_revert_with_same_return_data_are_equivalent_under_current_abstraction():
    """status code 相同时，return-data 抽象只看非空 return data 的 (offset, length, bytes)。"""
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

    # 两侧 status code 相同（都记为 RETURNED）时，checker 只观察
    # (offset, length, bytes) 元组，因此判等价；status code 不同的情形
    # 由 test_status_code_mismatch_is_counterexample 覆盖。
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

    verified, msg = checker.check_equivalence(evm_result, x86_result)

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

    verified, msg = checker.check_equivalence(evm_result, x86_result)

    assert verified, msg


def test_zero_length_fast_path_still_checks_return_presence():
    checker = _make_checker()
    evm_memory = Array("zero_len_presence_evm_mem", BitVecSort(64), BitVecSort(8))
    x86_memory = Array("zero_len_presence_x86_mem", BitVecSort(64), BitVecSort(8))

    evm_result = _make_result(
        offset=0,
        length=0,
        memory=evm_memory,
        base_addr=None,
        has_return_data=False,
    )
    x86_result = _make_result(
        offset=0,
        length=32,
        memory=x86_memory,
        base_addr=0,
        has_return_data=True,
    )

    verified, msg = checker.check_equivalence(evm_result, x86_result)

    assert not verified
    assert "Non-empty return-data conditions differ" in msg


def test_symbolic_later_store_alias_is_not_hidden_by_memory_select_cache():
    checker = _make_checker()
    symbolic_offset = BitVec("return_byte_symbolic_alias", 64)
    zero = BitVecVal(0, 64)
    base = K(BitVecSort(64), BitVecVal(0, 8))
    evm_memory = Store(
        Store(base, zero, BitVecVal(0xAA, 8)),
        symbolic_offset,
        BitVecVal(0xBB, 8),
    )
    x86_memory = Store(base, zero, BitVecVal(0xAA, 8))

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

    verified, msg = checker.check_equivalence(
        evm_result,
        x86_result,
        assumptions=symbolic_offset == zero,
    )

    assert not verified
    assert "memory contents differ" in msg


def _zero_length_result(*, memory, base_addr: int | None, status_code) -> dict:
    """两侧完全相同、零长度返回的 observable，只有 status code 可能不同。"""
    return _make_result(
        offset=0,
        length=0,
        memory=memory,
        base_addr=base_addr,
        has_return_data=False,
        status_code=status_code,
    )


def test_status_code_mismatch_is_counterexample():
    """return data 完全一致但终止状态码不同，必须报反例而不是判等价。"""
    checker = _make_checker()
    memory = K(BitVecSort(64), BitVecVal(0, 8))

    evm_result = _zero_length_result(
        memory=memory, base_addr=None, status_code=EvmStatusCode.REVERTED
    )
    x86_result = _zero_length_result(
        memory=memory, base_addr=0, status_code=EvmStatusCode.STOPPED
    )

    verified, msg = checker.check_equivalence(evm_result, x86_result)

    assert not verified
    assert "termination status codes differ" in msg


def test_missing_status_code_is_fail_closed():
    """任一侧漏传 status_code 必须判失败，不能退化成缺省值互相比较。"""
    checker = _make_checker()
    memory = K(BitVecSort(64), BitVecVal(0, 8))

    evm_result = _zero_length_result(memory=memory, base_addr=None, status_code=None)
    x86_result = _zero_length_result(
        memory=memory, base_addr=0, status_code=EvmStatusCode.RETURNED
    )

    verified, msg = checker.check_equivalence(evm_result, x86_result)

    assert not verified
    assert "cannot verify termination status" in msg
    assert "missing on EVM side" in msg


def test_both_sides_missing_status_code_is_fail_closed():
    """两侧同时漏传（并行 worker 丢键的形态）也必须判失败。"""
    checker = _make_checker()
    memory = K(BitVecSort(64), BitVecVal(0, 8))

    evm_result = _zero_length_result(memory=memory, base_addr=None, status_code=None)
    x86_result = _zero_length_result(memory=memory, base_addr=0, status_code=None)

    verified, msg = checker.check_equivalence(evm_result, x86_result)

    assert not verified
    assert "cannot verify termination status" in msg


def test_status_code_with_wrong_width_is_fail_closed():
    """位宽不对时给出明确信息，而不是让 Z3 抛 sort mismatch。"""
    checker = _make_checker()
    memory = K(BitVecSort(64), BitVecVal(0, 8))

    evm_result = _zero_length_result(
        memory=memory, base_addr=None, status_code=EvmStatusCode.RETURNED
    )
    x86_result = _zero_length_result(
        memory=memory, base_addr=0, status_code=EvmStatusCode.RETURNED
    )
    x86_result["status_code"] = BitVecVal(0, 32)

    verified, msg = checker.check_equivalence(evm_result, x86_result)

    assert not verified
    assert "cannot verify termination status" in msg
    assert "width is 32" in msg
