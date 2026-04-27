#!/usr/bin/env python3
"""测试固定栈槽位到 x86 内存窗口的映射。"""

from z3 import BitVecVal, is_true, simplify

from state.x86_state import X86MemoryState
from verification.memory_mapping import StackMemoryMapper


def _assert_bv_eq(actual, expected):
    assert is_true(simplify(actual == expected))


def test_slot_index_to_base_offset_two_slots():
    """两个固定槽位时，应从栈底开始落到 -0x40、-0x20。"""
    assert StackMemoryMapper.slot_index_to_base_offset(0, 2) == -0x40
    assert StackMemoryMapper.slot_index_to_base_offset(1, 2) == -0x20


def test_x86_memory_default_zero_initialized():
    """新建 x86 内存时，未写入字节默认应为 0。"""
    memory = X86MemoryState()

    _assert_bv_eq(memory.load_byte(BitVecVal(0, 64)), BitVecVal(0, 8))
    _assert_bv_eq(memory.load_byte(BitVecVal(0x1234, 64)), BitVecVal(0, 8))


def test_slot_index_to_base_offset_single_slot():
    """单槽位窗口时，唯一槽位应位于 -0x20。"""
    assert StackMemoryMapper.slot_index_to_base_offset(0, 1) == -0x20


def test_slot_index_to_base_offset_rejects_empty_window():
    """空栈不应直接调用槽位偏移 helper。"""
    try:
        StackMemoryMapper.slot_index_to_base_offset(0, 0)
    except ValueError as exc:
        assert "total_slots must be positive" in str(exc)
    else:
        raise AssertionError("expected ValueError for total_slots=0")


def test_initialize_x86_memory_from_stack_places_bottom_and_top_slots():
    """压栈顺序输入应显式落到从底部到顶部的固定槽位。"""
    base = BitVecVal(0x1000, 64)
    bottom_value = BitVecVal(0x11, 256)
    top_value = BitVecVal(0x22, 256)

    memory = X86MemoryState()
    initialized = StackMemoryMapper.initialize_x86_memory_from_stack(
        memory,
        [bottom_value, top_value],
        base=base,
    )

    _assert_bv_eq(
        initialized.load_256bit(base + BitVecVal(-0x40, 64)),
        bottom_value,
    )
    _assert_bv_eq(
        initialized.load_256bit(base + BitVecVal(-0x20, 64)),
        top_value,
    )


def test_initialize_x86_memory_from_stack_empty_stack_keeps_memory_unchanged():
    """空栈不应产生任何预填槽位写入。"""
    memory = X86MemoryState()
    initialized = StackMemoryMapper.initialize_x86_memory_from_stack(memory, [])
    assert initialized is memory


def test_extract_stack_from_x86_memory_round_trip_returns_bottom_to_top():
    """预置后再读取，应按固定槽位顺序返回从底部到顶部的值。"""
    base = BitVecVal(0x2000, 64)
    slot0 = BitVecVal(0x1234, 256)
    slot1 = BitVecVal(0x5678, 256)

    memory = X86MemoryState()
    initialized = StackMemoryMapper.initialize_x86_memory_from_stack(
        memory,
        [slot0, slot1],
        base=base,
    )
    extracted = StackMemoryMapper.extract_stack_from_x86_memory(
        initialized,
        2,
        base=base,
    )

    assert len(extracted) == 2
    _assert_bv_eq(extracted[0], slot0)
    _assert_bv_eq(extracted[1], slot1)
