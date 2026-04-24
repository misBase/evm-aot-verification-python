"""
EVM 固定栈槽位和 x86-64 内存窗口之间的映射。

本模块服务于 create_initial_state() 预置的“固定槽位窗口”：

- 初始栈深为 N 时，预置窗口覆盖 [base - N*0x20, ..., base - 0x20]
- 槽位编号从栈底开始：slot 0 是最底部，slot N-1 是最顶部
- 当 N = 0 时，没有预填的负偏移槽位；若后续需要定义第一个槽位，其起点是 base + 0

这个约定与 RefinementChecker.check_stack_equivalence() 保持一致：
mapper 负责建立/读取初始固定槽位窗口，checker 负责按相同的固定槽位约定比较最终状态。
二者都不建模运行时随 SP 变化的逻辑栈顶，只关注固定槽位。
"""

from typing import Dict, List, Optional

from z3 import BitVec, BitVecVal, Concat, Extract

from state.x86_state import X86MemoryState


class StackMemoryMapper:
    """在 EVM 固定栈槽位和 x86-64 内存窗口之间映射。"""

    LIMBS_PER_UINT256 = 4
    LIMB_SIZE = 8
    STACK_ELEMENT_SIZE = 32

    @staticmethod
    def slot_index_to_base_offset(slot_index: int, total_slots: int) -> int:
        """返回固定槽位相对于 base 的起始偏移。

        Args:
            slot_index: 固定槽位编号（0 = 最底部）
            total_slots: 固定槽位总数

        Returns:
            该槽位相对于 base 的起始偏移

        Examples:
            total_slots=2: slot 0 -> -0x40, slot 1 -> -0x20
            total_slots=1: slot 0 -> -0x20

        Notes:
            total_slots=0 时不应调用本函数；空栈表示“下一个槽位从 base + 0 开始”。
        """
        if total_slots <= 0:
            raise ValueError(f"total_slots must be positive, got {total_slots}")
        if slot_index < 0:
            raise ValueError(f"slot_index must be non-negative, got {slot_index}")
        if slot_index >= total_slots:
            raise ValueError(
                f"slot_index must be smaller than total_slots, got {slot_index} >= {total_slots}"
            )
        return -(total_slots - slot_index) * StackMemoryMapper.STACK_ELEMENT_SIZE

    @staticmethod
    def stack_to_memory_layout(
        stack_value: BitVec,
        slot_index: int,
        total_slots: int,
    ) -> Dict[int, BitVec]:
        """将一个 256-bit 栈值映射到固定槽位布局。

        Args:
            stack_value: 256-bit BitVec 值
            slot_index: 固定槽位编号（0 = 最底部）
            total_slots: 固定槽位总数

        Returns:
            相对 base 的 64-bit limb 布局
        """
        if stack_value.size() != 256:
            raise ValueError(f"Stack value must be 256 bits, got {stack_value.size()}")

        base_offset = StackMemoryMapper.slot_index_to_base_offset(slot_index, total_slots)
        z0 = Extract(63, 0, stack_value)
        z1 = Extract(127, 64, stack_value)
        z2 = Extract(191, 128, stack_value)
        z3 = Extract(255, 192, stack_value)
        return {
            base_offset: z0,
            base_offset + 8: z1,
            base_offset + 16: z2,
            base_offset + 24: z3,
        }

    @staticmethod
    def memory_to_stack_value(
        memory: X86MemoryState,
        slot_index: int,
        total_slots: int,
        base: Optional[BitVec] = None,
    ) -> BitVec:
        """从固定槽位窗口读取一个 256-bit 栈值。

        Args:
            memory: X86MemoryState
            slot_index: 固定槽位编号（0 = 最底部）
            total_slots: 固定槽位总数
            base: 栈窗口基址；为 None 时使用 0
        """
        base_bv = base if base is not None else BitVecVal(0, 64)
        base_offset = StackMemoryMapper.slot_index_to_base_offset(slot_index, total_slots)
        absolute_base = base_bv + BitVecVal(base_offset, 64)
        z0 = memory.load_limb(absolute_base)
        z1 = memory.load_limb(absolute_base + BitVecVal(8, 64))
        z2 = memory.load_limb(absolute_base + BitVecVal(16, 64))
        z3 = memory.load_limb(absolute_base + BitVecVal(24, 64))
        return Concat(z3, z2, z1, z0)

    @staticmethod
    def initialize_x86_memory_from_stack(
        x86_memory: X86MemoryState,
        stack_values: List[BitVec],
        base: Optional[BitVec] = None,
    ) -> X86MemoryState:
        """按固定槽位窗口布局预置 x86 内存。

        `stack_values` 按“压栈顺序”给出，最后一个元素是逻辑栈顶。
        写入时会将它们重新编号为固定槽位：

        - 第一个压入的值 -> slot 0（最底部）
        - 最后一个压入的值 -> slot N-1（最顶部）

        当 N=0 时，不写入任何预置槽位。
        """
        base_bv = base if base is not None else BitVecVal(0, 64)
        new_memory = x86_memory
        total_slots = len(stack_values)

        for slot_index, stack_value in enumerate(stack_values):
            rel_offset = StackMemoryMapper.slot_index_to_base_offset(slot_index, total_slots)
            abs_base = base_bv + BitVecVal(rel_offset, 64)
            z0 = Extract(63, 0, stack_value)
            z1 = Extract(127, 64, stack_value)
            z2 = Extract(191, 128, stack_value)
            z3 = Extract(255, 192, stack_value)
            layout = {
                abs_base: z0,
                abs_base + BitVecVal(8, 64): z1,
                abs_base + BitVecVal(16, 64): z2,
                abs_base + BitVecVal(24, 64): z3,
            }
            for addr, limb in layout.items():
                new_memory = new_memory.store_limb(addr, limb)

        return new_memory

    @staticmethod
    def extract_stack_from_x86_memory(
        x86_memory: X86MemoryState,
        num_elements: int,
        base: Optional[BitVec] = None,
    ) -> List[BitVec]:
        """从固定槽位窗口读取多个 256-bit 栈值。

        Returns:
            按固定槽位顺序返回，即从底部到顶部。
        """
        if num_elements < 0:
            raise ValueError(f"num_elements must be non-negative, got {num_elements}")

        stack_values = []
        for slot_index in range(num_elements):
            stack_values.append(
                StackMemoryMapper.memory_to_stack_value(
                    x86_memory,
                    slot_index,
                    num_elements,
                    base=base,
                )
            )
        return stack_values


def stack_to_memory_layout(
    stack_value: BitVec,
    slot_index: int,
    total_slots: int,
) -> Dict[int, BitVec]:
    """便利函数：将单个固定槽位值转换为相对 base 的 limb 布局。"""
    return StackMemoryMapper.stack_to_memory_layout(stack_value, slot_index, total_slots)


def memory_to_stack_value(
    memory: X86MemoryState,
    slot_index: int,
    total_slots: int,
    base: Optional[BitVec] = None,
) -> BitVec:
    """便利函数：从固定槽位窗口读取单个 256-bit 值。"""
    return StackMemoryMapper.memory_to_stack_value(
        memory,
        slot_index,
        total_slots,
        base=base,
    )
