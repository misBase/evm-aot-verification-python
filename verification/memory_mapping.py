"""
EVM栈和x86-64内存之间的内存映射。

本模块提供映射函数，用于在EVM栈表示和x86-64内存布局之间转换，
用于验证目的。
"""

from typing import List, Dict, Optional
from z3 import BitVec, BitVecVal, Concat, Extract
from common.uint256 import Uint256
from state.smt_state import SMTState, EVMStackState, X86MemoryState


class StackMemoryMapper:
    """在EVM栈和x86-64内存布局之间映射。

    这里的 R14 不是整个物理栈的起点，而是"当前 block 的栈基准"。
    当前逻辑栈顶 stack[0] 的基址取决于当前 sp，本模块只建模一种特例：
    block 入口且 sp=0 时预置的已有栈窗口。此时：

    - stack[0] -> [R14-0x20 .. R14-0x08]
    - stack[1] -> [R14-0x40 .. R14-0x28]
    - stack[2] -> [R14-0x60 .. R14-0x48]
    """

    # x86内存中栈元素的基址偏移量
    # 每个栈元素占用32字节（4×64位limb）
    LIMBS_PER_UINT256 = 4
    LIMB_SIZE = 8  # 字节
    STACK_ELEMENT_SIZE = 32  # 字节
    STACK_TOP_BASE_OFFSET = -0x20  # 仅用于 block 入口且 sp=0 时的预置 stack[0] 基址

    @staticmethod
    def stack_index_to_base_offset(stack_index: int) -> int:
        """将栈索引转换为x86内存基址偏移量。

        Args:
            stack_index: EVM栈索引（0 = 栈顶）

        Returns:
            在 block 入口且 sp=0 的预置栈窗口中，栈元素相对于 R14 的基址偏移量
        """
        if stack_index < 0:
            raise ValueError(f"stack_index must be non-negative, got {stack_index}")
        return StackMemoryMapper.STACK_TOP_BASE_OFFSET - (
            stack_index * StackMemoryMapper.STACK_ELEMENT_SIZE
        )

    @staticmethod
    def stack_to_memory_layout(stack_value: BitVec, stack_index: int) -> Dict[int, BitVec]:
        """将EVM栈值转换为x86内存布局。

        Args:
            stack_value: 表示栈元素的256位BitVec
            stack_index: 栈索引（0 = 栈顶）

        Returns:
            将内存偏移量映射到64位limb的字典
            {base_offset: z0, base_offset+8: z1, base_offset+16: z2, base_offset+24: z3}

        注意：x86内存现在是字节可寻址的（Array[BitVec[64], BitVec[8]]），
        但此函数为方便起见返回64位limb。limb将按小端序存储为每个8字节。
        """
        if stack_value.size() != 256:
            raise ValueError(f"Stack value must be 256 bits, got {stack_value.size()}")

        # 获取此栈元素的基址偏移量
        base_offset = StackMemoryMapper.stack_index_to_base_offset(stack_index)

        # 从256位值中提取4个limb
        z0 = Extract(63, 0, stack_value)    # LSB
        z1 = Extract(127, 64, stack_value)
        z2 = Extract(191, 128, stack_value)
        z3 = Extract(255, 192, stack_value)  # MSB

        # 映射到x86内存偏移量
        return {
            base_offset: z0,
            base_offset + 8: z1,
            base_offset + 16: z2,
            base_offset + 24: z3,
        }

    @staticmethod
    def memory_to_stack_value(memory: X86MemoryState, stack_index: int) -> BitVec:
        """从x86内存布局中提取EVM栈值。

        Args:
            memory: 包含内存值的X86MemoryState
            stack_index: 栈索引（0 = 栈顶）

        Returns:
            表示栈元素的256位BitVec
        """
        # 获取此栈元素的基址偏移量
        base_offset = StackMemoryMapper.stack_index_to_base_offset(stack_index)

        # 从内存加载4个limb
        z0 = memory.load_limb(base_offset)
        z1 = memory.load_limb(base_offset + 8)
        z2 = memory.load_limb(base_offset + 16)
        z3 = memory.load_limb(base_offset + 24)

        # 连接形成256位值：[z3|z2|z1|z0]
        return Concat(z3, z2, z1, z0)

    @staticmethod
    def initialize_x86_memory_from_stack(
        x86_memory: X86MemoryState,
        stack_values: List[BitVec],
        base: Optional[BitVec] = None,
    ) -> X86MemoryState:
        """从EVM栈值初始化x86内存。

        Args:
            x86_memory: 要初始化的X86MemoryState
            stack_values: 256位BitVec栈值列表
            base: 栈基址（R14），偏移量相对于该值计算；为 None 时使用 0

        Returns:
            具有初始化内存的新X86MemoryState
        """
        base_bv = base if base is not None else BitVecVal(0, 64)
        new_memory = x86_memory
        stack_depth = len(stack_values)
        for push_index, stack_value in enumerate(stack_values):
            # stack_values 按"压栈顺序"给出：最后一个元素是逻辑栈顶。
            stack_index = stack_depth - 1 - push_index
            rel_offset = StackMemoryMapper.stack_index_to_base_offset(stack_index)
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
        num_elements: int
    ) -> List[BitVec]:
        """从x86内存中提取EVM栈值。
        
        Args:
            x86_memory: 包含内存值的X86MemoryState
            num_elements: 要提取的栈元素数量
            
        Returns:
            256位BitVec栈值列表，按 EVM 逻辑顺序返回（0 = 栈顶）
        """
        stack_values = []
        for stack_index in range(num_elements):
            stack_value = StackMemoryMapper.memory_to_stack_value(x86_memory, stack_index)
            stack_values.append(stack_value)
        return stack_values


def stack_to_memory_layout(stack_value: BitVec, stack_index: int) -> Dict[int, BitVec]:
    """便利函数：将栈值转换为内存布局。

    Args:
        stack_value: 256位BitVec
        stack_index: 栈索引

    Returns:
        将偏移量映射到limb的字典
    """
    return StackMemoryMapper.stack_to_memory_layout(stack_value, stack_index)


def memory_to_stack_value(memory: X86MemoryState, stack_index: int) -> BitVec:
    """便利函数：从内存中提取栈值。

    Args:
        memory: X86MemoryState
        stack_index: 栈索引

    Returns:
        256位BitVec
    """
    return StackMemoryMapper.memory_to_stack_value(memory, stack_index)
