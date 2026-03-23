"""
用于Z3公式建模的SMT状态管理。

本模块为EVM IR和x86-64程序提供统一的状态管理，
将栈、内存和寄存器建模为符号变量。
"""

from z3 import BitVec, Array, BitVecSort

from state.evm_stack_state import EVMStackState
from state.evm_memory_state import EVMMemoryState
from state.evm_storage_state import EVMStorageState
from state.evm_gas_state import EVMGasState
from state.x86_state import X86MemoryState, X86RegisterState

# 为了向后兼容，重新导出所有子类
__all__ = [
    'SMTState',
    'EVMStackState',
    'EVMMemoryState',
    'EVMStorageState',
    'EVMGasState',
    'X86MemoryState',
    'X86RegisterState',
]


class SMTState:
    """用于程序验证的统一SMT状态。

    管理所有符号状态：EVM栈/内存/Storage/Gas、x86内存/寄存器。
    """

    def __init__(self):
        """初始化统一SMT状态。"""
        self.evm_stack = EVMStackState()
        self.evm_memory = EVMMemoryState()
        self.evm_storage = EVMStorageState()
        self.evm_gas = EVMGasState()
        self.x86_memory = X86MemoryState()
        self.x86_registers = X86RegisterState()

        # RETURN指令跟踪
        # 存储偏移量和长度而不是提取Array
        # 这允许直接内存比较，没有max_bytes限制
        # 使用条件符号值：0表示无返回值
        from z3 import BitVecVal
        self.return_offset: BitVec = BitVecVal(0, 64)  # 返回偏移量（64位），0 = 无返回
        self.return_length: BitVec = BitVecVal(0, 64)  # 返回长度（64位），0 = 无返回

        # PC（程序计数器）
        self.pc: int = 0

        # 环境信息
        self.calldata = Array('CallData', BitVecSort(64), BitVecSort(8))
        self.calldatasize = BitVec('CallDataSize', 256)
        self.callvalue = BitVec('CallValue', 256)
        self.basefee = BitVec('BaseFee', 256)

    @classmethod
    def _create_empty(cls) -> 'SMTState':
        """创建空的SMTState实例，跳过__init__以避免不必要的Z3对象创建。

        Returns:
            未初始化字段的SMTState实例
        """
        return cls.__new__(cls)

    def copy(self) -> 'SMTState':
        """创建状态的副本。

        Returns:
            新SMTState实例
        """
        new_state = SMTState._create_empty()
        new_state.evm_stack = self.evm_stack.copy()
        new_state.evm_memory = self.evm_memory.copy()
        new_state.evm_storage = self.evm_storage.copy()
        new_state.evm_gas = self.evm_gas.copy()
        new_state.x86_memory = self.x86_memory.copy()
        new_state.x86_registers = self.x86_registers.copy()
        new_state.return_offset = self.return_offset
        new_state.return_length = self.return_length
        new_state.pc = self.pc

        # 复制环境信息
        new_state.calldata = self.calldata
        new_state.calldatasize = self.calldatasize
        new_state.callvalue = self.callvalue
        new_state.basefee = self.basefee

        return new_state

    @staticmethod
    def create_initial_state(num_inputs: int = 2) -> 'SMTState':
        """创建具有符号输入的初始SMT状态。

        创建一个新状态，包含：
        - EVM栈上的指定数量的符号256位值
        - 映射到x86内存布局的EVM栈

        Args:
            num_inputs: 要创建的符号输入数量（默认2，适用于二元操作如ADD、SUB等）

        Returns:
            具有符号输入的已初始化SMTState

        Raises:
            ValueError: 如果num_inputs为负数或过大（>1024）
        """
        # Lazy imports to avoid circular dependencies
        from common.uint256 import Uint256
        from verification.memory_mapping import StackMemoryMapper
        from z3 import IntVal, BitVecVal
        from x86_64.models import Register

        # 验证输入数量
        if num_inputs < 0:
            raise ValueError(f"num_inputs must be non-negative, got {num_inputs}")
        if num_inputs > 1024:
            raise ValueError(f"num_inputs must be <= 1024 (EVM stack limit), got {num_inputs}")

        # 创建基础状态
        initial_state = SMTState()

        # 与AOT约定对齐：
        # R13: callEngine基址，R14: stack基址，R15: memory基址
        # 在验证环境中统一设为0，便于与相对偏移建模拼接。
        zero_64 = BitVecVal(0, 64)
        initial_state.x86_registers.set_register(Register.R13, zero_64)
        initial_state.x86_registers.set_register(Register.R14, zero_64)
        initial_state.x86_registers.set_register(Register.R15, zero_64)

        # 初始化callEngine中会被预热代码读取的关键字段：
        # [R13+16]  = memoryElement0Address
        # [R13+48]  = stackBasePointerInBytes
        # [R13+56]  = stackElement0Address
        initial_state.x86_memory = initial_state.x86_memory.store_limb(16, zero_64)
        initial_state.x86_memory = initial_state.x86_memory.store_limb(48, zero_64)
        initial_state.x86_memory = initial_state.x86_memory.store_limb(56, zero_64)

        # 使用SP = 0初始化EVM栈
        initial_state.evm_stack = EVMStackState(initial_depth=0, sp=IntVal(0))

        # 如果没有输入，直接返回空状态
        if num_inputs == 0:
            return initial_state

        # 为EVM栈创建符号输入
        input_stack = []
        for i in range(num_inputs):
            val = Uint256.symbolic(f"program_input_{i}")
            input_stack.append(val.to_bv256())

        # 推送初始栈值
        for stack_val in input_stack:
            initial_state.evm_stack = initial_state.evm_stack.push(stack_val)

        # 将EVM栈输入映射到x86内存布局
        for stack_index, stack_value in enumerate(input_stack):
            layout = StackMemoryMapper.stack_to_memory_layout(stack_value, stack_index)
            for offset, limb in layout.items():
                initial_state.x86_memory = initial_state.x86_memory.store_limb(offset, limb)

        return initial_state
