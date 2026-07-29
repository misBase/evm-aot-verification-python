"""
用于Z3公式建模的SMT状态管理。

本模块为EVM IR和x86-64程序提供统一的状态管理，
将栈、内存和寄存器建模为符号变量。
"""

from typing import Optional, Set

from z3 import BitVec, BitVecVal, Array, BitVecSort

from state.evm_stack_state import EVMStackState
from state.evm_memory_state import EVMMemoryState
from state.evm_storage_state import EVMStorageState
from state.evm_transient_storage_state import EVMTransientStorageState
from state.evm_gas_state import EVMGasState
from state.x86_state import (
    MemoryDomain,
    MemoryDomainError,
    PointerTag,
    X86MemoryState,
    X86RegisterState,
)

# 为了向后兼容，重新导出所有子类
__all__ = [
    'SMTState',
    'EVMStackState',
    'EVMMemoryState',
    'EVMStorageState',
    'EVMTransientStorageState',
    'EVMGasState',
    'X86MemoryState',
    'X86RegisterState',
    'MemoryDomain',
    'MemoryDomainError',
    'PointerTag',
]


class SMTState:
    """用于程序验证的统一SMT状态。

    管理所有符号状态：EVM栈/内存/Storage/Gas、x86内存/寄存器。
    """

    CALLENGINE_SIDE_CHANNEL_FIELDS = (
        "callengine_memory_base",
        "callengine_memory_size_bytes",
        "callengine_memory_gas_used",
        "callengine_stack_pointer_limbs",
        "callengine_stack_byte_offset",
        "callengine_stack_base",
        "callengine_callvalue",
        "callengine_gas_remaining",
        "callengine_self_address_pointer",
        "callengine_origin_address_pointer",
        "callengine_caller_address_pointer",
        "callengine_input_pointer",
        "callengine_input_size_bytes",
        "callengine_code_pointer",
        "callengine_code_size_bytes",
        "callengine_return_data_pointer",
        "callengine_return_data_size_bytes",
        "callengine_status_code",
        "callengine_builtin_func_index",
        "callengine_go_func_index",
        "callengine_return_address",
        "callengine_builtin_arg0",
    )

    ENVIRONMENT_FIELDS = (
        "calldata",
        "code",
        "return_data",
        "calldatasize",
        "callvalue",
        "basefee",
        "self_address",
        "origin_address",
        "caller_address",
        "block_timestamp",
        "block_number",
        "gaslimit",
        "blobbasefee",
    )

    OPTIONAL_ENVIRONMENT_FIELDS = (
        "blobhash_count",
    )

    def __init__(self):
        """初始化统一SMT状态。"""
        # EVM IR 的逻辑执行状态：用于符号化 EVM IR 的栈/内存语义。
        # x86 路径不直接操作这两个字段，而是使用 x86_memory 的 STACK/EVM 域。
        self.evm_stack = EVMStackState()
        self.evm_memory = EVMMemoryState()

        # x86 执行视图：用于符号化编译后机器码的内存/寄存器状态投影。
        # 这些字段服务于 x86 指令级执行，不等同于上面的逻辑 EVM 状态。
        self.x86_memory = X86MemoryState()
        self.x86_registers = X86RegisterState()

        # 统一语义状态中的 contract storage；名称里的 evm 强调语义来源，
        # 不是指“仅 EVM 侧私有”，x86 host 语义也会读写它。
        self.evm_storage = EVMStorageState()
        self.evm_transient_storage = EVMTransientStorageState()
        self.evm_gas = EVMGasState()

        # RETURN/REVERT 数据跟踪
        # 存储偏移量和长度而不是提取Array
        # 这允许直接内存比较，没有max_bytes限制
        # 当前抽象下，0 长度表示“不暴露非空 return data”
        self.return_offset: BitVec = BitVecVal(0, 64)  # 返回偏移量（64位）
        self.return_length: BitVec = BitVecVal(0, 64)  # 返回长度（64位），0 表示当前抽象下不暴露非空 return data
        self.error_string: Optional[str] = None      # EVM 执行错误或回滚原因字符串
        self.error_code: BitVec = BitVecVal(0, 8)     # EVM 执行状态码，0=RETURNED，与 callengine_status_code 对齐
        self.read_only: bool = False                 # todo: 可能无用,只用于跨合约调用
        self.valid_jump_targets: Optional[Set[int]] = None  # TAG is_jump_target=True 的 PC 集合

        # callEngine 字段的显式 side-channel。
        # x86 指令执行器识别到 mov [r13+KNOWN_OFFSET], ... 时同步更新这些字段，
        # 同时保留对 x86_memory 的写入（side-channel 是冗余快路径）。
        # 目的：让栈一致性检查、状态码检查直接读 BitVec 字段，
        # 避免 Z3 穿透 100+ 层 Memory Store 链做 array 理论推理。
        self.callengine_memory_base:         BitVec = BitVecVal(0, 64)   # [R13+0x10]
        self.callengine_memory_size_bytes:   BitVec = BitVecVal(0, 64)   # [R13+0x18]
        self.callengine_memory_gas_used:     BitVec = BitVecVal(0, 64)   # [R13+0x20]
        self.callengine_stack_pointer_limbs: BitVec = BitVecVal(0, 64)   # [R13+0x28]
        self.callengine_stack_byte_offset:   BitVec = BitVecVal(0, 64)   # [R13+0x30]
        self.callengine_stack_base:          BitVec = BitVecVal(0, 64)   # [R13+0x38]
        self.callengine_callvalue:           BitVec = BitVecVal(0, 64)   # [R13+0x68]
        self.callengine_gas_remaining:       BitVec = BitVecVal(0, 64)   # [R13+0x70]
        self.callengine_self_address_pointer: BitVec = BitVecVal(0, 64)  # [R13+0x78]
        self.callengine_origin_address_pointer: BitVec = BitVecVal(0, 64)  # [R13+0x80]
        self.callengine_caller_address_pointer: BitVec = BitVecVal(0, 64)  # [R13+0x88]
        self.callengine_input_pointer:       BitVec = BitVecVal(0, 64)   # [R13+0x90]
        self.callengine_input_size_bytes:    BitVec = BitVecVal(0, 64)   # [R13+0x98]
        self.callengine_code_pointer:        BitVec = BitVecVal(0, 64)   # [R13+0xA0]
        self.callengine_code_size_bytes:     BitVec = BitVecVal(0, 64)   # [R13+0xA8]
        self.callengine_return_data_pointer: BitVec = BitVecVal(0, 64)   # [R13+0xB0]
        self.callengine_return_data_size_bytes: BitVec = BitVecVal(0, 64)  # [R13+0xB8]
        self.callengine_status_code:         BitVec = BitVecVal(0, 8)    # [R13+0xE0]
        self.callengine_builtin_func_index:  BitVec = BitVecVal(0, 32)   # [R13+0xE4]
        self.callengine_go_func_index:       BitVec = BitVecVal(0, 32)   # [R13+0xE8]
        self.callengine_return_address:      BitVec = BitVecVal(0, 64)   # [R13+0xF0]
        self.callengine_builtin_arg0:        BitVec = BitVecVal(0, 64)   # [R13+0x108]

        # PC（程序计数器）
        self.pc: int = 0

        # 测试桩 unsafe fallback：仅供 instruction-level 单测使用。
        # 当 base_reg ∉ {R13, R14, R15} 时（如 [rax]、[rbx]），生产代码会抛
        # MemoryDomainError；测试桩可以把这一行设为 MemoryDomain.STACK，把这些
        # 访存兜底到 stack 域，避免在低层指令机制单测里到处改 hex。
        # 生产路径（create_initial_state、to_z3）不会修改这个字段。
        self.unrouted_memory_domain: Optional[MemoryDomain] = None

        # 全局前置假设（precondition assumptions）。
        # 这是一个 Z3 BoolRef 列表，由 caller 在创建初始 state 时塞入（例如
        # "calldatasize ≤ 2^32-1" 这类无损先验），也可以由语义建模函数在执行
        # 过程中追加（例如 CALLDATALOAD 处的 "offset hi-192 == 0"）。
        # 后续 x86/EVM cfg_executor 在每条路径上把它们注入 world_state.constraints，
        # refinement_checker 在 final solve 前也会把它们 add 到 solver。
        # 默认 None；不影响既有路径。
        self.assumptions: Optional[list] = None

        # 默认开启 CALLDATALOAD/CALLDATACOPY 的 offset 高 192-bit == 0 假设。
        # 这条假设在 EVM/x86 两侧都对应 vacuous 同行为分支（两侧 overflow 都返
        # 回 0），所以对 refinement 无损；但能让 z3 跳过 256-bit carry chain，
        # 大幅压缩 bit-blast 后的搜索空间。需要建模 overflow 行为差异的单测可
        # 以显式把这个字段置 False。
        self.assume_calldata_offset_no_overflow: bool = True
        self.abstract_calldataload_words: bool = False

        # 原始 stack_base 符号值和输入数量（create_initial_state 中赋值，供栈一致性检查使用）
        self.stack_base = None
        self.stack_num_inputs = 0

        # 环境信息
        self.calldata = Array('CallData', BitVecSort(64), BitVecSort(8))
        self.code = Array('CodeData', BitVecSort(64), BitVecSort(8))
        self.return_data = Array('ReturnData', BitVecSort(64), BitVecSort(8))
        # Go evmLedgerContext.inputSliceLen / len(scope.Contract.Input).
        # CALLDATASIZE opcode semantics zero-extend this 64-bit context value
        # before pushing it onto the 256-bit EVM stack.
        self.calldatasize = BitVec('CallDataSize', 64)
        self.callvalue = BitVec('CallValue', 256)
        self.basefee = BitVec('BaseFee', 256)
        self.self_address = BitVec('SelfAddress', 256)
        self.origin_address = BitVec('OriginAddress', 256)
        self.caller_address = BitVec('CallerAddress', 256)
        self.block_timestamp = BitVec('BlockTimestamp', 64)
        self.block_number = BitVec('BlockNumber', 64)
        self.gaslimit = BitVec('GasLimit', 64)
        self.blobbasefee = BitVec('BlobBaseFee', 64)

    def add_assumption(self, assumption) -> None:
        """追加一个全局假设到 self.assumptions（若需要会自动初始化为空 list）。

        语义建模函数（如 CALLDATALOAD）用它注入 "offset 高 192-bit == 0"
        这类 vacuous-同行为分支假设；cfg_executor 在每条路径出发时会把
        最新的列表一并加进 path constraints。
        """
        if self.assumptions is None:
            self.assumptions = []
        self.assumptions.append(assumption)

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
        new_state.evm_transient_storage = self.evm_transient_storage.copy()
        new_state.evm_gas = self.evm_gas.copy()
        new_state.x86_memory = self.x86_memory.copy()
        new_state.x86_registers = self.x86_registers.copy()
        new_state.return_offset = getattr(self, 'return_offset', BitVecVal(0, 64))
        new_state.return_length = getattr(self, 'return_length', BitVecVal(0, 64))
        new_state.error_string = getattr(self, 'error_string', None)
        new_state.read_only = getattr(self, 'read_only', False)
        new_state.valid_jump_targets = getattr(self, 'valid_jump_targets', None)
        new_state.error_code = getattr(self, 'error_code', BitVecVal(0, 8))
        self.copy_callengine_side_channels_to(new_state)
        new_state.pc = self.pc

        self.copy_environment_to(new_state)
        new_state.stack_base = getattr(self, 'stack_base', None)
        new_state.stack_num_inputs = getattr(self, 'stack_num_inputs', 0)
        new_state.unrouted_memory_domain = getattr(self, 'unrouted_memory_domain', None)
        # 深拷贝 assumptions list，避免 sibling state 之间 mutate 互相污染。
        # 后续 add_assumption() 只影响当前路径，不会回流到父/兄弟路径。
        src_assumptions = getattr(self, 'assumptions', None)
        new_state.assumptions = list(src_assumptions) if src_assumptions else None
        self.copy_verification_options_to(new_state)

        return new_state

    def copy_verification_options_to(self, other: 'SMTState') -> None:
        """复制 verifier 局部建模开关到另一个 state。"""
        other.assume_calldata_offset_no_overflow = getattr(
            self, 'assume_calldata_offset_no_overflow', True,
        )
        other.abstract_calldataload_words = getattr(
            self, 'abstract_calldataload_words', False,
        )

    def copy_callengine_side_channels_to(self, other: 'SMTState') -> None:
        """复制 callEngine side-channel 字段到另一个 SMTState。"""
        for field in self.CALLENGINE_SIDE_CHANNEL_FIELDS:
            setattr(other, field, getattr(self, field))

    def copy_environment_to(self, other: 'SMTState') -> None:
        """复制共享环境字段到另一个 SMTState。"""
        for field in self.ENVIRONMENT_FIELDS:
            setattr(other, field, getattr(self, field))
        for field in self.OPTIONAL_ENVIRONMENT_FIELDS:
            if hasattr(self, field):
                setattr(other, field, getattr(self, field))

    @classmethod
    def merge_callengine_side_channels(cls, merged_state: 'SMTState',
                                       states: list['SMTState'],
                                       conditions,
                                       default_from_end: bool = False) -> None:
        """将多条路径上的 callEngine side-channel 字段合并到 merged_state。

        Args:
            merged_state: 接收合并结果的 SMTState
            states: 待合并的 SMTState 列表
            conditions: 与 states 对齐的路径条件（BoolRef）列表
            default_from_end: 是否以最后一个状态作为嵌套 If 的默认分支
        """
        if not states:
            return
        if len(states) != len(conditions):
            raise ValueError(
                f"states and conditions must have the same length, "
                f"got {len(states)} and {len(conditions)}"
            )

        from z3 import If

        default_index = len(states) - 1 if default_from_end else 0
        default_state = states[default_index]
        merged_values = {
            field: getattr(default_state, field)
            for field in cls.CALLENGINE_SIDE_CHANNEL_FIELDS
        }

        if default_from_end:
            iter_pairs = reversed(list(zip(states[:-1], conditions[:-1], strict=False)))
        else:
            iter_pairs = reversed(list(zip(states, conditions, strict=False)))

        for state, cond in iter_pairs:
            for field in cls.CALLENGINE_SIDE_CHANNEL_FIELDS:
                merged_values[field] = If(cond, getattr(state, field), merged_values[field])

        for field, value in merged_values.items():
            setattr(merged_state, field, value)

    @staticmethod
    def create_initial_state(
        num_inputs: int = 0,
        calldata_size_bytes: Optional[int] = None,
        calldata_size_max_bytes: Optional[int] = None,
    ) -> 'SMTState':
        """创建具有符号输入的初始SMT状态。

        创建一个新状态，包含：
        - EVM栈上的指定数量的符号256位值
        - 映射到x86内存布局的EVM栈
        - EVM calldatasize context 与 x86 callEngine 64-bit input_size 的一致映射

        Args:
            num_inputs: 要创建的符号输入数量（默认0）
            calldata_size_bytes: 固定 calldata 字节长度；None 表示使用 64-bit 符号长度。
            calldata_size_max_bytes: 符号 calldata 长度的无符号上界；None 表示不添加上界。

        Returns:
            具有符号输入的已初始化SMTState

        Raises:
            ValueError: 如果num_inputs为负数或过大（>1024），或 calldata 长度参数超出 uint64
        """
        # Lazy imports to avoid circular dependencies
        from common.uint256 import Uint256
        from verification.memory_mapping import StackMemoryMapper
        from z3 import IntVal, BitVecVal, ULE, ZeroExt
        from x86_64.models import Register
        from x86_64.aot_profile import GO_HPC_EVM_PROFILE

        callengine_offsets = GO_HPC_EVM_PROFILE.offsets

        # 验证输入数量
        if num_inputs < 0:
            raise ValueError(f"num_inputs must be non-negative, got {num_inputs}")
        if num_inputs > 1024:
            raise ValueError(f"num_inputs must be <= 1024 (EVM stack limit), got {num_inputs}")
        if calldata_size_bytes is not None:
            if calldata_size_bytes < 0:
                raise ValueError(
                    f"calldata_size_bytes must be non-negative, got {calldata_size_bytes}"
                )
            if calldata_size_bytes > (1 << 64) - 1:
                raise ValueError(
                    f"calldata_size_bytes must fit in uint64, got {calldata_size_bytes}"
                )
        if calldata_size_max_bytes is not None:
            if calldata_size_max_bytes < 0:
                raise ValueError(
                    f"calldata_size_max_bytes must be non-negative, got {calldata_size_max_bytes}"
                )
            if calldata_size_max_bytes > (1 << 64) - 1:
                raise ValueError(
                    f"calldata_size_max_bytes must fit in uint64, got {calldata_size_max_bytes}"
                )
            if (
                calldata_size_bytes is not None
                and calldata_size_bytes > calldata_size_max_bytes
            ):
                raise ValueError(
                    "calldata_size_bytes must be <= calldata_size_max_bytes, "
                    f"got {calldata_size_bytes} > {calldata_size_max_bytes}"
                )

        # 创建基础状态
        initial_state = SMTState()

        # R13 是 callEngine 的符号基址，运行时由 Go 决定，验证时视为任意值。
        # R14（栈基址）和 R15（内存基址）从 callEngine 字段中读取：
        #   [R13+16]  = memoryElement0Address  -> R15
        #   [R13+56]  = stackElement0Address   -> R14
        r13 = BitVec('R13', 64)
        initial_state.x86_registers.set_register(Register.R13, r13)

        # 为 callEngine 中会被读取的字段创建符号值
        r14 = BitVec('R14_stack_base', 64)   # stackElement0Address
        r15 = BitVec('R15_mem_base', 64)     # memoryElement0Address
        calldata_ptr = BitVec('CallDataPtr', 64)
        code_ptr = BitVec('CodePtr', 64)
        return_data_ptr = BitVec('ReturnDataPtr', 64)
        self_address_ptr = BitVec('SelfAddressPtr', 64)
        origin_address_ptr = BitVec('OriginAddressPtr', 64)
        caller_address_ptr = BitVec('CallerAddressPtr', 64)
        code_size = BitVec('CodeSizeBytes', 64)
        callvalue64 = BitVec('CallValue64', 64)

        initial_state.callvalue = ZeroExt(192, callvalue64)
        initial_state.self_address = ZeroExt(96, BitVec('SelfAddress160', 160))
        initial_state.origin_address = ZeroExt(96, BitVec('OriginAddress160', 160))
        initial_state.caller_address = ZeroExt(96, BitVec('CallerAddress160', 160))

        # 写入 callEngine 字段（相对于 R13 的偏移）：
        # [R13+0x10] = memoryElement0Address -> R15
        # [R13+0x18] = current memory size（bytes，初始为 0）
        # [R13+0x20] = accumulated memory gas cost（初始为 0）
        # [R13+0x28] = stackPointer（limb 数 delta，初始为 0）
        # [R13+0x30] = stackPointer 字节偏移（add r14, [r13+0x30]，初始为 0）
        # [R13+0x38] = stackElement0Address -> R14 基址
        # [R13+0x68] = callvalue low 64 bits（AOT 当前写入 uint256 低 limb，高 limb 清零）
        # [R13+0x70] = gas，固定为足够大的具体值，确保 gas 检查走 success path
        # [R13+0x78/0x80/0x88] = self/origin/caller 20-byte address buffers
        initial_state.callengine_memory_base = r15
        initial_state.callengine_memory_size_bytes = BitVecVal(0, 64)
        initial_state.callengine_memory_gas_used = BitVecVal(0, 64)
        initial_state.callengine_stack_pointer_limbs = BitVecVal(0, 64)
        initial_state.callengine_stack_byte_offset = BitVecVal(0, 64)
        initial_state.callengine_stack_base = r14
        initial_state.callengine_callvalue = callvalue64
        initial_state.callengine_gas_remaining = BitVecVal(1000000000, 64)
        initial_state.callengine_self_address_pointer = self_address_ptr
        initial_state.callengine_origin_address_pointer = origin_address_ptr
        initial_state.callengine_caller_address_pointer = caller_address_ptr
        initial_state.callengine_input_pointer = calldata_ptr
        initial_state.callengine_code_pointer = code_ptr
        initial_state.callengine_code_size_bytes = code_size
        initial_state.callengine_return_data_pointer = return_data_ptr
        initial_state.callengine_return_data_size_bytes = BitVecVal(0, 64)
        initial_state.x86_memory = initial_state.x86_memory.store_limb(
            r13 + BitVecVal(callengine_offsets["memory_base"], 64),
            r15,
            domain=MemoryDomain.CALLENGINE,
        )
        initial_state.x86_memory = initial_state.x86_memory.store_limb(
            r13 + BitVecVal(callengine_offsets["memory_size"], 64),
            BitVecVal(0, 64),
            domain=MemoryDomain.CALLENGINE,
        )
        initial_state.x86_memory = initial_state.x86_memory.store_limb(
            r13 + BitVecVal(callengine_offsets["last_gas_cost"], 64),
            BitVecVal(0, 64),
            domain=MemoryDomain.CALLENGINE,
        )
        initial_state.x86_memory = initial_state.x86_memory.store_limb(
            r13 + BitVecVal(callengine_offsets["stack_pointer"], 64),
            BitVecVal(0, 64),
            domain=MemoryDomain.CALLENGINE,
        )
        initial_state.x86_memory = initial_state.x86_memory.store_limb(
            r13 + BitVecVal(callengine_offsets["stack_byte_offset"], 64),
            BitVecVal(0, 64),
            domain=MemoryDomain.CALLENGINE,
        )
        initial_state.x86_memory = initial_state.x86_memory.store_limb(
            r13 + BitVecVal(callengine_offsets["stack_base"], 64),
            r14,
            domain=MemoryDomain.CALLENGINE,
        )
        initial_state.x86_memory = initial_state.x86_memory.store_limb(
            r13 + BitVecVal(callengine_offsets["callvalue"], 64),
            callvalue64,
            domain=MemoryDomain.CALLENGINE,
        )
        initial_state.x86_memory = initial_state.x86_memory.store_limb(
            r13 + BitVecVal(callengine_offsets["gas_remaining"], 64),
            BitVecVal(1000000000, 64),
            domain=MemoryDomain.CALLENGINE,
        )
        initial_state.x86_memory = initial_state.x86_memory.store_limb(
            r13 + BitVecVal(callengine_offsets["self_address_pointer"], 64),
            self_address_ptr,
            domain=MemoryDomain.CALLENGINE,
        )
        initial_state.x86_memory = initial_state.x86_memory.store_limb(
            r13 + BitVecVal(callengine_offsets["origin_address_pointer"], 64),
            origin_address_ptr,
            domain=MemoryDomain.CALLENGINE,
        )
        initial_state.x86_memory = initial_state.x86_memory.store_limb(
            r13 + BitVecVal(callengine_offsets["caller_address_pointer"], 64),
            caller_address_ptr,
            domain=MemoryDomain.CALLENGINE,
        )
        initial_state.x86_memory = initial_state.x86_memory.store_limb(
            r13 + BitVecVal(callengine_offsets["input_pointer"], 64),
            calldata_ptr,
            domain=MemoryDomain.CALLENGINE,
        )
        initial_state.x86_memory = initial_state.x86_memory.store_limb(
            r13 + BitVecVal(callengine_offsets["code_pointer"], 64),
            code_ptr,
            domain=MemoryDomain.CALLENGINE,
        )
        initial_state.x86_memory = initial_state.x86_memory.store_limb(
            r13 + BitVecVal(callengine_offsets["code_size"], 64),
            code_size,
            domain=MemoryDomain.CALLENGINE,
        )
        initial_state.x86_memory = initial_state.x86_memory.store_limb(
            r13 + BitVecVal(callengine_offsets["return_data_pointer"], 64),
            return_data_ptr,
            domain=MemoryDomain.CALLENGINE,
        )
        initial_state.x86_memory = initial_state.x86_memory.store_limb(
            r13 + BitVecVal(callengine_offsets["return_data_size"], 64),
            BitVecVal(0, 64),
            domain=MemoryDomain.CALLENGINE,
        )

        # 保存原始 stack_base 和输入数量，供栈一致性检查使用
        initial_state.stack_base = r14
        initial_state.stack_num_inputs = num_inputs

        # 使用SP = 0初始化EVM栈
        initial_state.evm_stack = EVMStackState(sp=IntVal(0))

        if calldata_size_bytes is None:
            calldata_size_64 = initial_state.calldatasize
            if calldata_size_max_bytes is not None:
                initial_state.add_assumption(
                    ULE(calldata_size_64, BitVecVal(calldata_size_max_bytes, 64))
                )
        else:
            calldata_size_64 = BitVecVal(calldata_size_bytes, 64)
            initial_state.calldatasize = calldata_size_64
        initial_state.callengine_input_size_bytes = calldata_size_64
        initial_state.x86_memory = initial_state.x86_memory.store_limb(
            r13 + BitVecVal(callengine_offsets["input_size"], 64),
            calldata_size_64,
            domain=MemoryDomain.CALLENGINE,
        )

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

        # 将 EVM 栈输入按“固定槽位窗口”映射到 x86 内存：
        # slot 0 是栈底，slot N-1 是栈顶，预置区间为 [r14 - N*0x20, ..., r14 - 0x20]。
        # input_stack 仍按“压栈顺序”给出，因此第一个输入会落到最底部槽位。
        # 传入 r14 使地址计算为 r14 + rel_offset，与 GoFunctionSemantics 一致。
        initial_state.x86_memory = StackMemoryMapper.initialize_x86_memory_from_stack(
            initial_state.x86_memory, input_stack, base=r14
        )

        return initial_state
