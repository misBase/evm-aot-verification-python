"""
x86-64 内存和寄存器状态建模。
"""

from enum import Enum
from typing import Dict, Optional, TYPE_CHECKING
from z3 import BitVec, BitVecVal, Array, BitVecSort, K, Select, Store

if TYPE_CHECKING:
    from x86_64.models import Register


class MemoryDomain(str, Enum):
    """x86 内存访问 domain，按 Go AOT 的寄存器约定路由到独立 Z3 Array。

    - CALLENGINE: 通过 R13 访问 callEngine 结构体（sp、status_code、gas、return_address ...）
    - STACK:      通过 R14 访问 EVM 栈窗口（4 limb × 槽位）
    - EVM:        通过 R15 访问 EVM 256-bit memory（MSTORE/MLOAD/SHA3/RETURN data）
    """
    CALLENGINE = "callengine"
    STACK = "stack"
    EVM = "evm"


class PointerTag(str, Enum):
    """通用寄存器中只读源指针的轻量 provenance 标签。"""

    NONE = "none"
    CALLDATA_PTR = "calldata_ptr"
    CODE_PTR = "code_ptr"
    RETURNDATA_PTR = "returndata_ptr"
    EVM_PTR = "evm_ptr"
    STACK_PTR = "stack_ptr"


class MemoryDomainError(ValueError):
    """无法把内存访问静态路由到 {callengine, stack, evm} 任一 domain 时抛出。

    继承 ValueError 以兼容现有 except ValueError 块。
    """

    def __init__(self, message: str, *, base_reg=None, size_bytes: Optional[int] = None,
                 disasm: Optional[str] = None):
        super().__init__(message)
        self.base_reg = base_reg
        self.size_bytes = size_bytes
        self.disasm = disasm


class X86MemoryState:
    """x86-64 内存状态：拆分为三个独立 Z3 Array，按 base_reg 路由。

    每个 Array 都是 Array[BitVec[64], BitVec[8]]，默认全零（K(BV64, 0)）。
    所有 load_*/store_* 必须显式传入 keyword-only 的 `domain` 参数，
    无默认值，无 fallback —— 写错 domain 会立刻在 Select/Store 上跑错 Array。

    构造方式：
        X86MemoryState()                                 # 三个 Array 全零
        X86MemoryState.from_arrays(ce, st, ev)           # 显式指定三个 Array
        state._with_array(domain, new_array)             # 替换某一个 Array，返回新实例
    """

    __slots__ = ("call_engine_mem", "stack_mem", "evm_mem")

    def __init__(self, *,
                 call_engine_mem: Optional[Array] = None,
                 stack_mem: Optional[Array] = None,
                 evm_mem: Optional[Array] = None):
        self.call_engine_mem = call_engine_mem if call_engine_mem is not None else _zero_byte_array()
        self.stack_mem       = stack_mem       if stack_mem       is not None else _zero_byte_array()
        self.evm_mem         = evm_mem         if evm_mem         is not None else _zero_byte_array()

    @classmethod
    def from_arrays(cls, call_engine_mem: Array, stack_mem: Array, evm_mem: Array) -> 'X86MemoryState':
        return cls(call_engine_mem=call_engine_mem, stack_mem=stack_mem, evm_mem=evm_mem)

    # ---- 内部 dispatch helpers ----

    def _array_for_domain(self, domain: MemoryDomain) -> Array:
        if not isinstance(domain, MemoryDomain):
            raise MemoryDomainError(f"unrecognized memory domain: {domain!r}")
        if domain == MemoryDomain.CALLENGINE:
            return self.call_engine_mem
        if domain == MemoryDomain.STACK:
            return self.stack_mem
        if domain == MemoryDomain.EVM:
            return self.evm_mem
        raise MemoryDomainError(f"unrecognized memory domain: {domain!r}")

    def _with_array(self, domain: MemoryDomain, new_array: Array) -> 'X86MemoryState':
        if not isinstance(domain, MemoryDomain):
            raise MemoryDomainError(f"unrecognized memory domain: {domain!r}")
        if domain == MemoryDomain.CALLENGINE:
            return X86MemoryState.from_arrays(new_array, self.stack_mem, self.evm_mem)
        if domain == MemoryDomain.STACK:
            return X86MemoryState.from_arrays(self.call_engine_mem, new_array, self.evm_mem)
        if domain == MemoryDomain.EVM:
            return X86MemoryState.from_arrays(self.call_engine_mem, self.stack_mem, new_array)
        raise MemoryDomainError(f"unrecognized memory domain: {domain!r}")

    # ---- 字节级访问 ----

    def load_byte(self, offset: BitVec, *, domain: MemoryDomain) -> BitVec:
        offset = _coerce_offset(offset)
        return Select(self._array_for_domain(domain), offset)

    def store_byte(self, offset: BitVec, value: BitVec, *, domain: MemoryDomain) -> 'X86MemoryState':
        offset = _coerce_offset(offset)
        if value.size() != 8:
            raise ValueError(f"Memory byte must be 8 bits, got {value.size()}")
        new_arr = Store(self._array_for_domain(domain), offset, value)
        return self._with_array(domain, new_arr)

    # ---- 64-bit 访问（小端序） ----

    def load_64bit(self, offset: BitVec, *, domain: MemoryDomain) -> BitVec:
        from z3 import Concat
        offset = _coerce_offset(offset)
        arr = self._array_for_domain(domain)
        bytes_list = [Select(arr, offset + BitVecVal(i, 64)) for i in range(8)]
        return Concat(*reversed(bytes_list))

    def store_64bit(self, offset: BitVec, value: BitVec, *, domain: MemoryDomain) -> 'X86MemoryState':
        from z3 import Extract
        offset = _coerce_offset(offset)
        if value.size() != 64:
            raise ValueError(f"Value must be 64 bits, got {value.size()}")
        arr = self._array_for_domain(domain)
        for i in range(8):
            byte_val = Extract(8 * i + 7, 8 * i, value)
            arr = Store(arr, offset + BitVecVal(i, 64), byte_val)
        return self._with_array(domain, arr)

    def load_limb(self, offset: BitVec, *, domain: MemoryDomain) -> BitVec:
        return self.load_64bit(offset, domain=domain)

    def store_limb(self, offset: BitVec, value: BitVec, *, domain: MemoryDomain) -> 'X86MemoryState':
        return self.store_64bit(offset, value, domain=domain)

    # ---- 256-bit 访问（4×64-bit limb，小端序） ----

    def load_256bit(self, base_offset: BitVec, *, domain: MemoryDomain) -> BitVec:
        from z3 import Concat
        base_offset = _coerce_offset(base_offset)
        z0 = self.load_64bit(base_offset, domain=domain)
        z1 = self.load_64bit(base_offset + BitVecVal(8, 64), domain=domain)
        z2 = self.load_64bit(base_offset + BitVecVal(16, 64), domain=domain)
        z3 = self.load_64bit(base_offset + BitVecVal(24, 64), domain=domain)
        return Concat(z3, z2, z1, z0)

    def store_256bit(self, base_offset: BitVec, value: BitVec, *, domain: MemoryDomain) -> 'X86MemoryState':
        from z3 import Extract
        base_offset = _coerce_offset(base_offset)
        if value.size() != 256:
            raise ValueError(f"Value must be 256 bits, got {value.size()}")
        z0 = Extract(63, 0, value)
        z1 = Extract(127, 64, value)
        z2 = Extract(191, 128, value)
        z3 = Extract(255, 192, value)
        new_state = self.store_64bit(base_offset, z0, domain=domain)
        new_state = new_state.store_64bit(base_offset + BitVecVal(8, 64), z1, domain=domain)
        new_state = new_state.store_64bit(base_offset + BitVecVal(16, 64), z2, domain=domain)
        new_state = new_state.store_64bit(base_offset + BitVecVal(24, 64), z3, domain=domain)
        return new_state

    def copy(self) -> 'X86MemoryState':
        return X86MemoryState.from_arrays(self.call_engine_mem, self.stack_mem, self.evm_mem)


def _zero_byte_array() -> Array:
    return K(BitVecSort(64), BitVecVal(0, 8))


def _coerce_offset(offset) -> BitVec:
    if isinstance(offset, int):
        return BitVecVal(offset, 64)
    if offset.size() != 64:
        raise ValueError(f"Memory offset must be 64 bits, got {offset.size()}")
    return offset


class X86RegisterState:
    """x86-64寄存器状态表示。

    将x86-64寄存器建模为64位符号变量。
    """

    def __init__(self):
        """初始化x86-64寄存器状态。"""
        # 寄存器：reg[Register]是64位BitVec
        # 使用字符串键以避免循环导入
        self._registers: Dict[str, BitVec] = {}
        self._pointer_tags: Dict[str, PointerTag] = {}
        # 标志：flags[name]是1位BitVec
        self._flags: Dict[str, BitVec] = {}
        # CF（进位标志）从0开始
        self._flags['CF'] = BitVecVal(0, 1)

    def get_register(self, reg) -> BitVec:
        """获取寄存器值。

        Args:
            reg: 要获取的寄存器（Register枚举或字符串）

        Returns:
            64位BitVec
        """
        # 将Register枚举转换为字符串键
        reg_key = reg.value if hasattr(reg, 'value') else str(reg)
        if reg_key not in self._registers:
            self._registers[reg_key] = BitVec(f"{reg_key}_init", 64)
        return self._registers[reg_key]

    def set_register(self, reg, value: BitVec) -> None:
        """设置寄存器值。

        Args:
            reg: 要设置的寄存器（Register枚举或字符串）
            value: 64位BitVec
        """
        if value.size() != 64:
            raise ValueError(f"Register value must be 64 bits, got {value.size()}")
        # 将Register枚举转换为字符串键
        reg_key = reg.value if hasattr(reg, 'value') else str(reg)
        self._registers[reg_key] = value
        self._pointer_tags[reg_key] = PointerTag.NONE

    def get_pointer_tag(self, reg) -> PointerTag:
        """获取寄存器的只读源指针标签。"""
        reg_key = reg.value if hasattr(reg, 'value') else str(reg)
        return self._pointer_tags.get(reg_key, PointerTag.NONE)

    def set_pointer_tag(self, reg, tag: PointerTag) -> None:
        """设置寄存器的只读源指针标签。"""
        reg_key = reg.value if hasattr(reg, 'value') else str(reg)
        self._pointer_tags[reg_key] = tag

    def clear_pointer_tag(self, reg) -> None:
        """清空寄存器的只读源指针标签。"""
        self.set_pointer_tag(reg, PointerTag.NONE)

    def get_flag(self, flag_name: str) -> BitVec:
        """获取标志值。

        Args:
            flag_name: 标志名称（例如，'CF'）

        Returns:
            1位BitVec
        """
        if flag_name not in self._flags:
            self._flags[flag_name] = BitVecVal(0, 1)
        return self._flags[flag_name]

    def set_flag(self, flag_name: str, value: BitVec) -> None:
        """设置标志值。

        Args:
            flag_name: 标志名称
            value: 1位BitVec
        """
        if value.size() != 1:
            raise ValueError(f"Flag value must be 1 bit, got {value.size()}")
        self._flags[flag_name] = value

    def copy(self) -> 'X86RegisterState':
        """创建寄存器状态的副本。

        Returns:
            新X86RegisterState实例
        """
        new_state = X86RegisterState()
        new_state._registers = self._registers.copy()
        new_state._pointer_tags = self._pointer_tags.copy()
        new_state._flags = self._flags.copy()
        return new_state
