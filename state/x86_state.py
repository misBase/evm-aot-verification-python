"""
x86-64 内存和寄存器状态建模。
"""

from typing import Dict, Optional, TYPE_CHECKING
from z3 import BitVec, BitVecVal, Array, BitVecSort, K, Select, Store

if TYPE_CHECKING:
    from x86_64.models import Register


class X86MemoryState:
    """x86-64内存状态表示。

    使用Z3 Array对x86-64内存建模：Memory : Array[BitVec[64], BitVec[8]]
    支持符号索引（例如，[r14+rax]，其中偏移量是符号的）
    使用字节级寻址进行精确的内存建模。
    """

    def __init__(self, memory_array: Optional[Array] = None):
        """初始化x86-64内存状态。

        Args:
            memory_array: 可选的现有Memory数组
        """
        # Memory : Array[BitVec[64], BitVec[8]] - 偏移量是64位，值是8位（字节）
        # x86 内存在未写入前默认为 0。
        if memory_array is None:
            self.Memory = K(BitVecSort(64), BitVecVal(0, 8))
        else:
            self.Memory = memory_array

    def load_byte(self, offset: BitVec) -> BitVec:
        """从内存加载单个字节。

        支持符号偏移量（例如，base_offset + reg_value）

        Args:
            offset: 64位BitVec内存偏移量（可以是符号的）

        Returns:
            8位BitVec值
        """
        if isinstance(offset, int):
            # 将int转换为BitVec以向后兼容
            offset = BitVecVal(offset, 64)
        elif offset.size() != 64:
            raise ValueError(f"Memory offset must be 64 bits, got {offset.size()}")

        return Select(self.Memory, offset)

    def store_byte(self, offset: BitVec, value: BitVec) -> 'X86MemoryState':
        """将单个字节存储到内存。

        支持符号偏移量（例如，base_offset + reg_value）

        Args:
            offset: 64位BitVec内存偏移量（可以是符号的）
            value: 8位BitVec值

        Returns:
            具有更新Memory的新X86MemoryState
        """
        if isinstance(offset, int):
            # 将int转换为BitVec以向后兼容
            offset = BitVecVal(offset, 64)
        elif offset.size() != 64:
            raise ValueError(f"Memory offset must be 64 bits, got {offset.size()}")

        if value.size() != 8:
            raise ValueError(f"Memory byte must be 8 bits, got {value.size()}")

        new_memory = Store(self.Memory, offset, value)
        new_state = X86MemoryState(memory_array=new_memory)
        return new_state

    def load_64bit(self, offset: BitVec) -> BitVec:
        """从内存加载64位值（小端序）。

        Args:
            offset: 64位BitVec内存偏移量

        Returns:
            64位BitVec值
        """
        from z3 import Concat

        if isinstance(offset, int):
            offset = BitVecVal(offset, 64)
        elif offset.size() != 64:
            raise ValueError(f"Memory offset must be 64 bits, got {offset.size()}")

        # 按小端序加载8字节：[byte0|byte1|...|byte7]
        # 其中byte0在offset（LSB），byte7在offset+7（MSB）
        bytes_list = []
        for i in range(8):
            byte_offset = offset + BitVecVal(i, 64)
            byte_val = Select(self.Memory, byte_offset)
            bytes_list.append(byte_val)

        # 按小端序连接：[byte7|byte6|...|byte0]
        return Concat(*reversed(bytes_list))

    def store_64bit(self, offset: BitVec, value: BitVec) -> 'X86MemoryState':
        """将64位值存储到内存（小端序）。

        Args:
            offset: 64位BitVec内存偏移量
            value: 64位BitVec值

        Returns:
            具有更新Memory的新X86MemoryState
        """
        from z3 import Extract

        if isinstance(offset, int):
            offset = BitVecVal(offset, 64)
        elif offset.size() != 64:
            raise ValueError(f"Memory offset must be 64 bits, got {offset.size()}")

        if value.size() != 64:
            raise ValueError(f"Value must be 64 bits, got {value.size()}")

        # 按小端序存储8字节
        new_memory = self.Memory
        for i in range(8):
            # 提取字节i：位[8*i+7 : 8*i]（byte0是LSB）
            byte_val = Extract(8*i+7, 8*i, value)
            byte_offset = offset + BitVecVal(i, 64)
            new_memory = Store(new_memory, byte_offset, byte_val)

        new_state = X86MemoryState(memory_array=new_memory)
        return new_state

    def load_limb(self, offset: BitVec) -> BitVec:
        """从内存加载64位limb（向后兼容）。

        这是load_64bit()的别名，以保持向后兼容性。

        Args:
            offset: 64位BitVec内存偏移量（可以是符号的）

        Returns:
            64位BitVec值
        """
        return self.load_64bit(offset)

    def store_limb(self, offset: BitVec, value: BitVec) -> 'X86MemoryState':
        """将64位limb存储到内存（向后兼容）。

        这是store_64bit()的别名，以保持向后兼容性。

        Args:
            offset: 64位BitVec内存偏移量（可以是符号的）
            value: 64位BitVec值

        Returns:
            具有更新Memory的新X86MemoryState
        """
        return self.store_64bit(offset, value)

    def load_256bit(self, base_offset: BitVec) -> BitVec:
        """从内存加载256位值（4×64位limb，小端序）。

        Args:
            base_offset: 256位值的64位BitVec基址偏移量（LSB偏移量）

        Returns:
            256位BitVec
        """
        from z3 import Concat

        if isinstance(base_offset, int):
            base_offset = BitVecVal(base_offset, 64)

        # 加载4个limb：z0（LSB）在base_offset，z1在base_offset+8，等等
        z0 = self.load_64bit(base_offset)
        z1 = self.load_64bit(base_offset + BitVecVal(8, 64))
        z2 = self.load_64bit(base_offset + BitVecVal(16, 64))
        z3 = self.load_64bit(base_offset + BitVecVal(24, 64))

        # 连接：[z3|z2|z1|z0]用于256位值
        return Concat(z3, z2, z1, z0)

    def store_256bit(self, base_offset: BitVec, value: BitVec) -> 'X86MemoryState':
        """将256位值存储到内存（4×64位limb，小端序）。

        Args:
            base_offset: 256位值的64位BitVec基址偏移量（LSB偏移量）
            value: 256位BitVec

        Returns:
            具有更新Memory的新X86MemoryState
        """
        from z3 import Extract

        if isinstance(base_offset, int):
            base_offset = BitVecVal(base_offset, 64)

        if value.size() != 256:
            raise ValueError(f"Value must be 256 bits, got {value.size()}")

        # 提取4个limb：z0（LSB）、z1、z2、z3（MSB）
        z0 = Extract(63, 0, value)
        z1 = Extract(127, 64, value)
        z2 = Extract(191, 128, value)
        z3 = Extract(255, 192, value)

        # 存储limb（每次存储返回新状态）
        new_state = self.store_64bit(base_offset, z0)
        new_state = new_state.store_64bit(base_offset + BitVecVal(8, 64), z1)
        new_state = new_state.store_64bit(base_offset + BitVecVal(16, 64), z2)
        new_state = new_state.store_64bit(base_offset + BitVecVal(24, 64), z3)

        return new_state

    def copy(self) -> 'X86MemoryState':
        """创建内存状态的副本。

        Returns:
            具有相同Memory的新X86MemoryState实例
        """
        new_state = X86MemoryState(memory_array=self.Memory)
        return new_state


class X86RegisterState:
    """x86-64寄存器状态表示。

    将x86-64寄存器建模为64位符号变量。
    """

    def __init__(self):
        """初始化x86-64寄存器状态。"""
        # 寄存器：reg[Register]是64位BitVec
        # 使用字符串键以避免循环导入
        self._registers: Dict[str, BitVec] = {}
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
        new_state._flags = self._flags.copy()
        return new_state
