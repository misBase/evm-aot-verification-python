"""
EVM 内存状态建模。
"""

from typing import Optional
from z3 import BitVec, BitVecVal, Array, BitVecSort, Select, Store


class EVMMemoryState:
    """EVM内存状态表示。

    使用Z3 Array对EVM内存建模：Memory : Array[BitVec[64], BitVec[8]]
    内存大小：MSize : BitVec[64]（跟踪最大访问地址）

    注意：虽然EVM理论上支持256位地址，但在实践中
    AOT编译的代码使用64位地址，实际的EVM程序从不
    使用地址 >= 2^64。使用64位地址简化了验证
    并提高了Z3求解器性能。
    """

    def __init__(self, memory_array: Optional[Array] = None, msize: Optional[BitVec] = None):
        """初始化EVM内存状态。

        Args:
            memory_array: 可选的现有Memory数组
            msize: 可选的现有MSize变量
        """
        # Memory : Array[BitVec[64], BitVec[8]] - 地址是64位，值是8位（字节）
        if memory_array is None:
            self.Memory = Array('Memory', BitVecSort(64), BitVecSort(8))
        else:
            self.Memory = memory_array

        # MSize : BitVec[64] - 跟踪最大访问地址（内存大小）
        if msize is None:
            self.MSize = BitVec('MSize', 64)
        else:
            self.MSize = msize

    def load_256bit(self, offset: BitVec) -> tuple[BitVec, 'EVMMemoryState']:
        """从内存加载32字节（256位）。

        MLOAD操作：从偏移量开始读取32字节
        内存布局：大端序（偏移量处的字节是MSB）

        Args:
            offset: 64位或256位BitVec内存偏移量（256位将被截断）

        Returns:
            (256位值, 具有更新MSize的新状态)元组
        """
        from z3 import Concat, If, UGE, Extract as Z3Extract

        # 如果偏移量是256位，截断为64位（取低64位）
        if offset.size() == 256:
            offset = Z3Extract(63, 0, offset)
        elif offset.size() != 64:
            raise ValueError(f"Offset must be 64 or 256 bits, got {offset.size()}")

        # 加载32字节：Memory[offset], Memory[offset+1], ..., Memory[offset+31]
        # 按大端序连接：[byte0|byte1|...|byte31]，其中byte0是MSB
        bytes_list = []
        for i in range(32):
            byte_offset = offset + BitVecVal(i, 64)
            byte_val = Select(self.Memory, byte_offset)
            bytes_list.append(byte_val)

        # 连接：[byte0|byte1|...|byte31] = 256位值
        value = Concat(*bytes_list)

        # 更新MSize：MSize' = If(offset + 32 > MSize, offset + 32, MSize)
        new_msize = If(UGE(offset + BitVecVal(32, 64), self.MSize),
                       offset + BitVecVal(32, 64),
                       self.MSize)

        new_state = EVMMemoryState(memory_array=self.Memory, msize=new_msize)
        return value, new_state

    def store_256bit(self, offset: BitVec, value: BitVec) -> 'EVMMemoryState':
        """将32字节（256位）存储到内存。

        MSTORE操作：从偏移量开始写入32字节
        内存布局：大端序（偏移量处的字节是MSB）

        Args:
            offset: 64位或256位BitVec内存偏移量（256位将被截断）
            value: 要存储的256位BitVec值

        Returns:
            具有更新Memory和MSize的新EVMMemoryState
        """
        from z3 import Extract, If, UGE, Extract as Z3Extract

        if value.size() != 256:
            raise ValueError(f"Value must be 256 bits, got {value.size()}")

        # 如果偏移量是256位，截断为64位（取低64位）
        if offset.size() == 256:
            offset = Z3Extract(63, 0, offset)
        elif offset.size() != 64:
            raise ValueError(f"Offset must be 64 or 256 bits, got {offset.size()}")

        # 从值中提取32字节：byte0（MSB）到byte31（LSB）
        # 将它们存储在Memory[offset], Memory[offset+1], ..., Memory[offset+31]
        new_memory = self.Memory
        for i in range(32):
            # 提取字节i：位[255-8*i : 248-8*i]（byte0是MSB）
            byte_val = Extract(255 - 8*i, 248 - 8*i, value)
            byte_offset = offset + BitVecVal(i, 64)
            new_memory = Store(new_memory, byte_offset, byte_val)

        # 更新MSize：MSize' = If(offset + 32 > MSize, offset + 32, MSize)
        new_msize = If(UGE(offset + BitVecVal(32, 64), self.MSize),
                       offset + BitVecVal(32, 64),
                       self.MSize)

        new_state = EVMMemoryState(memory_array=new_memory, msize=new_msize)
        return new_state

    def get_byte(self, offset: BitVec) -> BitVec:
        """从内存获取单个字节。

        Args:
            offset: 64位或256位BitVec内存偏移量（256位将被截断）

        Returns:
            8位BitVec值
        """
        from z3 import Extract as Z3Extract

        # 如果偏移量是256位，截断为64位
        if offset.size() == 256:
            offset = Z3Extract(63, 0, offset)
        elif offset.size() != 64:
            raise ValueError(f"Offset must be 64 or 256 bits, got {offset.size()}")

        return Select(self.Memory, offset)

    def set_byte(self, offset: BitVec, value: BitVec) -> 'EVMMemoryState':
        """在内存中设置单个字节。

        Args:
            offset: 64位或256位BitVec内存偏移量（256位将被截断）
            value: 8位BitVec值

        Returns:
            具有更新Memory和MSize的新EVMMemoryState
        """
        from z3 import If, UGE, Extract as Z3Extract

        if value.size() != 8:
            raise ValueError(f"Memory byte must be 8 bits, got {value.size()}")

        # 如果偏移量是256位，截断为64位
        if offset.size() == 256:
            offset = Z3Extract(63, 0, offset)
        elif offset.size() != 64:
            raise ValueError(f"Offset must be 64 or 256 bits, got {offset.size()}")

        new_memory = Store(self.Memory, offset, value)

        # 更新MSize：MSize' = If(offset + 1 > MSize, offset + 1, MSize)
        new_msize = If(UGE(offset + BitVecVal(1, 64), self.MSize),
                       offset + BitVecVal(1, 64),
                       self.MSize)

        new_state = EVMMemoryState(memory_array=new_memory, msize=new_msize)
        return new_state

    def copy(self) -> 'EVMMemoryState':
        """创建内存状态的副本。

        Returns:
            具有相同Memory和MSize的新EVMMemoryState实例
        """
        new_state = EVMMemoryState(memory_array=self.Memory, msize=self.MSize)
        return new_state
