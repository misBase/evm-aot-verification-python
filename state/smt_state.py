"""
用于Z3公式建模的SMT状态管理。

本模块为EVM IR和x86-64程序提供统一的状态管理，
将栈、内存和寄存器建模为符号变量。
"""

from typing import Dict, Optional, List, TYPE_CHECKING
from z3 import BitVec, BitVecVal, Array, ArraySort, BitVecSort, IntSort, Int, Select, Store, BoolRef

if TYPE_CHECKING:
    from x86_64.models import Register


class EVMStackState:
    """EVM栈状态表示。

    使用Z3 Array对EVM栈建模：Stack : Array[Int, BitVec[256]]
    栈指针SP : Int（范围0-1024）
    栈顶元素：Stack[SP-1]
    """

    def __init__(self, initial_depth: int = 0, stack_array: Optional[Array] = None, sp: Optional[Int] = None):
        """初始化EVM栈状态。

        Args:
            initial_depth: 初始栈深度（用于向后兼容）
            stack_array: 可选的现有Stack数组
            sp: 可选的现有SP指针
        """
        # Stack : Array[Int, BitVec[256]]
        if stack_array is None:
            self.Stack = Array('Stack', IntSort(), BitVecSort(256))
        else:
            self.Stack = stack_array

        # SP : Int（栈指针，范围0-1024）
        if sp is None:
            self.SP = Int('SP')
        else:
            self.SP = sp

        # 为了向后兼容，跟踪深度
        self.depth = initial_depth

    def dup(self, n: int) -> 'EVMStackState':
        """DUP操作：复制栈上的第n个元素到栈顶。

        DUP1复制栈顶元素，DUP2复制次栈顶元素，以此类推。

        Args:
            n: DUP编号（1-16），DUP1复制Stack[SP-1]，DUP2复制Stack[SP-2]

        Returns:
            具有更新Stack和SP的新EVMStackState
        """
        if not 1 <= n <= 16:
            raise ValueError(f"DUP number must be 1-16, got {n}")

        # 获取要复制的值：Stack[SP-n]
        value = Select(self.Stack, self.SP - n)

        # 推送到栈顶：SP' = SP + 1, Stack' = Store(Stack, SP, value)
        new_sp = self.SP + 1
        new_stack = Store(self.Stack, self.SP, value)

        new_state = EVMStackState(initial_depth=self.depth + 1, stack_array=new_stack, sp=new_sp)
        return new_state

    def swap(self, n: int) -> 'EVMStackState':
        """SWAP操作：交换栈顶元素和第n个元素。

        SWAP1交换Stack[SP-1]和Stack[SP-2]，SWAP2交换Stack[SP-1]和Stack[SP-3]，以此类推。

        Args:
            n: SWAP编号（1-16），SWAP1交换栈顶和次栈顶

        Returns:
            具有更新Stack的新EVMStackState（SP不变）
        """
        if not 1 <= n <= 16:
            raise ValueError(f"SWAP number must be 1-16, got {n}")

        # 获取栈顶元素：Stack[SP-1]
        top_value = Select(self.Stack, self.SP - 1)

        # 获取要交换的元素：Stack[SP-1-n]
        other_value = Select(self.Stack, self.SP - 1 - n)

        # 存储到交换位置：Stack[SP-1-n] = top_value
        new_stack = Store(self.Stack, self.SP - 1 - n, top_value)

        # 存储栈顶：Stack[SP-1] = other_value
        new_stack = Store(new_stack, self.SP - 1, other_value)

        new_state = EVMStackState(initial_depth=self.depth, stack_array=new_stack, sp=self.SP)
        return new_state
    
    def push(self, value: BitVec) -> 'EVMStackState':
        """将值推送到栈上。
        
        PUSH操作：SP' = SP + 1, Stack' = Store(Stack, SP, value)
        
        Args:
            value: 要推送的256位BitVec值
            
        Returns:
            具有更新Stack和SP的新EVMStackState
        """
        if value.size() != 256:
            raise ValueError(f"Stack value must be 256 bits, got {value.size()}")
        
        # SP' = SP + 1
        new_sp = self.SP + 1
        # Stack' = Store(Stack, SP, value)
        new_stack = Store(self.Stack, self.SP, value)
        
        # 创建新状态
        new_state = EVMStackState(initial_depth=self.depth + 1, stack_array=new_stack, sp=new_sp)
        return new_state
    
    def pop(self) -> tuple[BitVec, 'EVMStackState']:
        """从栈中弹出一个值。
        
        POP操作：value = Select(Stack, SP-1), SP' = SP - 1
        
        Returns:
            (popped_value, new_state)元组
        """
        # value = Select(Stack, SP-1)
        value = Select(self.Stack, self.SP - 1)
        # SP' = SP - 1
        new_sp = self.SP - 1
        # Stack保持不变（我们不修改它，只更改SP）
        
        new_state = EVMStackState(initial_depth=max(0, self.depth - 1), stack_array=self.Stack, sp=new_sp)
        return value, new_state
    
    def peek(self, index: int = 0) -> BitVec:
        """查看栈值而不弹出。
        
        Args:
            index: 栈索引（0 = 栈顶，1 = 次栈顶，等等）
            
        Returns:
            索引处的256位BitVec值
        """
        # 栈索引0在SP-1，索引1在SP-2，等等
        stack_index = self.SP - 1 - index
        return Select(self.Stack, stack_index)
    
    @property
    def top(self) -> BitVec:
        """获取栈的顶部元素（Stack[SP-1]）。
        
        Returns:
            栈顶的256位BitVec值
        """
        return Select(self.Stack, self.SP - 1)
    
    def back(self, n: int) -> BitVec:
        """获取栈中back(n)位置的值。
        
        back(0)是栈顶（Stack[SP-1]）
        back(1)是次栈顶（Stack[SP-2]）
        等等
        
        Args:
            n: 栈索引（0 = 栈顶，1 = 次栈顶，等等）
            
        Returns:
            back(n)位置的256位BitVec值
        """
        # back(n) = Stack[SP-1-n]
        stack_index = self.SP - 1 - n
        return Select(self.Stack, stack_index)
    
    def copy(self) -> 'EVMStackState':
        """创建栈状态的副本。
        
        Returns:
            具有相同Stack和SP的新EVMStackState实例
        """
        # 注意：在Z3中，数组和整数是不可变表达式，
        # 所以我们可以直接重用它们
        new_state = EVMStackState(initial_depth=self.depth, stack_array=self.Stack, sp=self.SP)
        return new_state


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
        if memory_array is None:
            self.Memory = Array('X86Memory', BitVecSort(64), BitVecSort(8))
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

    def copy(self) -> 'SMTState':
        """创建状态的副本。

        Returns:
            新SMTState实例
        """
        new_state = SMTState()
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
        from z3 import IntVal

        # 验证输入数量
        if num_inputs < 0:
            raise ValueError(f"num_inputs must be non-negative, got {num_inputs}")
        if num_inputs > 1024:
            raise ValueError(f"num_inputs must be <= 1024 (EVM stack limit), got {num_inputs}")

        # 创建基础状态
        initial_state = SMTState()

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


class EVMStorageState:
    """EVM存储状态表示。

    使用Z3 Array对EVM存储建模：Storage : Array[BitVec[256], BitVec[256]]
    键值对存储，256位地址到256位值。
    """

    def __init__(self, storage_array: Optional[Array] = None):
        """初始化EVM存储状态。

        Args:
            storage_array: 可选的现有Storage数组
        """
        # Storage : Array[BitVec[256], BitVec[256]]
        if storage_array is None:
            self.Storage = Array('Storage', BitVecSort(256), BitVecSort(256))
        else:
            self.Storage = storage_array

    def sload(self, key: BitVec) -> BitVec:
        """从存储中加载值。

        Args:
            key: 256位存储键

        Returns:
            256位存储值
        """
        if key.size() != 256:
            raise ValueError(f"Storage key must be 256 bits, got {key.size()}")

        return Select(self.Storage, key)

    def sstore(self, key: BitVec, value: BitVec) -> 'EVMStorageState':
        """存储值到存储中。

        Args:
            key: 256位存储键
            value: 256位要存储的值

        Returns:
            具有更新Storage的新EVMStorageState
        """
        if key.size() != 256:
            raise ValueError(f"Storage key must be 256 bits, got {key.size()}")
        if value.size() != 256:
            raise ValueError(f"Storage value must be 256 bits, got {value.size()}")

        new_storage = Store(self.Storage, key, value)
        new_state = EVMStorageState(storage_array=new_storage)
        return new_state

    def copy(self) -> 'EVMStorageState':
        """创建存储状态的副本。

        Returns:
            具有相同Storage的新EVMStorageState实例
        """
        new_state = EVMStorageState(storage_array=self.Storage)
        return new_state


class EVMGasState:
    """EVM Gas状态表示。

    跟踪Gas消耗：Gas : BitVec[64]
    支持静态Gas和动态Gas计算。
    """

    def __init__(self, initial_gas: Optional[BitVec] = None):
        """初始化EVM Gas状态。

        Args:
            initial_gas: 可选的初始Gas值
        """
        # Gas : BitVec[64]
        if initial_gas is None:
            self.Gas = BitVec('Gas', 64)
        else:
            self.Gas = initial_gas

    def consume_static(self, amount: int) -> 'EVMGasState':
        """消耗静态Gas。

        Args:
            amount: 要消耗的Gas数量

        Returns:
            具有更新Gas的新EVMGasState
        """
        from z3 import BitVecVal, If, UGT
        amount_bv = BitVecVal(amount, 64)

        # 检查Gas溢出：如果Gas < amount，设为0（out of gas）
        new_gas = If(UGT(amount_bv, self.Gas),
                     BitVecVal(0, 64),
                     self.Gas - amount_bv)

        new_state = EVMGasState(initial_gas=new_gas)
        return new_state

    def consume_dynamic(self, cost: BitVec) -> 'EVMGasState':
        """消耗动态Gas。

        Args:
            cost: 动态Gas成本（符号表达式）

        Returns:
            具有更新Gas的新EVMGasState
        """
        from z3 import If, UGT

        # 检查Gas溢出：如果Gas < cost，设为0（out of gas）
        new_gas = If(UGT(cost, self.Gas),
                     BitVecVal(0, 64),
                     self.Gas - cost)

        new_state = EVMGasState(initial_gas=new_gas)
        return new_state

    def is_out_of_gas(self) -> BoolRef:
        """检查是否耗尽Gas。

        Returns:
            BoolRef：如果Gas == 0则为True
        """
        from z3 import BitVecVal
        return self.Gas == BitVecVal(0, 64)

    def copy(self) -> 'EVMGasState':
        """创建Gas状态的副本。

        Returns:
            具有相同Gas的新EVMGasState实例
        """
        new_state = EVMGasState(initial_gas=self.Gas)
        return new_state

