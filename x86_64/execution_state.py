"""
x86-64执行状态管理。

本模块提供ExecutionState类，用于在指令序列执行期间维护寄存器、内存和标志状态。
"""

from z3 import BitVec, BitVecVal
from typing import Dict, Optional
from .models import Register


class ExecutionState:
    """维护x86-64指令执行的执行状态。
    
    跟踪：
    - 寄存器：每个寄存器的64位值
    - 内存：内存偏移量处的值（相对于R14基址寄存器）
    - 标志：CPU标志（CF、ZF、SF等）- 1位值
    """
    
    def __init__(self, initial_memory: Optional[Dict[int, BitVec]] = None):
        """初始化执行状态。
        
        Args:
            initial_memory: 初始内存状态（将偏移量映射到BitVec值的字典）
        """
        # 将所有寄存器初始化为符号变量（将在首次使用时设置）
        self.registers: Dict[Register, BitVec] = {}
        
        # 从提供的初始状态初始化内存
        self.memory: Dict[int, BitVec] = {}
        if initial_memory:
            self.memory.update(initial_memory)
        
        # 初始化标志（CF = 进位标志，对ADD/ADC最重要）
        self.flags: Dict[str, BitVec] = {}
        # CF从0开始
        self.flags['CF'] = BitVecVal(0, 1)
    
    def get_register(self, reg: Register) -> BitVec:
        """获取寄存器值，如果不存在则初始化。
        
        Args:
            reg: 要获取的寄存器
            
        Returns:
            当前寄存器值（64位BitVec）
        """
        if reg not in self.registers:
            # 使用符号变量初始化
            self.registers[reg] = BitVec(f"{reg.value}_init", 64)
        return self.registers[reg]
    
    def set_register(self, reg: Register, value: BitVec) -> None:
        """设置寄存器值。
        
        Args:
            reg: 要设置的寄存器
            value: 要设置的值（必须是64位BitVec）
        """
        if value.size() != 64:
            raise ValueError(f"Register value must be 64 bits, got {value.size()}")
        self.registers[reg] = value
    
    def load_memory(self, offset: int) -> BitVec:
        """从给定偏移量（相对于R14）的内存加载值。
        
        Args:
            offset: 内存偏移量（例如，-0x40）
            
        Returns:
            内存位置的值（64位BitVec）
        """
        if offset not in self.memory:
            # 如果不存在则创建符号变量
            self.memory[offset] = BitVec(f"mem_{offset:+d}", 64)
        return self.memory[offset]
    
    def store_memory(self, offset: int, value: BitVec) -> None:
        """将值存储到给定偏移量（相对于R14）的内存。
        
        Args:
            offset: 内存偏移量
            value: 要存储的值（必须是64位BitVec）
        """
        if value.size() != 64:
            raise ValueError(f"Memory value must be 64 bits, got {value.size()}")
        self.memory[offset] = value
    
    def get_flag(self, flag_name: str) -> BitVec:
        """获取标志值，如果不存在则初始化。
        
        Args:
            flag_name: 标志名称（例如，'CF'）
            
        Returns:
            标志值（1位BitVec）
        """
        if flag_name not in self.flags:
            # 使用0初始化
            self.flags[flag_name] = BitVecVal(0, 1)
        return self.flags[flag_name]
    
    def set_flag(self, flag_name: str, value: BitVec) -> None:
        """设置标志值。
        
        Args:
            flag_name: 标志名称（例如，'CF'）
            value: 标志值（必须是1位BitVec）
        """
        if value.size() != 1:
            raise ValueError(f"Flag value must be 1 bit, got {value.size()}")
        self.flags[flag_name] = value

