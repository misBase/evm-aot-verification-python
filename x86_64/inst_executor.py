"""
x86-64指令执行器。

本模块提供InstructionExecutor类，使用指令语义和执行状态执行指令序列。
"""

from typing import List
from z3 import BitVec, BitVecVal, Concat, Extract
from .models import X86Instruction, Register
from .execution_state import ExecutionState
from .disassembler import parse_operands


class InstructionExecutor:
    """使用语义建模执行x86-64指令序列。"""
    
    def __init__(self):
        """初始化指令执行器。"""
        pass
    
    def execute_instruction(self, state: ExecutionState, instruction: X86Instruction) -> None:
        """执行单个指令，更新执行状态。
        
        Args:
            state: 当前执行状态
            instruction: 要执行的指令
        """
        mnemonic = instruction.mnemonic.lower()
        op_str = instruction.op_str
        
        # 解析操作数
        operands = parse_operands(op_str)
        
        if mnemonic == 'mov':
            self._execute_mov(state, operands)
        elif mnemonic == 'add':
            self._execute_add(state, operands)
        elif mnemonic == 'adc':
            self._execute_adc(state, operands)
        elif mnemonic == 'sub':
            self._execute_sub(state, operands)
        elif mnemonic == 'cmp':
            self._execute_cmp(state, operands)
        elif mnemonic in ['jb', 'jae', 'jmp']:
            # 条件/无条件跳转 - 目前，我们继续执行
            # 在完整实现中，我们将跟踪控制流
            # 为了验证目的，我们假设采用成功路径
            pass
        elif mnemonic == 'ret':
            # RET指令 - 目前，我们只是继续
            # 在完整实现中，我们将从函数返回
            pass
        else:
            raise ValueError(f"Unsupported instruction: {mnemonic}")
    
    def _execute_mov(self, state: ExecutionState, operands: dict) -> None:
        """执行MOV指令。
        
        支持：
        - MOV reg, [base+offset]  （从内存加载）
        - MOV [base+offset], reg  （存储到内存）
        - MOV reg1, reg2          （寄存器到寄存器）
        - MOV reg, immediate      （加载立即值）
        - MOV [base+offset], immediate  （将立即值存储到内存）
        """
        if operands['is_memory'] and operands['dest_reg']:
            # MOV reg, [base+offset]
            base_reg = operands['base_reg']
            offset = operands['offset']
            dest_reg = operands['dest_reg']
            
            if base_reg not in [Register.R14, Register.R13]:
                raise ValueError(f"Unsupported base register for MOV: {base_reg}")
            
            # 从内存加载
            mem_val = state.load_memory(offset)
            state.set_register(dest_reg, mem_val)
            
        elif operands['is_memory'] and operands['src_reg']:
            # MOV [base+offset], reg
            base_reg = operands['base_reg']
            offset = operands['offset']
            src_reg = operands['src_reg']
            
            if base_reg not in [Register.R14, Register.R13]:
                raise ValueError(f"Unsupported base register for MOV: {base_reg}")
            
            # 存储到内存
            reg_val = state.get_register(src_reg)
            state.store_memory(offset, reg_val)
            
        elif operands['is_memory'] and operands['immediate'] is not None:
            # MOV [base+offset], immediate（例如，MOV BYTE PTR [r13+0xe0], 0xc）
            base_reg = operands['base_reg']
            offset = operands['offset']
            immediate = operands['immediate']
            
            if base_reg not in [Register.R14, Register.R13]:
                raise ValueError(f"Unsupported base register for MOV: {base_reg}")
            
            # 将立即值存储到内存（根据大小进行符号扩展或零扩展）
            # 对于字节操作，我们将存储为64位，并进行适当的扩展
            imm_val = BitVecVal(immediate & 0xFF, 64)  # 字节操作
            state.store_memory(offset, imm_val)
            
        elif operands['dest_reg'] and operands['src_reg']:
            # MOV reg1, reg2
            dest_reg = operands['dest_reg']
            src_reg = operands['src_reg']
            
            src_val = state.get_register(src_reg)
            state.set_register(dest_reg, src_val)
            
        elif operands['dest_reg'] and operands['immediate'] is not None:
            # MOV reg, immediate
            dest_reg = operands['dest_reg']
            immediate = operands['immediate']
            
            # 将立即值符号扩展到64位
            imm_val = BitVecVal(immediate, 64)
            state.set_register(dest_reg, imm_val)
        else:
            raise ValueError(f"Unsupported MOV operand combination: {operands}")
    
    def _execute_add(self, state: ExecutionState, operands: dict) -> None:
        """执行ADD指令。
        
        支持：
        - ADD reg, [base+offset]  （将内存加到寄存器）
        - ADD reg, reg            （将寄存器加到寄存器）
        """
        if not operands['dest_reg']:
            raise ValueError(f"ADD instruction must have register destination: {operands}")
        
        dest_reg = operands['dest_reg']
        reg_val = state.get_register(dest_reg)
        
        if operands['is_memory']:
            # ADD reg, [base+offset]
            base_reg = operands['base_reg']
            offset = operands['offset']
            
            if base_reg not in [Register.R14, Register.R13]:
                raise ValueError(f"Unsupported base register for ADD: {base_reg}")
            
            # 加载内存值
            mem_val = state.load_memory(offset)
            
            # 执行加法（64位，带进位生成）
            reg_ext = Concat(BitVecVal(0, 1), reg_val)
            mem_ext = Concat(BitVecVal(0, 1), mem_val)
            sum_ext = reg_ext + mem_ext
            
            # 提取结果和进位
            result = Extract(63, 0, sum_ext)
            carry_out = Extract(64, 64, sum_ext)
            
            # 更新寄存器
            state.set_register(dest_reg, result)
            
            # 更新进位标志
            state.set_flag('CF', carry_out)
            
        elif operands['src_reg']:
            # ADD reg, reg
            src_reg = operands['src_reg']
            src_val = state.get_register(src_reg)
            
            # 执行加法（64位，带进位生成）
            reg_ext = Concat(BitVecVal(0, 1), reg_val)
            src_ext = Concat(BitVecVal(0, 1), src_val)
            sum_ext = reg_ext + src_ext
            
            # 提取结果和进位
            result = Extract(63, 0, sum_ext)
            carry_out = Extract(64, 64, sum_ext)
            
            # 更新寄存器
            state.set_register(dest_reg, result)
            
            # 更新进位标志
            state.set_flag('CF', carry_out)
        else:
            raise ValueError(f"Unsupported ADD operand combination: {operands}")
    
    def _execute_adc(self, state: ExecutionState, operands: dict) -> None:
        """执行ADC（带进位加法）指令。
        
        支持：
        - ADC reg, [base+offset]  （将内存和进位加到寄存器）
        """
        if not operands['dest_reg'] or not operands['is_memory']:
            raise ValueError(f"ADC instruction must have register destination and memory source: {operands}")
        
        dest_reg = operands['dest_reg']
        base_reg = operands['base_reg']
        offset = operands['offset']
        
        if base_reg != Register.R14:
            raise ValueError(f"Unsupported base register for ADC: {base_reg}")
        
        # 获取当前寄存器值
        reg_val = state.get_register(dest_reg)
        
        # 加载内存值
        mem_val = state.load_memory(offset)
        
        # 获取进位标志
        carry_in = state.get_flag('CF')
        
        # 执行带进位加法（64位，带进位生成）
        reg_ext = Concat(BitVecVal(0, 1), reg_val)
        mem_ext = Concat(BitVecVal(0, 1), mem_val)
        carry_ext = Concat(BitVecVal(0, 64), carry_in)
        sum_ext = reg_ext + mem_ext + carry_ext
        
        # 提取结果和进位
        result = Extract(63, 0, sum_ext)
        carry_out = Extract(64, 64, sum_ext)
        
        # 更新寄存器
        state.set_register(dest_reg, result)
        
        # 更新进位标志
        state.set_flag('CF', carry_out)
    
    def _execute_sub(self, state: ExecutionState, operands: dict) -> None:
        """执行SUB指令。
        
        支持：
        - SUB reg, immediate  （从寄存器减去立即值）
        """
        if not operands['dest_reg']:
            raise ValueError(f"SUB instruction must have register destination: {operands}")
        
        dest_reg = operands['dest_reg']
        reg_val = state.get_register(dest_reg)
        
        if operands['immediate'] is not None:
            # SUB reg, immediate
            imm_val = BitVecVal(operands['immediate'], 64)
            result = reg_val - imm_val
            state.set_register(dest_reg, result)
        else:
            raise ValueError(f"Unsupported SUB operand combination: {operands}")
    
    def _execute_cmp(self, state: ExecutionState, operands: dict) -> None:
        """执行CMP指令。
        
        CMP根据比较设置标志，但不修改操作数。
        支持：
        - CMP reg, immediate  （将寄存器与立即值比较）
        """
        if not operands['dest_reg']:
            raise ValueError(f"CMP instruction must have register operand: {operands}")
        
        dest_reg = operands['dest_reg']
        reg_val = state.get_register(dest_reg)
        
        if operands['immediate'] is not None:
            # CMP reg, immediate
            imm_val = BitVecVal(operands['immediate'], 64)
            # 计算用于设置标志的结果
            result = reg_val - imm_val
            
            # 根据比较设置标志
            # CF（进位标志）：如果无符号减法会借位则设置
            # 目前，我们将符号地计算它
            reg_ext = Concat(BitVecVal(0, 1), reg_val)
            imm_ext = Concat(BitVecVal(0, 1), imm_val)
            diff_ext = reg_ext - imm_ext
            cf = Extract(64, 64, diff_ext)
            state.set_flag('CF', cf)
            
            # ZF（零标志）：如果结果为零则设置
            # reg_val == imm_val返回BoolRef，转换为1位BitVec
            zf_bool = (reg_val == imm_val)
            # 将BoolRef转换为1位BitVec：IfThenElse(condition, 1, 0)
            from z3 import If
            zf = If(zf_bool, BitVecVal(1, 1), BitVecVal(0, 1))
            state.set_flag('ZF', zf)
        else:
            raise ValueError(f"Unsupported CMP operand combination: {operands}")
    
    def execute_sequence(self, state: ExecutionState, instructions: List[X86Instruction]) -> None:
        """执行指令序列。
        
        Args:
            state: 初始执行状态（将被修改）
            instructions: 要执行的指令列表
        """
        for instruction in instructions:
            self.execute_instruction(state, instruction)

