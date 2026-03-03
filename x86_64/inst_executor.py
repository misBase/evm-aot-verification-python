"""
x86-64指令执行器。

本模块提供InstructionExecutor类，使用指令语义和执行状态执行指令序列。
"""

from typing import List
from z3 import BitVec, BitVecVal, Concat, Extract, LShR, UDiv, URem, If, Not, And, Or
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

        # 解析操作数
        operands = parse_operands(instruction)

        if mnemonic == 'mov' or mnemonic == 'movabs':
            self._execute_mov(state, operands)
        elif mnemonic == 'lea':
            self._execute_lea(state, operands, instruction)
        elif mnemonic == 'add':
            self._execute_add(state, operands)
        elif mnemonic == 'adc':
            self._execute_adc(state, operands)
        elif mnemonic == 'sbb':
            self._execute_sbb(state, operands)
        elif mnemonic == 'sub':
            self._execute_sub(state, operands)
        elif mnemonic == 'inc':
            self._execute_inc(state, operands)
        elif mnemonic == 'movzx':
            self._execute_movzx(state, operands)
        elif mnemonic == 'shl':
            self._execute_shl(state, operands)
        elif mnemonic == 'shr':
            self._execute_shr(state, operands)
        elif mnemonic == 'not':
            self._execute_not(state, operands)
        elif mnemonic == 'bswap':
            self._execute_bswap(state, operands)
        elif mnemonic == 'div':
            self._execute_div(state, operands)
        elif mnemonic == 'cmp':
            self._execute_cmp(state, operands)
        elif mnemonic == 'mul':
            self._execute_mul(state, operands)
        elif mnemonic == 'and':
            self._execute_and(state, operands)
        elif mnemonic == 'or':
            self._execute_or(state, operands)
        elif mnemonic == 'xor':
            self._execute_xor(state, operands)
        elif mnemonic == 'nop':
            pass
        elif mnemonic.startswith('set'):
            self._execute_setcc(state, mnemonic, operands)
        elif mnemonic in ['jb', 'jae', 'ja', 'jbe', 'je', 'jne', 'jl', 'jle', 'jg', 'jge', 'jmp']:
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

    def _update_add_flags(self, state: ExecutionState, lhs, rhs, result, carry_out) -> None:
        """更新 ADD/ADC 类指令使用的核心标志。"""
        overflow = Extract(63, 63, (lhs ^ result) & (rhs ^ result))
        zf = If(result == BitVecVal(0, 64), BitVecVal(1, 1), BitVecVal(0, 1))
        sf = Extract(63, 63, result)
        state.set_flag('CF', carry_out)
        state.set_flag('OF', overflow)
        state.set_flag('ZF', zf)
        state.set_flag('SF', sf)
    
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
            offset = operands['offset']
            dest_reg = operands['dest_reg']
            
            # 从内存加载
            mem_val = state.load_memory(offset)
            state.set_register(dest_reg, mem_val)
            
        elif operands['is_memory'] and operands['src_reg']:
            # MOV [base+offset], reg
            offset = operands['offset']
            src_reg = operands['src_reg']
            
            # 存储到内存
            reg_val = state.get_register(src_reg)
            state.store_memory(offset, reg_val)
            
        elif operands['is_memory'] and operands['immediate'] is not None:
            # MOV [base+offset], immediate（例如，MOV BYTE PTR [r13+0xe0], 0xc）
            offset = operands['offset']
            immediate = operands['immediate']
            
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

    def _execute_lea(self, state: ExecutionState, operands: dict, instruction: X86Instruction) -> None:
        """执行 LEA 指令（仅计算地址，不访问内存）。"""
        if not operands['dest_reg'] or not operands['is_memory']:
            raise ValueError(f"Unsupported LEA operand combination: {operands}")

        offset = operands.get('offset', 0)
        base_reg = operands.get('base_reg')
        index_reg = operands.get('index_reg')
        scale = operands.get('scale', 1) or 1

        if base_reg:
            addr = state.get_register(base_reg) + BitVecVal(offset, 64)
        elif 'rip' in instruction.op_str.lower():
            # RIP 相对寻址：next_ip + disp
            addr = BitVecVal(instruction.addr + instruction.size + offset, 64)
        else:
            addr = BitVecVal(offset, 64)

        if index_reg:
            index_val = state.get_register(index_reg)
            if scale != 1:
                index_val = index_val * BitVecVal(scale, 64)
            addr = addr + index_val

        state.set_register(operands['dest_reg'], addr)
    
    def _execute_add(self, state: ExecutionState, operands: dict) -> None:
        """执行ADD指令。
        
        支持：
        - ADD reg, [base+offset]  （将内存加到寄存器）
        - ADD reg, reg            （将寄存器加到寄存器）
        """
        if operands['is_memory'] and not operands['dest_reg']:
            # ADD [base+offset], reg/imm
            offset = operands['offset']
            mem_val = state.load_memory(offset)

            if operands['src_reg']:
                rhs_val = state.get_register(operands['src_reg'])
            elif operands['immediate'] is not None:
                rhs_val = BitVecVal(operands['immediate'], 64)
            else:
                raise ValueError(f"Unsupported ADD operand combination: {operands}")

            mem_ext = Concat(BitVecVal(0, 1), mem_val)
            rhs_ext = Concat(BitVecVal(0, 1), rhs_val)
            sum_ext = mem_ext + rhs_ext
            result = Extract(63, 0, sum_ext)
            carry_out = Extract(64, 64, sum_ext)

            state.store_memory(offset, result)
            self._update_add_flags(state, mem_val, rhs_val, result, carry_out)
            return

        if not operands['dest_reg']:
            raise ValueError(f"ADD instruction must have register destination: {operands}")

        dest_reg = operands['dest_reg']
        reg_val = state.get_register(dest_reg)

        if operands['is_memory']:
            # ADD reg, [base+offset]
            offset = operands['offset']
            
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
            self._update_add_flags(state, reg_val, mem_val, result, carry_out)
            
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
            self._update_add_flags(state, reg_val, src_val, result, carry_out)
        elif operands['immediate'] is not None:
            imm_val = BitVecVal(operands['immediate'], 64)
            reg_ext = Concat(BitVecVal(0, 1), reg_val)
            imm_ext = Concat(BitVecVal(0, 1), imm_val)
            sum_ext = reg_ext + imm_ext
            result = Extract(63, 0, sum_ext)
            carry_out = Extract(64, 64, sum_ext)
            state.set_register(dest_reg, result)
            self._update_add_flags(state, reg_val, imm_val, result, carry_out)
        else:
            raise ValueError(f"Unsupported ADD operand combination: {operands}")
    
    def _execute_adc(self, state: ExecutionState, operands: dict) -> None:
        """执行ADC（带进位加法）指令。
        
        支持：
        - ADC reg, [base+offset]  （将内存和进位加到寄存器）
        """
        if not operands['dest_reg']:
            raise ValueError(f"ADC instruction must have register destination: {operands}")
        
        dest_reg = operands['dest_reg']
        
        # 获取当前寄存器值
        reg_val = state.get_register(dest_reg)
        
        if operands['is_memory']:
            rhs_val = state.load_memory(operands['offset'])
        elif operands['src_reg']:
            rhs_val = state.get_register(operands['src_reg'])
        elif operands['immediate'] is not None:
            rhs_val = BitVecVal(operands['immediate'], 64)
        else:
            raise ValueError(f"Unsupported ADC operand combination: {operands}")
        
        # 获取进位标志
        carry_in = state.get_flag('CF')
        
        # 执行带进位加法（64位，带进位生成）
        reg_ext = Concat(BitVecVal(0, 1), reg_val)
        rhs_ext = Concat(BitVecVal(0, 1), rhs_val)
        carry_ext = Concat(BitVecVal(0, 64), carry_in)
        sum_ext = reg_ext + rhs_ext + carry_ext
        
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
        
        if operands['is_memory']:
            rhs_val = state.load_memory(operands['offset'])
        elif operands['src_reg']:
            rhs_val = state.get_register(operands['src_reg'])
        elif operands['immediate'] is not None:
            rhs_val = BitVecVal(operands['immediate'], 64)
        else:
            raise ValueError(f"Unsupported SUB operand combination: {operands}")
        result = reg_val - rhs_val
        state.set_register(dest_reg, result)

    def _execute_sbb(self, state: ExecutionState, operands: dict) -> None:
        """执行SBB指令。"""
        if not operands['dest_reg']:
            raise ValueError(f"SBB instruction must have register destination: {operands}")

        dest_reg = operands['dest_reg']
        lhs = state.get_register(dest_reg)
        carry_in = state.get_flag('CF')

        if operands['is_memory']:
            rhs = state.load_memory(operands['offset'])
        elif operands['src_reg']:
            rhs = state.get_register(operands['src_reg'])
        elif operands['immediate'] is not None:
            rhs = BitVecVal(operands['immediate'], 64)
        else:
            raise ValueError(f"Unsupported SBB operand combination: {operands}")

        result = lhs - rhs - Concat(BitVecVal(0, 63), carry_in)
        state.set_register(dest_reg, result)

    def _execute_inc(self, state: ExecutionState, operands: dict) -> None:
        """执行INC指令。

        支持：
        - INC reg
        """
        if not operands['dest_reg']:
            raise ValueError(f"INC instruction must have register destination: {operands}")

        dest_reg = operands['dest_reg']
        reg_val = state.get_register(dest_reg)
        state.set_register(dest_reg, reg_val + BitVecVal(1, 64))

    def _execute_movzx(self, state: ExecutionState, operands: dict) -> None:
        """执行MOVZX指令（简化版，仅保留零扩展效果）。"""
        if not operands['dest_reg']:
            raise ValueError(f"MOVZX instruction must have register destination: {operands}")

        if operands['is_memory']:
            src_val = state.load_memory(operands['offset']) & BitVecVal(0xFF, 64)
        elif operands['src_reg']:
            src_val = state.get_register(operands['src_reg']) & BitVecVal(0xFF, 64)
        else:
            raise ValueError(f"Unsupported MOVZX operand combination: {operands}")

        state.set_register(operands['dest_reg'], src_val)

    def _execute_shl(self, state: ExecutionState, operands: dict) -> None:
        """执行SHL指令（寄存器目标）。"""
        if not operands['dest_reg']:
            raise ValueError(f"SHL instruction must have register destination: {operands}")
        dest_reg = operands['dest_reg']
        value = state.get_register(dest_reg)

        if operands['immediate'] is not None:
            count = BitVecVal(operands['immediate'] & 0x3F, 64)
        elif operands['src_reg']:
            count = state.get_register(operands['src_reg']) & BitVecVal(0x3F, 64)
        else:
            count = BitVecVal(0, 64)

        state.set_register(dest_reg, value << count)

    def _execute_shr(self, state: ExecutionState, operands: dict) -> None:
        """执行SHR指令（寄存器目标）。"""
        if not operands['dest_reg']:
            raise ValueError(f"SHR instruction must have register destination: {operands}")
        dest_reg = operands['dest_reg']
        value = state.get_register(dest_reg)

        if operands['immediate'] is not None:
            count = BitVecVal(operands['immediate'] & 0x3F, 64)
        elif operands['src_reg']:
            count = state.get_register(operands['src_reg']) & BitVecVal(0x3F, 64)
        else:
            count = BitVecVal(0, 64)

        state.set_register(dest_reg, LShR(value, count))

    def _execute_not(self, state: ExecutionState, operands: dict) -> None:
        """执行NOT指令。"""
        if operands['is_memory'] and not operands['dest_reg']:
            offset = operands['offset']
            state.store_memory(offset, ~state.load_memory(offset))
            return

        if not operands['dest_reg']:
            raise ValueError(f"NOT instruction must have destination: {operands}")
        dest_reg = operands['dest_reg']
        state.set_register(dest_reg, ~state.get_register(dest_reg))

    def _execute_bswap(self, state: ExecutionState, operands: dict) -> None:
        """执行BSWAP指令。"""
        if not operands['dest_reg']:
            raise ValueError(f"BSWAP instruction must have register operand: {operands}")
        dest_reg = operands['dest_reg']
        value = state.get_register(dest_reg)
        swapped = Concat(
            Extract(7, 0, value),
            Extract(15, 8, value),
            Extract(23, 16, value),
            Extract(31, 24, value),
            Extract(39, 32, value),
            Extract(47, 40, value),
            Extract(55, 48, value),
            Extract(63, 56, value),
        )
        state.set_register(dest_reg, swapped)

    def _execute_div(self, state: ExecutionState, operands: dict) -> None:
        """执行DIV指令（RDX:RAX / op）。"""
        if operands['is_memory']:
            divisor = state.load_memory(operands['offset'])
        elif operands['dest_reg']:
            divisor = state.get_register(operands['dest_reg'])
        else:
            raise ValueError(f"DIV instruction must have memory/register operand: {operands}")

        rax = state.get_register(Register.RAX)
        rdx = state.get_register(Register.RDX)
        dividend = Concat(rdx, rax)
        divisor128 = Concat(BitVecVal(0, 64), divisor)

        q = UDiv(dividend, divisor128)
        r = URem(dividend, divisor128)
        state.set_register(Register.RAX, Extract(63, 0, q))
        state.set_register(Register.RDX, Extract(63, 0, r))
    
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
            rhs_val = BitVecVal(operands['immediate'], 64)
        elif operands['src_reg']:
            rhs_val = state.get_register(operands['src_reg'])
        elif operands['is_memory']:
            rhs_val = state.load_memory(operands['offset'])
        else:
            raise ValueError(f"Unsupported CMP operand combination: {operands}")

        reg_ext = Concat(BitVecVal(0, 1), reg_val)
        rhs_ext = Concat(BitVecVal(0, 1), rhs_val)
        diff_ext = reg_ext - rhs_ext
        cf = Extract(64, 64, diff_ext)
        zf = If(reg_val == rhs_val, BitVecVal(1, 1), BitVecVal(0, 1))
        state.set_flag('CF', cf)
        state.set_flag('ZF', zf)

    def _execute_mul(self, state: ExecutionState, operands: dict) -> None:
        """执行MUL指令（RDX:RAX = RAX * op）。"""
        if operands['is_memory']:
            op_val = state.load_memory(operands['offset'])
        elif operands['dest_reg']:
            op_val = state.get_register(operands['dest_reg'])
        else:
            raise ValueError(f"MUL instruction must have memory/register operand: {operands}")

        rax = state.get_register(Register.RAX)
        product = Concat(BitVecVal(0, 64), rax) * Concat(BitVecVal(0, 64), op_val)
        state.set_register(Register.RAX, Extract(63, 0, product))
        state.set_register(Register.RDX, Extract(127, 64, product))

    def _execute_and(self, state: ExecutionState, operands: dict) -> None:
        """执行AND指令。"""
        if not operands['dest_reg']:
            raise ValueError(f"AND instruction must have register destination: {operands}")
        dest_reg = operands['dest_reg']
        lhs = state.get_register(dest_reg)
        if operands['is_memory']:
            rhs = state.load_memory(operands['offset'])
        elif operands['src_reg']:
            rhs = state.get_register(operands['src_reg'])
        elif operands['immediate'] is not None:
            rhs = BitVecVal(operands['immediate'], 64)
        else:
            raise ValueError(f"Unsupported AND operand combination: {operands}")
        state.set_register(dest_reg, lhs & rhs)

    def _execute_or(self, state: ExecutionState, operands: dict) -> None:
        """执行OR指令。"""
        if not operands['dest_reg']:
            raise ValueError(f"OR instruction must have register destination: {operands}")
        dest_reg = operands['dest_reg']
        lhs = state.get_register(dest_reg)
        if operands['is_memory']:
            rhs = state.load_memory(operands['offset'])
        elif operands['src_reg']:
            rhs = state.get_register(operands['src_reg'])
        elif operands['immediate'] is not None:
            rhs = BitVecVal(operands['immediate'], 64)
        else:
            raise ValueError(f"Unsupported OR operand combination: {operands}")
        state.set_register(dest_reg, lhs | rhs)

    def _execute_xor(self, state: ExecutionState, operands: dict) -> None:
        """执行XOR指令。"""
        if not operands['dest_reg']:
            raise ValueError(f"XOR instruction must have register destination: {operands}")
        dest_reg = operands['dest_reg']
        lhs = state.get_register(dest_reg)
        if operands['is_memory']:
            rhs = state.load_memory(operands['offset'])
        elif operands['src_reg']:
            rhs = state.get_register(operands['src_reg'])
        elif operands['immediate'] is not None:
            rhs = BitVecVal(operands['immediate'], 64)
        else:
            raise ValueError(f"Unsupported XOR operand combination: {operands}")
        state.set_register(dest_reg, lhs ^ rhs)

    def _execute_setcc(self, state: ExecutionState, mnemonic: str, operands: dict) -> None:
        """执行SETcc指令（仅寄存器目标）。"""
        if not operands['dest_reg']:
            raise ValueError(f"SETcc instruction must have register destination: {operands}")

        cf = state.get_flag('CF') == BitVecVal(1, 1)
        zf = state.get_flag('ZF') == BitVecVal(1, 1)
        sf = state.get_flag('SF') == BitVecVal(1, 1)
        of = state.get_flag('OF') == BitVecVal(1, 1)
        sf_eq_of = sf == of
        sf_ne_of = Not(sf == of)

        conds = {
            'setb': cf,
            'setae': Not(cf),
            'seta': And(Not(cf), Not(zf)),
            'setbe': Or(cf, zf),
            'sete': zf,
            'setne': Not(zf),
            'setl': sf_ne_of,
            'setle': Or(zf, sf_ne_of),
            'setg': And(Not(zf), sf_eq_of),
            'setge': sf_eq_of,
            'sets': sf,
            'setns': Not(sf),
        }
        if mnemonic not in conds:
            raise ValueError(f"Unsupported SETcc instruction: {mnemonic}")

        old_val = state.get_register(operands['dest_reg'])
        low8 = If(conds[mnemonic], BitVecVal(1, 8), BitVecVal(0, 8))
        state.set_register(operands['dest_reg'], Concat(Extract(63, 8, old_val), low8))
    
    def execute_sequence(self, state: ExecutionState, instructions: List[X86Instruction]) -> None:
        """执行指令序列。
        
        Args:
            state: 初始执行状态（将被修改）
            instructions: 要执行的指令列表
        """
        for instruction in instructions:
            self.execute_instruction(state, instruction)
