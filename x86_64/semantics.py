"""
x86-64指令语义建模。

本模块使用Z3为x86-64指令提供语义建模。
"""

from z3 import BitVec, BitVecVal, Concat, Extract, If
from typing import List, Dict, Optional, Any, Tuple
from .models import X86Block, X86Instruction, Register
from .execution_state import ExecutionState
from .inst_executor import InstructionExecutor
from .disassembler import disassemble_hex, parse_operands
from common.uint256 import Uint256
from state.smt_state import SMTState

# RETURN指令的常量
EVM_NATIVE_CALL_STATUS_CODE_RETURNED = 0  # evmNativeCallStatusCodeReturned = iota
EVM_CALL_ENGINE_EXIT_CONTEXT_NATIVE_CALL_STATUS_CODE_OFFSET = 200  # 168 + 8 + 8 + 8 + 32
AMD64_RESERVED_REGISTER_FOR_CALL_ENGINE = Register.R13  # 指向callEngine实例的指针
AMD64_RESERVED_REGISTER_FOR_MEMORY = Register.R15  # 指向EVM内存的指针（memoryElement0Address）


class X86InstructionSemantics:
    """单个x86-64指令的语义建模。"""
    
    def mov_reg_mem_semantics(self, dest_reg: Register, base_reg: Register, 
                              offset: int, mem_vars: Dict[int, BitVec]) -> BitVec:
        """建模MOV reg, [base+offset]指令。
        
        Args:
            dest_reg: 目标寄存器
            base_reg: 基址寄存器（对于栈访问应为R14）
            offset: 内存偏移量
            mem_vars: 将偏移量映射到符号内存变量的字典
            
        Returns:
            加载到目标寄存器的值
        """
        if base_reg == Register.R14:
            # 从EVM栈内存加载
            if offset not in mem_vars:
                # 如果不存在则创建符号变量
                mem_vars[offset] = BitVec(f"mem_{offset:+d}", 64)
            return mem_vars[offset]
        else:
            raise ValueError(f"Unsupported base register: {base_reg}")
    
    def add_reg_mem_semantics(self, dest_reg: Register, base_reg: Register,
                              offset: int, mem_vars: Dict[int, BitVec],
                              carry_in: Optional[BitVec] = None) -> Tuple[BitVec, BitVec]:
        """建模ADD/ADC reg, [base+offset]指令。
        
        Args:
            dest_reg: 目标寄存器
            base_reg: 基址寄存器
            offset: 内存偏移量
            mem_vars: 将偏移量映射到符号内存变量的字典
            carry_in: 可选的进位输入（用于ADC）
            
        Returns:
            (result, carry_out)元组，两者都是64位BitVecs
        """
        # 获取当前寄存器值（假设它在mem_vars中，使用特殊键）
        # 为简单起见，我们将单独跟踪它
        reg_val_key = f"reg_{dest_reg.value}"
        if reg_val_key not in mem_vars:
            # 初始化寄存器值
            mem_vars[reg_val_key] = BitVec(f"{dest_reg.value}_init", 64)
        
        reg_val = mem_vars[reg_val_key]
        mem_val = self.mov_reg_mem_semantics(dest_reg, base_reg, offset, mem_vars)
        
        # 执行带可选进位的加法
        if carry_in is not None:
            # ADC：带进位加法
            reg_ext = Concat(BitVecVal(0, 1), reg_val)
            mem_ext = Concat(BitVecVal(0, 1), mem_val)
            carry_ext = Concat(BitVecVal(0, 64), carry_in)
            sum_ext = reg_ext + mem_ext + carry_ext
        else:
            # ADD：简单加法
            reg_ext = Concat(BitVecVal(0, 1), reg_val)
            mem_ext = Concat(BitVecVal(0, 1), mem_val)
            sum_ext = reg_ext + mem_ext
        
        result = Extract(63, 0, sum_ext)
        carry_out = Extract(64, 64, sum_ext)
        
        # 更新寄存器值
        mem_vars[reg_val_key] = result
        
        return result, carry_out
    
    def mov_mem_reg_semantics(self, base_reg: Register, offset: int,
                              src_reg: Register, mem_vars: Dict[int, BitVec]) -> None:
        """建模MOV [base+offset], reg指令。
        
        Args:
            base_reg: 基址寄存器
            offset: 内存偏移量
            src_reg: 源寄存器
            mem_vars: 将偏移量映射到符号内存变量的字典
        """
        if base_reg == Register.R14:
            # 存储到EVM栈内存
            reg_val_key = f"reg_{src_reg.value}"
            if reg_val_key not in mem_vars:
                mem_vars[reg_val_key] = BitVec(f"{src_reg.value}_init", 64)
            mem_vars[offset] = mem_vars[reg_val_key]
        else:
            raise ValueError(f"Unsupported base register: {base_reg}")


class X86SemanticsModel:
    """x86-64指令序列的语义建模。"""
    
    def __init__(self):
        """初始化x86语义模型。"""
        self.instr_semantics = X86InstructionSemantics()
        self.executor = InstructionExecutor()
    
    def execute_instruction_sequence(self, 
                                    instructions: List[X86Instruction],
                                    initial_memory: Dict[int, BitVec],
                                    result_registers: Optional[List[Register]] = None) -> BitVec:
        """执行指令序列并提取结果。
        
        此方法创建执行状态，执行指令序列，
        并从寄存器状态中提取最终结果。
        
        Args:
            instructions: 要执行的X86Instruction对象列表
            initial_memory: 初始内存状态（将偏移量映射到BitVec值的字典）
            result_registers: 要从中提取结果的寄存器列表（从高到低顺序）。
                            如果为None，对于ADD序列默认为[RBX, RDX, RCX, RAX]。
                            每个寄存器应为64位，它们将被连接
                            形成256位结果。
            
        Returns:
            表示256位结果的逻辑公式，作为BitVec
        """
        # 使用初始内存创建执行状态
        state = ExecutionState(initial_memory=initial_memory)
        
        # 执行指令序列
        self.executor.execute_sequence(state, instructions)
        
        # 从寄存器中提取结果
        if result_registers is None:
            # ADD序列的默认值：result = [rbx, rdx, rcx, rax]
            result_registers = [Register.RBX, Register.RDX, Register.RCX, Register.RAX]
        
        # 获取寄存器值并组合成256位结果
        reg_values = [state.get_register(reg) for reg in result_registers]
        
        # 组合成256位结果（从高到低）
        result = Concat(*reg_values)
        
        return result
    
    def build_instructions_from_hex(self, hex_str: str, base_addr: int = 0) -> List[X86Instruction]:
        """从十六进制编码的机器码构建指令序列。
        
        这是一个通用方法，将十六进制机器码反汇编为
        X86Instruction对象。
        
        Args:
            hex_str: 包含机器码的十六进制字符串（带或不带空格/0x前缀）
            base_addr: 指令的基址（默认：0）
            
        Returns:
            X86Instruction对象列表
        """
        return disassemble_hex(hex_str, base_addr=base_addr)
    
    def build_sequence_semantics_from_hex(self,
                                         hex_sequence: str,
                                         mem_vars: Dict[int, BitVec],
                                         base_addr: int = 0,
                                         result_registers: Optional[List[Register]] = None) -> BitVec:
        """从十六进制机器码构建x86指令序列的逻辑公式。
        
        这是一个通用方法，反汇编十六进制机器码并执行
        指令序列以构建语义公式。
        
        Args:
            hex_sequence: 包含指令序列的十六进制字符串
            mem_vars: 将栈偏移量映射到符号内存变量的字典
            base_addr: 指令序列的基址（默认：0）
            result_registers: 要从中提取结果的寄存器列表（从高到低顺序）。
                            如果为None，对于256位结果默认为[RBX, RDX, RCX, RAX]。
                            每个寄存器应为64位，它们将被连接
                            形成256位结果。
                                    
        Returns:
            表示结果的逻辑公式，作为BitVec
        """
        # 从十六进制构建指令序列
        instructions = self.build_instructions_from_hex(hex_sequence, base_addr=base_addr)
        
        # 执行序列并从寄存器中提取结果
        return self.execute_instruction_sequence(
            instructions, 
            mem_vars,
            result_registers=result_registers
        )
    
    def build_sequence_from_limbs(self,
                                 hex_sequence: str,
                                 val1_limbs: List[BitVec],
                                 val2_limbs: List[BitVec],
                                 base_addr: int = 0,
                                 result_registers: Optional[List[Register]] = None) -> BitVec:
        """从limb列表构建指令序列语义。
        
        便利方法，从limb创建内存变量映射并
        从十六进制机器码执行指令序列。
        
        Args:
            hex_sequence: 包含指令序列的十六进制字符串
            val1_limbs: 第一个操作数的[z0, z1, z2, z3]（每个64位）
            val2_limbs: 第二个操作数的[z0, z1, z2, z3]（每个64位）
            base_addr: 指令序列的基址（默认：0）
            result_registers: 要从中提取结果的寄存器列表（从高到低顺序）。
                            如果为None，对于256位结果默认为[RBX, RDX, RCX, RAX]。
            
        Returns:
            表示256位结果的逻辑公式
        """
        if len(val1_limbs) != 4 or len(val2_limbs) != 4:
            raise ValueError("Expected 4 limbs for 256-bit value")
        
        mem_vars = {
            -0x40: val1_limbs[0],  # val1.z0
            -0x38: val1_limbs[1],  # val1.z1
            -0x30: val1_limbs[2],  # val1.z2
            -0x28: val1_limbs[3],  # val1.z3
            -0x20: val2_limbs[0],  # val2.z0
            -0x18: val2_limbs[1],  # val2.z1
            -0x10: val2_limbs[2],  # val2.z2
            -0x08: val2_limbs[3],  # val2.z3
        }
        
        return self.build_sequence_semantics_from_hex(
            hex_sequence, 
            mem_vars, 
            base_addr=base_addr,
            result_registers=result_registers
        )
    
    def build_block_semantics(self, 
                             block: X86Block, 
                             mem_vars: Dict[int, BitVec],
                             hex_sequence: Optional[str] = None,
                             result_registers: Optional[List[Register]] = None) -> Dict[str, Any]:
        """构建x86块的语义公式。
        
        Args:
            block: 要建模的x86块
            mem_vars: 初始内存状态（将偏移量映射到值的字典）
            hex_sequence: 包含指令序列的可选十六进制字符串。
                         如果为None，将尝试从block.instructions中提取。
            result_registers: 要从中提取结果的寄存器列表。
            
        Returns:
            包含以下内容的字典：
            - output_memory: 最终内存状态
            - semantic_formula: 块的总体语义公式
        """
        # 如果提供了hex_sequence，使用它
        if hex_sequence:
            result = self.build_sequence_semantics_from_hex(
                hex_sequence,
                mem_vars,
                base_addr=block.start_addr,
                result_registers=result_registers
            )
            return {
                'output_memory': mem_vars,
                'semantic_formula': result,
                'output_count': 1
            }
        
        # 否则，从块中执行指令
        # 这是当我们有X86Instruction对象时的回退
        if len(block.instructions) > 0:
            state = ExecutionState(initial_memory=mem_vars)
            self.executor.execute_sequence(state, block.instructions)
            
            # 如果未指定，从默认寄存器中提取结果
            if result_registers is None:
                result_registers = [Register.RBX, Register.RDX, Register.RCX, Register.RAX]
            
            reg_values = [state.get_register(reg) for reg in result_registers]
            result = Concat(*reg_values)
            
            return {
                'output_memory': state.memory,
                'semantic_formula': result,
                'output_count': 1
            }
        
        # 默认：返回恒等
        return {
            'output_memory': mem_vars,
            'semantic_formula': BitVecVal(0, 256),
            'output_count': 0
        }


def x86_instruction_to_z3(insn: X86Instruction, state: SMTState) -> SMTState:
    """将x86-64指令转换为Z3公式，更新状态。
    
    这是Alive2风格的直接公式构建方法。
    每个指令直接构建Z3表达式，无需执行模拟。
    
    Args:
        insn: 要转换的x86-64指令
        state: 当前SMT状态（将被修改）
        
    Returns:
        更新后的SMT状态
    """
    mnemonic = insn.mnemonic.lower()
    operands = parse_operands(insn.op_str)
    
    if mnemonic == 'mov':
        # MOV：将值从源移动到目标
        if operands['is_memory'] and operands['dest_reg']:
            # MOV reg, [base+offset]
            base_reg = operands['base_reg']
            offset = operands['offset']
            dest_reg = operands['dest_reg']
            
            if base_reg in [Register.R14, Register.R13]:
                # 从x86内存加载（R14 = 栈基址，R13 = callEngine指针）
                # offset可以是int（具体）或BitVec（符号）
                # 如果有索引寄存器，计算：base_offset + index_reg
                memory_offset = offset
                if 'index_reg' in operands and operands['index_reg']:
                    # 支持[base+index]寻址模式
                    index_reg = operands['index_reg']
                    index_val = state.x86_registers.get_register(index_reg)
                    # 如果需要，将具体offset转换为BitVec
                    if isinstance(offset, int):
                        offset_bv = BitVecVal(offset, 64)
                    else:
                        offset_bv = offset
                    memory_offset = offset_bv + index_val
                
                mem_val = state.x86_memory.load_limb(memory_offset)
                state.x86_registers.set_register(dest_reg, mem_val)
            else:
                raise ValueError(f"Unsupported base register for MOV: {base_reg}")
        
        elif operands['is_memory'] and operands['src_reg']:
            # MOV [base+offset], reg
            base_reg = operands['base_reg']
            offset = operands['offset']
            src_reg = operands['src_reg']
            
            if base_reg in [Register.R14, Register.R13]:
                # 存储到x86内存（R14 = 栈基址，R13 = callEngine指针）
                # offset可以是int（具体）或BitVec（符号）
                # 如果有索引寄存器，计算：base_offset + index_reg
                memory_offset = offset
                if 'index_reg' in operands and operands['index_reg']:
                    # 支持[base+index]寻址模式
                    index_reg = operands['index_reg']
                    index_val = state.x86_registers.get_register(index_reg)
                    # 如果需要，将具体offset转换为BitVec
                    if isinstance(offset, int):
                        offset_bv = BitVecVal(offset, 64)
                    else:
                        offset_bv = offset
                    memory_offset = offset_bv + index_val
                
                reg_val = state.x86_registers.get_register(src_reg)
                new_memory_state = state.x86_memory.store_limb(memory_offset, reg_val)
                state.x86_memory = new_memory_state
            else:
                raise ValueError(f"Unsupported base register for MOV: {base_reg}")
        
        elif operands['dest_reg'] and operands['src_reg']:
            # MOV reg1, reg2
            dest_reg = operands['dest_reg']
            src_reg = operands['src_reg']
            src_val = state.x86_registers.get_register(src_reg)
            state.x86_registers.set_register(dest_reg, src_val)
        
        elif operands['dest_reg'] and operands['immediate'] is not None:
            # MOV reg, immediate
            dest_reg = operands['dest_reg']
            immediate = operands['immediate']
            imm_val = BitVecVal(immediate, 64)
            state.x86_registers.set_register(dest_reg, imm_val)
        
        elif operands['is_memory'] and operands['immediate'] is not None:
            # MOV [base+offset], immediate（字节操作）
            base_reg = operands['base_reg']
            offset = operands['offset']
            immediate = operands['immediate']
            
            if base_reg in [Register.R14, Register.R13]:
                # 将立即值存储到内存（R14 = 栈基址，R13 = callEngine指针）
                imm_val = BitVecVal(immediate & 0xFF, 64)  # 字节操作
                new_memory_state = state.x86_memory.store_limb(offset, imm_val)
                state.x86_memory = new_memory_state
            else:
                raise ValueError(f"Unsupported base register for MOV: {base_reg}")
        
        return state
    
    elif mnemonic == 'add':
        # ADD：将源加到目标，设置进位标志
        if not operands['dest_reg']:
            raise ValueError(f"ADD instruction must have register destination: {operands}")
        
        dest_reg = operands['dest_reg']
        reg_val = state.x86_registers.get_register(dest_reg)
        
        if operands['is_memory']:
            # ADD reg, [base+offset]
            base_reg = operands['base_reg']
            offset = operands['offset']
            
            if base_reg in [Register.R14, Register.R13]:
                # 与内存相加（R14 = 栈基址，R13 = callEngine指针）
                # offset可以是int（具体）或BitVec（符号）
                # 如果有索引寄存器，计算：base_offset + index_reg
                memory_offset = offset
                if 'index_reg' in operands and operands['index_reg']:
                    index_reg = operands['index_reg']
                    index_val = state.x86_registers.get_register(index_reg)
                    if isinstance(offset, int):
                        offset_bv = BitVecVal(offset, 64)
                    else:
                        offset_bv = offset
                    memory_offset = offset_bv + index_val
                
                mem_val = state.x86_memory.load_limb(memory_offset)
                
                # 执行加法（64位，带进位生成）
                reg_ext = Concat(BitVecVal(0, 1), reg_val)
                mem_ext = Concat(BitVecVal(0, 1), mem_val)
                sum_ext = reg_ext + mem_ext
                
                # 提取结果和进位
                result = Extract(63, 0, sum_ext)
                carry_out = Extract(64, 64, sum_ext)
                
                # 更新寄存器和进位标志
                state.x86_registers.set_register(dest_reg, result)
                state.x86_registers.set_flag('CF', carry_out)
            else:
                raise ValueError(f"Unsupported base register for ADD: {base_reg}")
        
        elif operands['src_reg']:
            # ADD reg, reg
            src_reg = operands['src_reg']
            src_val = state.x86_registers.get_register(src_reg)
            
            # 执行加法
            reg_ext = Concat(BitVecVal(0, 1), reg_val)
            src_ext = Concat(BitVecVal(0, 1), src_val)
            sum_ext = reg_ext + src_ext
            
            result = Extract(63, 0, sum_ext)
            carry_out = Extract(64, 64, sum_ext)
            
            state.x86_registers.set_register(dest_reg, result)
            state.x86_registers.set_flag('CF', carry_out)
        
        return state
    
    elif mnemonic == 'adc':
        # ADC：带进位加法
        if not operands['dest_reg'] or not operands['is_memory']:
            raise ValueError(f"ADC instruction must have register destination and memory source: {operands}")
        
        dest_reg = operands['dest_reg']
        base_reg = operands['base_reg']
        offset = operands['offset']
        
        if base_reg not in [Register.R14, Register.R13]:
            raise ValueError(f"Unsupported base register for ADC: {base_reg}")
        
        reg_val = state.x86_registers.get_register(dest_reg)
        # offset可以是int（具体）或BitVec（符号）
        # 如果有索引寄存器，计算：base_offset + index_reg
        memory_offset = offset
        if 'index_reg' in operands and operands['index_reg']:
            index_reg = operands['index_reg']
            index_val = state.x86_registers.get_register(index_reg)
            if isinstance(offset, int):
                offset_bv = BitVecVal(offset, 64)
            else:
                offset_bv = offset
            memory_offset = offset_bv + index_val
        
        mem_val = state.x86_memory.load_limb(memory_offset)
        carry_in = state.x86_registers.get_flag('CF')
        
        # 执行带进位加法
        reg_ext = Concat(BitVecVal(0, 1), reg_val)
        mem_ext = Concat(BitVecVal(0, 1), mem_val)
        carry_ext = Concat(BitVecVal(0, 64), carry_in)
        sum_ext = reg_ext + mem_ext + carry_ext
        
        result = Extract(63, 0, sum_ext)
        carry_out = Extract(64, 64, sum_ext)
        
        state.x86_registers.set_register(dest_reg, result)
        state.x86_registers.set_flag('CF', carry_out)
        
        return state
    
    elif mnemonic == 'sub':
        # SUB：从目标减去源
        if not operands['dest_reg']:
            raise ValueError(f"SUB instruction must have register destination: {operands}")

        dest_reg = operands['dest_reg']
        reg_val = state.x86_registers.get_register(dest_reg)

        if operands['immediate'] is not None:
            # SUB reg, immediate
            imm_val = BitVecVal(operands['immediate'], 64)
            result = reg_val - imm_val
            state.x86_registers.set_register(dest_reg, result)

        return state
    
    elif mnemonic == 'cmp':
        # CMP：比较并设置标志（不修改操作数）
        if not operands['dest_reg']:
            raise ValueError(f"CMP instruction must have register operand: {operands}")
        
        dest_reg = operands['dest_reg']
        reg_val = state.x86_registers.get_register(dest_reg)
        
        if operands['immediate'] is not None:
            # CMP reg, immediate
            imm_val = BitVecVal(operands['immediate'], 64)
            result = reg_val - imm_val
            
            # 设置标志
            reg_ext = Concat(BitVecVal(0, 1), reg_val)
            imm_ext = Concat(BitVecVal(0, 1), imm_val)
            diff_ext = reg_ext - imm_ext
            cf = Extract(64, 64, diff_ext)
            state.x86_registers.set_flag('CF', cf)
            
            # ZF（零标志）
            zf_bool = (reg_val == imm_val)
            zf = If(zf_bool, BitVecVal(1, 1), BitVecVal(0, 1))
            state.x86_registers.set_flag('ZF', zf)
        
        return state
    
    elif mnemonic == 'ret':
        # RET指令：检查退出状态码，如果需要则提取返回数据
        # 从x86内存读取状态码：[R13 + evmCallEngineExitContextNativeCallStatusCodeOffset]
        
        # 获取R13寄存器值（callEngine指针）
        r13_value = state.x86_registers.get_register(AMD64_RESERVED_REGISTER_FOR_CALL_ENGINE)
        
        # 计算状态码内存地址
        status_code_offset = BitVecVal(EVM_CALL_ENGINE_EXIT_CONTEXT_NATIVE_CALL_STATUS_CODE_OFFSET, 64)
        status_code_addr = r13_value + status_code_offset
        
        # 从x86内存读取状态码（8位字节）
        status_code = state.x86_memory.load_byte(status_code_addr)
        
        # 检查状态码是否为RETURNED（0）
        # 重要：只有当status_code == RETURNED时，我们才应该设置返回值
        # 其他状态码（REVERTED、STOPPED、INVALID等）有不同的行为
        status_code_is_returned = (status_code == BitVecVal(EVM_NATIVE_CALL_STATUS_CODE_RETURNED, 8))
        
        # 只有当状态码为RETURNED时才提取返回数据
        # 对于其他状态码，我们不设置return_offset/return_length
        # 这与Go代码匹配：只有case evmNativeCallStatusCodeReturned设置返回值
        
        # 重要：x86-64不直接操作evm_stack或evm_memory
        # x86-64使用x86内存（通过R14用于栈，R15用于EVM内存）
        # 从x86内存获取offset和length（EVM栈通过R14存储在x86内存中）
        # Go代码：offset, size := c.PopUint64(), c.PopUint64()
        # 这意味着：首先弹出size（stack[0]），然后弹出offset（stack[1]）
        # x86内存中的栈布局：stack[0]在R14-0x40，stack[1]在R14-0x20
        
        # 获取R14寄存器值（栈基址指针）
        r14_value = state.x86_registers.get_register(Register.R14)
        
        # 使用绝对地址从x86内存中提取栈值
        # stack[0]（顶部）= size（length）在R14-0x40，stack[1] = offset在R14-0x20
        # 我们需要从x86内存加载256位值（4×64位limb）
        
        # Stack[0]（size/length）：从R14-0x40加载（4×64位limb）
        stack0_base = r14_value + BitVecVal(-0x40, 64)
        size_z0 = state.x86_memory.load_64bit(stack0_base)
        size_z1 = state.x86_memory.load_64bit(stack0_base + BitVecVal(8, 64))
        size_z2 = state.x86_memory.load_64bit(stack0_base + BitVecVal(16, 64))
        size_z3 = state.x86_memory.load_64bit(stack0_base + BitVecVal(24, 64))
        size_stack_value = Concat(size_z3, size_z2, size_z1, size_z0)  # 256位值
        
        # Stack[1]（offset）：从R14-0x20加载（4×64位limb）
        stack1_base = r14_value + BitVecVal(-0x20, 64)
        offset_z0 = state.x86_memory.load_64bit(stack1_base)
        offset_z1 = state.x86_memory.load_64bit(stack1_base + BitVecVal(8, 64))
        offset_z2 = state.x86_memory.load_64bit(stack1_base + BitVecVal(16, 64))
        offset_z3 = state.x86_memory.load_64bit(stack1_base + BitVecVal(24, 64))
        offset_stack_value = Concat(offset_z3, offset_z2, offset_z1, offset_z0)  # 256位值
        
        # 将256位栈值截断为64位用于offset和length
        # Go代码使用PopUint64()，所以我们需要64位值
        from z3 import Extract as Z3Extract
        if size_stack_value.size() == 256:
            length_bv = Z3Extract(63, 0, size_stack_value)  # 提取低64位
        elif size_stack_value.size() == 64:
            length_bv = size_stack_value
        else:
            raise ValueError(f"Unexpected size value size: {size_stack_value.size()}")
        
        if offset_stack_value.size() == 256:
            offset_bv = Z3Extract(63, 0, offset_stack_value)  # 提取低64位
        elif offset_stack_value.size() == 64:
            offset_bv = offset_stack_value
        else:
            raise ValueError(f"Unexpected offset value size: {offset_stack_value.size()}")
        
        # 重要：对return_offset和return_length使用条件符号值
        # 只有当status_code == RETURNED时才设置返回值
        # 不同的状态码有不同的行为（来自Go代码）：
        # - RETURNED（0）：返回数据（offset, size）- 这是我们验证的
        # - REVERTED：返回错误数据（不同的语义，不是成功返回）
        # - STOPPED：返回nil, nil（无返回数据）
        # - INVALID：返回错误（无返回数据）
        # 
        # 使用If表达式有条件地设置返回值：
        # - 如果status_code == RETURNED：使用提取的offset和length
        # - 否则：使用0（无返回值）
        
        # R15寄存器指向EVM内存基址（memoryElement0Address）
        r15_value = state.x86_registers.get_register(AMD64_RESERVED_REGISTER_FOR_MEMORY)
        
        # 使用If表达式有条件地设置返回值
        # 这允许符号地处理多条路径
        zero_64 = BitVecVal(0, 64)
        
        # 只有当status_code == RETURNED时才设置返回值
        # 否则，保持为0（无返回值）
        state.return_offset = If(status_code_is_returned, offset_bv, zero_64)
        state.return_length = If(status_code_is_returned, length_bv, zero_64)
        
        return state

    elif mnemonic == 'mul':
        # MUL：无符号乘法（RAX * src -> RDX:RAX）
        if not operands['dest_reg']:
            raise ValueError(f"MUL instruction must have register destination: {operands}")

        dest_reg = operands['dest_reg']
        reg_val = state.x86_registers.get_register(dest_reg)

        if operands['is_memory']:
            # MUL reg, [base+offset]
            base_reg = operands['base_reg']
            offset = operands['offset']

            if base_reg not in [Register.R14, Register.R13]:
                raise ValueError(f"Unsupported base register for MUL: {base_reg}")

            memory_offset = offset
            if 'index_reg' in operands and operands['index_reg']:
                index_reg = operands['index_reg']
                index_val = state.x86_registers.get_register(index_reg)
                if isinstance(offset, int):
                    offset_bv = BitVecVal(offset, 64)
                else:
                    offset_bv = offset
                memory_offset = offset_bv + index_val

            mem_val = state.x86_memory.load_64bit(memory_offset)

            # 执行64位乘法：result = reg_val * mem_val
            # 结果是128位：RDX:RAX（高64位在RDX，低64位在RAX）
            # 对于EVM验证，我们通常只关心低64位（截断）
            result = reg_val * mem_val

            # 存储低64位到目标寄存器
            result_low = Extract(63, 0, result)
            state.x86_registers.set_register(dest_reg, result_low)

            # 高64位存储到RDX（如果需要）
            result_high = Extract(127, 64, result)
            state.x86_registers.set_register(Register.RDX, result_high)

        elif operands['src_reg']:
            # MUL reg, reg
            src_reg = operands['src_reg']
            src_val = state.x86_registers.get_register(src_reg)

            # 执行乘法
            result = reg_val * src_val

            # 存储低64位
            result_low = Extract(63, 0, result)
            state.x86_registers.set_register(dest_reg, result_low)

            # 高64位存储到RDX
            result_high = Extract(127, 64, result)
            state.x86_registers.set_register(Register.RDX, result_high)

        return state

    elif mnemonic == 'and':
        # AND：按位与
        if not operands['dest_reg']:
            raise ValueError(f"AND instruction must have register destination: {operands}")

        dest_reg = operands['dest_reg']
        reg_val = state.x86_registers.get_register(dest_reg)

        if operands['is_memory']:
            # AND reg, [base+offset]
            base_reg = operands['base_reg']
            offset = operands['offset']

            if base_reg not in [Register.R14, Register.R13]:
                raise ValueError(f"Unsupported base register for AND: {base_reg}")

            memory_offset = offset
            if 'index_reg' in operands and operands['index_reg']:
                index_reg = operands['index_reg']
                index_val = state.x86_registers.get_register(index_reg)
                if isinstance(offset, int):
                    offset_bv = BitVecVal(offset, 64)
                else:
                    offset_bv = offset
                memory_offset = offset_bv + index_val

            mem_val = state.x86_memory.load_64bit(memory_offset)
            result = reg_val & mem_val
            state.x86_registers.set_register(dest_reg, result)

        elif operands['src_reg']:
            # AND reg, reg
            src_reg = operands['src_reg']
            src_val = state.x86_registers.get_register(src_reg)
            result = reg_val & src_val
            state.x86_registers.set_register(dest_reg, result)

        return state

    elif mnemonic == 'or':
        # OR：按位或
        if not operands['dest_reg']:
            raise ValueError(f"OR instruction must have register destination: {operands}")

        dest_reg = operands['dest_reg']
        reg_val = state.x86_registers.get_register(dest_reg)

        if operands['is_memory']:
            # OR reg, [base+offset]
            base_reg = operands['base_reg']
            offset = operands['offset']

            if base_reg not in [Register.R14, Register.R13]:
                raise ValueError(f"Unsupported base register for OR: {base_reg}")

            memory_offset = offset
            if 'index_reg' in operands and operands['index_reg']:
                index_reg = operands['index_reg']
                index_val = state.x86_registers.get_register(index_reg)
                if isinstance(offset, int):
                    offset_bv = BitVecVal(offset, 64)
                else:
                    offset_bv = offset
                memory_offset = offset_bv + index_val

            mem_val = state.x86_memory.load_64bit(memory_offset)
            result = reg_val | mem_val
            state.x86_registers.set_register(dest_reg, result)

        elif operands['src_reg']:
            # OR reg, reg
            src_reg = operands['src_reg']
            src_val = state.x86_registers.get_register(src_reg)
            result = reg_val | src_val
            state.x86_registers.set_register(dest_reg, result)

        return state

    elif mnemonic == 'xor':
        # XOR：按位异或
        if not operands['dest_reg']:
            raise ValueError(f"XOR instruction must have register destination: {operands}")

        dest_reg = operands['dest_reg']
        reg_val = state.x86_registers.get_register(dest_reg)

        if operands['is_memory']:
            # XOR reg, [base+offset]
            base_reg = operands['base_reg']
            offset = operands['offset']

            if base_reg not in [Register.R14, Register.R13]:
                raise ValueError(f"Unsupported base register for XOR: {base_reg}")

            memory_offset = offset
            if 'index_reg' in operands and operands['index_reg']:
                index_reg = operands['index_reg']
                index_val = state.x86_registers.get_register(index_reg)
                if isinstance(offset, int):
                    offset_bv = BitVecVal(offset, 64)
                else:
                    offset_bv = offset
                memory_offset = offset_bv + index_val

            mem_val = state.x86_memory.load_64bit(memory_offset)
            result = reg_val ^ mem_val
            state.x86_registers.set_register(dest_reg, result)

        elif operands['src_reg']:
            # XOR reg, reg
            src_reg = operands['src_reg']
            src_val = state.x86_registers.get_register(src_reg)
            result = reg_val ^ src_val
            state.x86_registers.set_register(dest_reg, result)

        return state

    elif mnemonic in ['jb', 'jae', 'jmp']:
        # 控制流指令 - 原样返回状态
        # 这些将在控制流级别处理
        return state

    else:
        # 未知指令 - 返回未更改的状态
        # TODO: 实现更多指令
        return state

