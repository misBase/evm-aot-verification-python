"""
x86-64指令语义建模。

本模块使用Z3为x86-64指令提供语义建模。
"""

import capstone
from z3 import BitVec, BitVecVal, Concat, Extract, If, ZeroExt, LShR, UDiv, URem, Not, And, Or
from typing import List, Dict, Optional, Any, Tuple
from .models import X86Block, X86Instruction, Register
from .aot_profile import GO_HPC_EVM_PROFILE
from .disassembler import disassemble_hex, parse_operands
from common.uint256 import Uint256
from state.smt_state import SMTState

# RETURN指令的常量
EVM_NATIVE_CALL_STATUS_CODE_RETURNED = GO_HPC_EVM_PROFILE.status_codes["returned"]
EVM_NATIVE_CALL_STATUS_CODE_REVERTED = GO_HPC_EVM_PROFILE.status_codes["reverted"]
EVM_NATIVE_CALL_STATUS_CODE_INVALID = GO_HPC_EVM_PROFILE.status_codes["invalid"]
EVM_CALL_ENGINE_EXIT_CONTEXT_NATIVE_CALL_STATUS_CODE_OFFSET = GO_HPC_EVM_PROFILE.offsets["status_code"]
EVM_CALL_ENGINE_STACK_CONTEXT_STACK_POINTER_OFFSET = GO_HPC_EVM_PROFILE.offsets["stack_pointer"]
AMD64_RESERVED_REGISTER_FOR_CALL_ENGINE = Register.R13  # 指向callEngine实例的指针


class X86SemanticsModel:
    """x86-64指令序列的语义建模。"""

    def execute_instruction_sequence(self,
                                    instructions: List[X86Instruction],
                                    initial_memory: Dict[int, BitVec],
                                    result_registers: Optional[List[Register]] = None) -> BitVec:
        """执行指令序列并提取结果。

        Args:
            instructions: 要执行的X86Instruction对象列表
            initial_memory: 初始内存状态（将偏移量映射到BitVec值的字典，key为Python int）
            result_registers: 要从中提取结果的寄存器列表（从高到低顺序）。
                            如果为None，默认为[RBX, RDX, RCX, RAX]。

        Returns:
            表示256位结果的逻辑公式，作为BitVec
        """
        state = SMTState()
        # 设基址寄存器为0，使 [R14 + offset] 退化为 [offset]
        state.x86_registers.set_register(Register.R13, BitVecVal(0, 64))
        state.x86_registers.set_register(Register.R14, BitVecVal(0, 64))
        state.x86_registers.set_register(Register.R15, BitVecVal(0, 64))

        # 写入初始内存（Python int key 转为 BitVecVal(64) 以支持负偏移的补码地址）
        for offset, val in initial_memory.items():
            addr = BitVecVal(offset, 64)
            state.x86_memory = state.x86_memory.store_limb(addr, val)

        for insn in instructions:
            state = insn.to_z3(state)

        if result_registers is None:
            result_registers = [Register.RBX, Register.RDX, Register.RCX, Register.RAX]

        reg_values = [state.x86_registers.get_register(reg) for reg in result_registers]
        return Concat(*reg_values)
    
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
        if len(block.instructions) > 0:
            result = self.execute_instruction_sequence(
                block.instructions,
                mem_vars,
                result_registers=result_registers
            )
            return {
                'output_memory': {},
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
    if mnemonic == 'movabs':
        # MOVABS 与 MOV reg, imm64 语义一致
        mnemonic = 'mov'
    operands = parse_operands(insn)

    def _to_bv64(value):
        if isinstance(value, int):
            return BitVecVal(value, 64)
        if value.size() == 64:
            return value
        raise ValueError(f"Expected 64-bit value, got {value.size()} bits")

    def _bool_to_bv1(cond):
        return If(cond, BitVecVal(1, 1), BitVecVal(0, 1))

    def _effective_address() -> BitVec:
        base_reg = operands.get('base_reg')
        offset = _to_bv64(operands.get('offset', 0))
        rip_relative = False
        cs_insn = insn._cs_insn
        if cs_insn is not None and hasattr(cs_insn, 'operands'):
            for op in cs_insn.operands:
                if op.type == capstone.x86.X86_OP_MEM and op.mem.base == capstone.x86.X86_REG_RIP:
                    rip_relative = True
                    break

        if rip_relative:
            addr = BitVecVal(insn.addr + insn.size, 64) + offset
        else:
            addr = offset if base_reg is None else state.x86_registers.get_register(base_reg) + offset

        index_reg = operands.get('index_reg')
        if index_reg is not None:
            scale = operands.get('scale', 1) or 1
            index_val = state.x86_registers.get_register(index_reg)
            if scale != 1:
                index_val = index_val * BitVecVal(scale, 64)
            addr = addr + index_val
        return addr

    def _update_logic_flags(result64):
        state.x86_registers.set_flag('CF', BitVecVal(0, 1))
        state.x86_registers.set_flag('OF', BitVecVal(0, 1))
        state.x86_registers.set_flag('ZF', _bool_to_bv1(result64 == BitVecVal(0, 64)))
        state.x86_registers.set_flag('SF', Extract(63, 63, result64))

    def _update_add_like_flags(lhs64, rhs64, result64, carry_out):
        # OF = MSB((lhs XOR result) AND (rhs XOR result))
        overflow = Extract(63, 63, (lhs64 ^ result64) & (rhs64 ^ result64))
        state.x86_registers.set_flag('CF', carry_out)
        state.x86_registers.set_flag('OF', overflow)
        state.x86_registers.set_flag('ZF', _bool_to_bv1(result64 == BitVecVal(0, 64)))
        state.x86_registers.set_flag('SF', Extract(63, 63, result64))

    def _update_sub_like_flags(lhs64, rhs64, result64):
        # CF 表示无符号借位，使用65位扩展提取
        lhs_ext = Concat(BitVecVal(0, 1), lhs64)
        rhs_ext = Concat(BitVecVal(0, 1), rhs64)
        borrow = Extract(64, 64, lhs_ext - rhs_ext)
        # OF = MSB((lhs XOR rhs) AND (lhs XOR result))
        overflow = Extract(63, 63, (lhs64 ^ rhs64) & (lhs64 ^ result64))
        state.x86_registers.set_flag('CF', borrow)
        state.x86_registers.set_flag('OF', overflow)
        state.x86_registers.set_flag('ZF', _bool_to_bv1(result64 == BitVecVal(0, 64)))
        state.x86_registers.set_flag('SF', Extract(63, 63, result64))

    def _update_inc_like_flags(lhs64, result64):
        # INC 不修改 CF，只更新 OF/ZF/SF（AF/PF 当前未建模）
        one64 = BitVecVal(1, 64)
        overflow = Extract(63, 63, (lhs64 ^ result64) & (one64 ^ result64))
        state.x86_registers.set_flag('OF', overflow)
        state.x86_registers.set_flag('ZF', _bool_to_bv1(result64 == BitVecVal(0, 64)))
        state.x86_registers.set_flag('SF', Extract(63, 63, result64))

    def _update_sbb_flags(lhs64, rhs64, carry_in, result64):
        # SBB: lhs - rhs - CF，CF 表示借位
        lhs_ext = Concat(BitVecVal(0, 1), lhs64)
        rhs_ext = Concat(BitVecVal(0, 1), rhs64)
        carry_ext = Concat(BitVecVal(0, 64), carry_in)
        diff_ext = lhs_ext - rhs_ext - carry_ext
        borrow = Extract(64, 64, diff_ext)

        rhs_with_carry = rhs64 + ZeroExt(63, carry_in)
        overflow = Extract(63, 63, (lhs64 ^ rhs_with_carry) & (lhs64 ^ result64))

        state.x86_registers.set_flag('CF', borrow)
        state.x86_registers.set_flag('OF', overflow)
        state.x86_registers.set_flag('ZF', _bool_to_bv1(result64 == BitVecVal(0, 64)))
        state.x86_registers.set_flag('SF', Extract(63, 63, result64))

    def _load_memory_by_size(addr64, size_bytes: Optional[int]):
        if size_bytes == 1:
            return ZeroExt(56, state.x86_memory.load_byte(addr64))
        if size_bytes == 2:
            b0 = state.x86_memory.load_byte(addr64)
            b1 = state.x86_memory.load_byte(addr64 + BitVecVal(1, 64))
            return ZeroExt(48, Concat(b1, b0))
        if size_bytes == 4:
            b0 = state.x86_memory.load_byte(addr64)
            b1 = state.x86_memory.load_byte(addr64 + BitVecVal(1, 64))
            b2 = state.x86_memory.load_byte(addr64 + BitVecVal(2, 64))
            b3 = state.x86_memory.load_byte(addr64 + BitVecVal(3, 64))
            return ZeroExt(32, Concat(b3, b2, b1, b0))
        return state.x86_memory.load_limb(addr64)

    def _store_memory_by_size(addr64, size_bytes: Optional[int], value64):
        if size_bytes == 1:
            return state.x86_memory.store_byte(addr64, Extract(7, 0, value64))
        if size_bytes == 2:
            mem = state.x86_memory
            mem = mem.store_byte(addr64, Extract(7, 0, value64))
            mem = mem.store_byte(addr64 + BitVecVal(1, 64), Extract(15, 8, value64))
            return mem
        if size_bytes == 4:
            mem = state.x86_memory
            mem = mem.store_byte(addr64, Extract(7, 0, value64))
            mem = mem.store_byte(addr64 + BitVecVal(1, 64), Extract(15, 8, value64))
            mem = mem.store_byte(addr64 + BitVecVal(2, 64), Extract(23, 16, value64))
            mem = mem.store_byte(addr64 + BitVecVal(3, 64), Extract(31, 24, value64))
            return mem
        return state.x86_memory.store_limb(addr64, value64)

    def _read_register_by_size(reg, size_bytes: Optional[int]):
        value64 = state.x86_registers.get_register(reg)
        if size_bytes == 1:
            return ZeroExt(56, Extract(7, 0, value64))
        if size_bytes == 2:
            return ZeroExt(48, Extract(15, 0, value64))
        if size_bytes == 4:
            return ZeroExt(32, Extract(31, 0, value64))
        return value64

    def _write_register_by_size(reg, value64, size_bytes: Optional[int]):
        old_val = state.x86_registers.get_register(reg)
        if size_bytes == 1:
            new_val = Concat(Extract(63, 8, old_val), Extract(7, 0, value64))
        elif size_bytes == 2:
            new_val = Concat(Extract(63, 16, old_val), Extract(15, 0, value64))
        elif size_bytes == 4:
            new_val = ZeroExt(32, Extract(31, 0, value64))
        else:
            new_val = value64
        state.x86_registers.set_register(reg, new_val)

    def _sign_extend_int(value: int, bits: int) -> int:
        mask = (1 << bits) - 1
        value &= mask
        sign_bit = 1 << (bits - 1)
        if value & sign_bit:
            return value - (1 << bits)
        return value

    def _imm_to_bv64(target_size_bytes: Optional[int]) -> BitVec:
        immediate = operands['immediate']
        imm_size = operands.get('immediate_size')

        if target_size_bytes == 1:
            return BitVecVal(immediate & 0xFF, 64)
        if target_size_bytes == 4:
            return ZeroExt(32, BitVecVal(immediate & 0xFFFFFFFF, 32))

        if imm_size in (1, 4):
            signed_imm = _sign_extend_int(immediate, imm_size * 8)
            return BitVecVal(signed_imm, 64)
        return BitVecVal(immediate, 64)

    def _shift_count_64() -> BitVec:
        if operands['immediate'] is not None:
            return BitVecVal(operands['immediate'] & 0x3F, 64)
        if operands['src_reg']:
            src_val = _read_register_by_size(operands['src_reg'], operands.get('src_size'))
            return ZeroExt(58, Extract(5, 0, src_val))
        return BitVecVal(0, 64)

    def _set_shift_flags(lhs64, result64, count64, is_left: bool):
        old_cf = state.x86_registers.get_flag('CF')
        old_of = state.x86_registers.get_flag('OF')
        count_is_zero = count64 == BitVecVal(0, 64)
        count_is_one = count64 == BitVecVal(1, 64)

        if is_left:
            cf_candidate = Extract(0, 0, LShR(lhs64, BitVecVal(64, 64) - count64))
            of_candidate = Extract(63, 63, result64) ^ cf_candidate
        else:
            cf_candidate = Extract(0, 0, LShR(lhs64, count64 - BitVecVal(1, 64)))
            of_candidate = Extract(63, 63, lhs64)

        new_cf = If(count_is_zero, old_cf, cf_candidate)
        new_of = If(count_is_zero, old_of, If(count_is_one, of_candidate, old_of))
        new_zf = If(count_is_zero, state.x86_registers.get_flag('ZF'),
                    _bool_to_bv1(result64 == BitVecVal(0, 64)))
        new_sf = If(count_is_zero, state.x86_registers.get_flag('SF'),
                    Extract(63, 63, result64))

        state.x86_registers.set_flag('CF', new_cf)
        state.x86_registers.set_flag('OF', new_of)
        state.x86_registers.set_flag('ZF', new_zf)
        state.x86_registers.set_flag('SF', new_sf)

    def _bswap64(value64):
        return Concat(
            Extract(7, 0, value64),
            Extract(15, 8, value64),
            Extract(23, 16, value64),
            Extract(31, 24, value64),
            Extract(39, 32, value64),
            Extract(47, 40, value64),
            Extract(55, 48, value64),
            Extract(63, 56, value64),
        )

    def _setcc_condition(setcc_mnemonic: str):
        cf = state.x86_registers.get_flag('CF') == BitVecVal(1, 1)
        zf = state.x86_registers.get_flag('ZF') == BitVecVal(1, 1)
        sf = state.x86_registers.get_flag('SF') == BitVecVal(1, 1)
        of = state.x86_registers.get_flag('OF') == BitVecVal(1, 1)
        pf = state.x86_registers.get_flag('PF') == BitVecVal(1, 1)
        sf_eq_of = sf == of
        sf_ne_of = sf != of

        conditions = {
            'seta': And(Not(cf), Not(zf)),
            'setnbe': And(Not(cf), Not(zf)),
            'setae': Not(cf),
            'setnb': Not(cf),
            'setnc': Not(cf),
            'setb': cf,
            'setc': cf,
            'setbe': Or(cf, zf),
            'setna': Or(cf, zf),
            'sete': zf,
            'setz': zf,
            'setne': Not(zf),
            'setnz': Not(zf),
            'setg': And(Not(zf), sf_eq_of),
            'setnle': And(Not(zf), sf_eq_of),
            'setge': sf_eq_of,
            'setnl': sf_eq_of,
            'setl': sf_ne_of,
            'setnge': sf_ne_of,
            'setle': Or(zf, sf_ne_of),
            'setng': Or(zf, sf_ne_of),
            'sets': sf,
            'setns': Not(sf),
            'seto': of,
            'setno': Not(of),
            'setp': pf,
            'setpe': pf,
            'setnp': Not(pf),
            'setpo': Not(pf),
        }

        cond = conditions.get(setcc_mnemonic)
        if cond is None:
            raise ValueError(f"Unsupported SETcc instruction: {setcc_mnemonic}")
        return cond
    
    if mnemonic == 'mov':
        # MOV：将值从源移动到目标
        if operands['is_memory'] and operands['dest_reg']:
            # MOV reg, [base+offset]
            dest_reg = operands['dest_reg']
            dest_size = operands.get('dest_size')
            memory_size = operands.get('memory_size')
            memory_offset = _effective_address()
            mem_val = _load_memory_by_size(memory_offset, memory_size)
            _write_register_by_size(dest_reg, mem_val, dest_size)
        
        elif operands['is_memory'] and operands['src_reg']:
            # MOV [base+offset], reg
            src_reg = operands['src_reg']
            src_size = operands.get('src_size')
            memory_size = operands.get('memory_size')
            memory_offset = _effective_address()

            reg_val = _read_register_by_size(src_reg, src_size)
            new_memory_state = _store_memory_by_size(memory_offset, memory_size, reg_val)
            state.x86_memory = new_memory_state
        
        elif operands['dest_reg'] and operands['src_reg']:
            # MOV reg1, reg2
            dest_reg = operands['dest_reg']
            dest_size = operands.get('dest_size')
            src_reg = operands['src_reg']
            src_size = operands.get('src_size')
            src_val = _read_register_by_size(src_reg, src_size)
            _write_register_by_size(dest_reg, src_val, dest_size)
        
        elif operands['dest_reg'] and operands['immediate'] is not None:
            # MOV reg, immediate
            dest_reg = operands['dest_reg']
            dest_size = operands.get('dest_size')
            imm_val = _imm_to_bv64(dest_size)
            _write_register_by_size(dest_reg, imm_val, dest_size)
        
        elif operands['is_memory'] and operands['immediate'] is not None:
            # MOV [base+offset], immediate
            memory_size = operands.get('memory_size')
            memory_offset = _effective_address()
            imm_val = _imm_to_bv64(memory_size)
            state.x86_memory = _store_memory_by_size(memory_offset, memory_size, imm_val)
        
        return state

    elif mnemonic == 'movzx':
        # MOVZX：零扩展移动
        if not operands['dest_reg']:
            raise ValueError(f"MOVZX instruction must have register destination: {operands}")

        dest_reg = operands['dest_reg']
        dest_size = operands.get('dest_size')

        if operands['is_memory']:
            src_val = _load_memory_by_size(_effective_address(), operands.get('memory_size'))
        elif operands['src_reg']:
            src_val = _read_register_by_size(operands['src_reg'], operands.get('src_size'))
        else:
            raise ValueError(f"Unsupported MOVZX operand combination: {operands}")

        _write_register_by_size(dest_reg, src_val, dest_size)
        return state

    elif mnemonic == 'lea':
        # LEA：只计算有效地址，不访问内存且不修改标志位
        if not operands['dest_reg'] or not operands['is_memory']:
            raise ValueError(f"Unsupported LEA operand combination: {operands}")

        dest_reg = operands['dest_reg']
        dest_size = operands.get('dest_size')
        effective_addr = _effective_address()
        _write_register_by_size(dest_reg, effective_addr, dest_size)
        return state
    
    elif mnemonic == 'add':
        # ADD：将源加到目标，设置进位标志
        if operands['is_memory'] and not operands['dest_reg']:
            # ADD [base+offset], reg/imm
            memory_offset = _effective_address()
            memory_size = operands.get('memory_size')
            lhs_val = _load_memory_by_size(memory_offset, memory_size)

            if operands['src_reg']:
                rhs_val = _read_register_by_size(operands['src_reg'], operands.get('src_size'))
            elif operands['immediate'] is not None:
                rhs_val = _imm_to_bv64(memory_size)
            else:
                raise ValueError(f"Unsupported ADD operand combination: {operands}")

            lhs_ext = Concat(BitVecVal(0, 1), lhs_val)
            rhs_ext = Concat(BitVecVal(0, 1), rhs_val)
            sum_ext = lhs_ext + rhs_ext

            result = Extract(63, 0, sum_ext)
            carry_out = Extract(64, 64, sum_ext)

            state.x86_memory = _store_memory_by_size(memory_offset, memory_size, result)
            _update_add_like_flags(lhs_val, rhs_val, result, carry_out)
            return state

        if not operands['dest_reg']:
            raise ValueError(f"ADD instruction must have register destination: {operands}")

        dest_reg = operands['dest_reg']
        dest_size = operands.get('dest_size')
        reg_val = _read_register_by_size(dest_reg, dest_size)
        
        if operands['is_memory']:
            # ADD reg, [base+offset]
            memory_offset = _effective_address()
            mem_val = _load_memory_by_size(memory_offset, operands.get('memory_size'))

            # 执行加法（64位，带进位生成）
            reg_ext = Concat(BitVecVal(0, 1), reg_val)
            mem_ext = Concat(BitVecVal(0, 1), mem_val)
            sum_ext = reg_ext + mem_ext

            # 提取结果和进位
            result = Extract(63, 0, sum_ext)
            carry_out = Extract(64, 64, sum_ext)

            # 更新寄存器和标志
            _write_register_by_size(dest_reg, result, dest_size)
            _update_add_like_flags(reg_val, mem_val, result, carry_out)
        
        elif operands['src_reg']:
            # ADD reg, reg
            src_reg = operands['src_reg']
            src_val = _read_register_by_size(src_reg, operands.get('src_size'))
            
            # 执行加法
            reg_ext = Concat(BitVecVal(0, 1), reg_val)
            src_ext = Concat(BitVecVal(0, 1), src_val)
            sum_ext = reg_ext + src_ext
            
            result = Extract(63, 0, sum_ext)
            carry_out = Extract(64, 64, sum_ext)
            
            _write_register_by_size(dest_reg, result, dest_size)
            _update_add_like_flags(reg_val, src_val, result, carry_out)

        elif operands['immediate'] is not None:
            # ADD reg, immediate
            imm_val = _imm_to_bv64(dest_size)
            reg_ext = Concat(BitVecVal(0, 1), reg_val)
            imm_ext = Concat(BitVecVal(0, 1), imm_val)
            sum_ext = reg_ext + imm_ext

            result = Extract(63, 0, sum_ext)
            carry_out = Extract(64, 64, sum_ext)

            _write_register_by_size(dest_reg, result, dest_size)
            _update_add_like_flags(reg_val, imm_val, result, carry_out)
        
        return state
    
    elif mnemonic == 'adc':
        # ADC：带进位加法
        if not operands['dest_reg']:
            raise ValueError(f"ADC instruction must have register destination: {operands}")
        
        dest_reg = operands['dest_reg']
        dest_size = operands.get('dest_size')
        reg_val = _read_register_by_size(dest_reg, dest_size)
        carry_in = state.x86_registers.get_flag('CF')

        if operands['is_memory']:
            rhs_val = _load_memory_by_size(_effective_address(), operands.get('memory_size'))
        elif operands['src_reg']:
            rhs_val = _read_register_by_size(operands['src_reg'], operands.get('src_size'))
        elif operands['immediate'] is not None:
            rhs_val = _imm_to_bv64(dest_size)
        else:
            raise ValueError(f"Unsupported ADC operand combination: {operands}")

        addend = rhs_val + ZeroExt(63, carry_in)
        
        # 执行带进位加法
        reg_ext = Concat(BitVecVal(0, 1), reg_val)
        rhs_ext = Concat(BitVecVal(0, 1), rhs_val)
        carry_ext = Concat(BitVecVal(0, 64), carry_in)
        sum_ext = reg_ext + rhs_ext + carry_ext
        
        result = Extract(63, 0, sum_ext)
        carry_out = Extract(64, 64, sum_ext)
        
        _write_register_by_size(dest_reg, result, dest_size)
        _update_add_like_flags(reg_val, addend, result, carry_out)
        
        return state

    elif mnemonic == 'sbb':
        # SBB：带借位减法
        if not operands['dest_reg']:
            raise ValueError(f"SBB instruction must have register destination: {operands}")

        dest_reg = operands['dest_reg']
        dest_size = operands.get('dest_size')
        lhs = _read_register_by_size(dest_reg, dest_size)
        carry_in = state.x86_registers.get_flag('CF')

        if operands['is_memory']:
            rhs = _load_memory_by_size(_effective_address(), operands.get('memory_size'))
        elif operands['src_reg']:
            rhs = _read_register_by_size(operands['src_reg'], operands.get('src_size'))
        elif operands['immediate'] is not None:
            rhs = _imm_to_bv64(dest_size)
        else:
            raise ValueError(f"Unsupported SBB operand combination: {operands}")

        result = lhs - rhs - ZeroExt(63, carry_in)
        _write_register_by_size(dest_reg, result, dest_size)
        _update_sbb_flags(lhs, rhs, carry_in, result)
        return state
    
    elif mnemonic == 'sub':
        # SUB：从目标减去源
        if not operands['dest_reg']:
            raise ValueError(f"SUB instruction must have register destination: {operands}")

        dest_reg = operands['dest_reg']
        dest_size = operands.get('dest_size')
        reg_val = _read_register_by_size(dest_reg, dest_size)

        if operands['is_memory']:
            rhs_val = _load_memory_by_size(_effective_address(), operands.get('memory_size'))
        elif operands['src_reg']:
            rhs_val = _read_register_by_size(operands['src_reg'], operands.get('src_size'))
        elif operands['immediate'] is not None:
            rhs_val = _imm_to_bv64(dest_size)
        else:
            raise ValueError(f"Unsupported SUB operand combination: {operands}")

        result = reg_val - rhs_val
        _write_register_by_size(dest_reg, result, dest_size)
        _update_sub_like_flags(reg_val, rhs_val, result)

        return state

    elif mnemonic == 'inc':
        # INC：目标 + 1，不修改 CF
        if not operands['dest_reg']:
            raise ValueError(f"INC instruction must have register destination: {operands}")

        dest_reg = operands['dest_reg']
        dest_size = operands.get('dest_size')
        reg_val = _read_register_by_size(dest_reg, dest_size)

        result = reg_val + BitVecVal(1, 64)
        _write_register_by_size(dest_reg, result, dest_size)
        _update_inc_like_flags(reg_val, result)
        return state
    
    elif mnemonic == 'cmp':
        # CMP：比较并设置标志（不修改操作数）
        if not operands['dest_reg']:
            raise ValueError(f"CMP instruction must have register operand: {operands}")
        
        dest_reg = operands['dest_reg']
        dest_size = operands.get('dest_size')
        reg_val = _read_register_by_size(dest_reg, dest_size)
        
        if operands['is_memory']:
            rhs_val = _load_memory_by_size(_effective_address(), operands.get('memory_size'))
        elif operands['src_reg']:
            rhs_val = _read_register_by_size(operands['src_reg'], operands.get('src_size'))
        elif operands['immediate'] is not None:
            rhs_val = _imm_to_bv64(dest_size)
        else:
            raise ValueError(f"Unsupported CMP operand combination: {operands}")

        result = reg_val - rhs_val
        _update_sub_like_flags(reg_val, rhs_val, result)
        
        return state

    elif mnemonic == 'test':
        # TEST：按位与并设置标志（不修改操作数）
        if not operands['dest_reg']:
            raise ValueError(f"TEST instruction must have register operand: {operands}")

        lhs = _read_register_by_size(operands['dest_reg'], operands.get('dest_size'))
        if operands['src_reg']:
            rhs = _read_register_by_size(operands['src_reg'], operands.get('src_size'))
        elif operands['immediate'] is not None:
            rhs = _imm_to_bv64(operands.get('dest_size'))
        elif operands['is_memory']:
            rhs = _load_memory_by_size(_effective_address(), operands.get('memory_size'))
        else:
            raise ValueError(f"Unsupported TEST operand combination: {operands}")

        _update_logic_flags(lhs & rhs)
        return state
    
    elif mnemonic == 'ret':
        # RET 指令：检查退出状态码，并在需要时提取返回/回退数据
        # 从x86内存读取状态码：[R13 + evmCallEngineExitContextNativeCallStatusCodeOffset]
        
        # 获取R13寄存器值（callEngine指针）
        r13_value = state.x86_registers.get_register(AMD64_RESERVED_REGISTER_FOR_CALL_ENGINE)
        
        # 计算状态码内存地址
        status_code_offset = BitVecVal(EVM_CALL_ENGINE_EXIT_CONTEXT_NATIVE_CALL_STATUS_CODE_OFFSET, 64)
        status_code_addr = r13_value + status_code_offset
        
        # 从x86内存读取状态码（8位字节）
        status_code = state.x86_memory.load_byte(status_code_addr)
        
        # RETURNED / REVERTED 都会从栈中读取 offset、size。
        # INVALID 只会弹出一个 opcode，当前模型不单独暴露该错误值。
        status_code_is_returned = (status_code == BitVecVal(EVM_NATIVE_CALL_STATUS_CODE_RETURNED, 8))
        status_code_is_reverted = (status_code == BitVecVal(EVM_NATIVE_CALL_STATUS_CODE_REVERTED, 8))
        status_code_has_return_data = Or(status_code_is_returned, status_code_is_reverted)
        status_code_is_invalid = (status_code == BitVecVal(EVM_NATIVE_CALL_STATUS_CODE_INVALID, 8))
        
        # 重要：x86-64不直接操作 evm_stack 或 evm_memory。
        # 这里需要从 x86 栈内存中提取栈顶参数。
        # Go 代码：
        # - RETURNED / REVERTED: offset, size := c.PopUint64(), c.PopUint64()
        # - INVALID: op := c.PopUint64()
        # 因此逻辑栈顶 stack[0] 是 offset/opcode，stack[1] 是 size（若存在）。
        #
        # 这里的 R14 是当前 block 的栈基准，不是整个物理栈起点。
        # 栈顶位置由当前 stack_pointer 决定：
        # stack[0] 基址 = R14 + (sp-4)*8，
        # stack[1] 基址 = R14 + (sp-8)*8。

        # 获取R14寄存器值（栈基址指针）
        r14_value = state.x86_registers.get_register(Register.R14)

        # 读取当前 stack_pointer（单位：limb）
        sp_offset = BitVecVal(EVM_CALL_ENGINE_STACK_CONTEXT_STACK_POINTER_OFFSET, 64)
        sp_bv = state.x86_memory.load_64bit(r13_value + sp_offset)

        # 使用当前 sp 反推出逻辑栈顶两项的物理地址
        limb_size = BitVecVal(8, 64)
        stack0_base = r14_value + (sp_bv - BitVecVal(4, 64)) * limb_size
        offset_z0 = state.x86_memory.load_64bit(stack0_base)
        offset_z1 = state.x86_memory.load_64bit(stack0_base + BitVecVal(8, 64))
        offset_z2 = state.x86_memory.load_64bit(stack0_base + BitVecVal(16, 64))
        offset_z3 = state.x86_memory.load_64bit(stack0_base + BitVecVal(24, 64))
        offset_stack_value = Concat(offset_z3, offset_z2, offset_z1, offset_z0)  # 256位值

        stack1_base = r14_value + (sp_bv - BitVecVal(8, 64)) * limb_size
        size_z0 = state.x86_memory.load_64bit(stack1_base)
        size_z1 = state.x86_memory.load_64bit(stack1_base + BitVecVal(8, 64))
        size_z2 = state.x86_memory.load_64bit(stack1_base + BitVecVal(16, 64))
        size_z3 = state.x86_memory.load_64bit(stack1_base + BitVecVal(24, 64))
        size_stack_value = Concat(size_z3, size_z2, size_z1, size_z0)  # 256位值
        
        # 将256位栈值截断为64位，模拟 Go 的 PopUint64()
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
        
        # 对 return_offset / return_length 使用条件符号值：
        # - RETURNED / REVERTED：设置为栈中的 offset、size
        # - 其他状态：保持为 0
        # 不同的状态码有不同的行为（来自Go代码）：
        # - RETURNED（0）：返回数据（offset, size）
        # - REVERTED（1）：返回回退数据（offset, size）
        # - STOPPED：返回nil, nil（无返回数据）
        # - INVALID：返回错误；当前模型只保留“无返回数据”这一可观察效果
        zero_64 = BitVecVal(0, 64)

        # INVALID 会消费栈顶 opcode，但当前状态模型没有单独的错误对象；
        # 这里保留“无返回数据”的外部可观察语义。
        _invalid_opcode = If(status_code_is_invalid, offset_bv, zero_64)

        state.return_offset = If(status_code_has_return_data, offset_bv, zero_64)
        state.return_length = If(status_code_has_return_data, length_bv, zero_64)
        
        return state

    elif mnemonic == 'mul':
        # MUL：无符号乘法（RDX:RAX = RAX * op）
        if operands['is_memory']:
            op_val = _load_memory_by_size(_effective_address(), operands.get('memory_size'))
        elif operands['dest_reg']:
            op_val = _read_register_by_size(operands['dest_reg'], operands.get('dest_size'))
        else:
            raise ValueError(f"MUL instruction must have memory/register operand: {operands}")

        rax_val = state.x86_registers.get_register(Register.RAX)
        product = ZeroExt(64, rax_val) * ZeroExt(64, op_val)
        result_low = Extract(63, 0, product)
        result_high = Extract(127, 64, product)

        state.x86_registers.set_register(Register.RAX, result_low)
        state.x86_registers.set_register(Register.RDX, result_high)

        # 对 MUL，CF/OF 在高64位非零时置1，否则置0
        high_is_non_zero = result_high != BitVecVal(0, 64)
        cf_of = _bool_to_bv1(high_is_non_zero)
        state.x86_registers.set_flag('CF', cf_of)
        state.x86_registers.set_flag('OF', cf_of)
        return state

    elif mnemonic == 'div':
        # DIV：无符号除法（RDX:RAX / op -> quotient in RAX, remainder in RDX）
        if operands['is_memory']:
            divisor = _load_memory_by_size(_effective_address(), operands.get('memory_size'))
        elif operands['dest_reg']:
            divisor = _read_register_by_size(operands['dest_reg'], operands.get('dest_size'))
        else:
            raise ValueError(f"DIV instruction must have memory/register operand: {operands}")

        old_rax = state.x86_registers.get_register(Register.RAX)
        old_rdx = state.x86_registers.get_register(Register.RDX)
        dividend = Concat(old_rdx, old_rax)
        divisor128 = ZeroExt(64, divisor)
        q128 = UDiv(dividend, divisor128)
        r128 = URem(dividend, divisor128)

        quotient_fits = Extract(127, 64, q128) == BitVecVal(0, 64)
        divisor_non_zero = divisor != BitVecVal(0, 64)
        can_divide = divisor_non_zero & quotient_fits

        new_rax = If(can_divide, Extract(63, 0, q128), old_rax)
        new_rdx = If(can_divide, Extract(63, 0, r128), old_rdx)
        state.x86_registers.set_register(Register.RAX, new_rax)
        state.x86_registers.set_register(Register.RDX, new_rdx)
        return state

    elif mnemonic == 'and':
        # AND：按位与
        if not operands['dest_reg']:
            raise ValueError(f"AND instruction must have register destination: {operands}")

        dest_reg = operands['dest_reg']
        dest_size = operands.get('dest_size')
        reg_val = _read_register_by_size(dest_reg, dest_size)

        if operands['is_memory']:
            # AND reg, [base+offset]
            memory_offset = _effective_address()
            mem_val = _load_memory_by_size(memory_offset, operands.get('memory_size'))
            result = reg_val & mem_val
            _write_register_by_size(dest_reg, result, dest_size)

        elif operands['src_reg']:
            # AND reg, reg
            src_reg = operands['src_reg']
            src_val = _read_register_by_size(src_reg, operands.get('src_size'))
            result = reg_val & src_val
            _write_register_by_size(dest_reg, result, dest_size)

        elif operands['immediate'] is not None:
            result = reg_val & _imm_to_bv64(dest_size)
            _write_register_by_size(dest_reg, result, dest_size)

        _update_logic_flags(_read_register_by_size(dest_reg, dest_size))
        return state

    elif mnemonic == 'or':
        # OR：按位或
        if not operands['dest_reg']:
            raise ValueError(f"OR instruction must have register destination: {operands}")

        dest_reg = operands['dest_reg']
        dest_size = operands.get('dest_size')
        reg_val = _read_register_by_size(dest_reg, dest_size)

        if operands['is_memory']:
            # OR reg, [base+offset]
            memory_offset = _effective_address()
            mem_val = _load_memory_by_size(memory_offset, operands.get('memory_size'))
            result = reg_val | mem_val
            _write_register_by_size(dest_reg, result, dest_size)

        elif operands['src_reg']:
            # OR reg, reg
            src_reg = operands['src_reg']
            src_val = _read_register_by_size(src_reg, operands.get('src_size'))
            result = reg_val | src_val
            _write_register_by_size(dest_reg, result, dest_size)

        elif operands['immediate'] is not None:
            result = reg_val | _imm_to_bv64(dest_size)
            _write_register_by_size(dest_reg, result, dest_size)

        _update_logic_flags(_read_register_by_size(dest_reg, dest_size))
        return state

    elif mnemonic == 'xor':
        # XOR：按位异或
        if not operands['dest_reg']:
            raise ValueError(f"XOR instruction must have register destination: {operands}")

        dest_reg = operands['dest_reg']
        dest_size = operands.get('dest_size')
        reg_val = _read_register_by_size(dest_reg, dest_size)

        if operands['is_memory']:
            # XOR reg, [base+offset]
            memory_offset = _effective_address()
            mem_val = _load_memory_by_size(memory_offset, operands.get('memory_size'))
            result = reg_val ^ mem_val
            _write_register_by_size(dest_reg, result, dest_size)

        elif operands['src_reg']:
            # XOR reg, reg
            src_reg = operands['src_reg']
            src_val = _read_register_by_size(src_reg, operands.get('src_size'))
            result = reg_val ^ src_val
            _write_register_by_size(dest_reg, result, dest_size)

        elif operands['immediate'] is not None:
            result = reg_val ^ _imm_to_bv64(dest_size)
            _write_register_by_size(dest_reg, result, dest_size)

        _update_logic_flags(_read_register_by_size(dest_reg, dest_size))
        return state

    elif mnemonic == 'shl':
        # SHL：逻辑左移
        count64 = _shift_count_64()
        if operands['is_memory'] and not operands['dest_reg']:
            addr = _effective_address()
            mem_size = operands.get('memory_size')
            lhs = _load_memory_by_size(addr, mem_size)
            result = lhs << count64
            state.x86_memory = _store_memory_by_size(addr, mem_size, result)
            _set_shift_flags(lhs, result, count64, is_left=True)
            return state

        if not operands['dest_reg']:
            raise ValueError(f"SHL instruction must have destination operand: {operands}")

        dest_reg = operands['dest_reg']
        dest_size = operands.get('dest_size')
        lhs = _read_register_by_size(dest_reg, dest_size)
        result = lhs << count64
        _write_register_by_size(dest_reg, result, dest_size)
        _set_shift_flags(lhs, result, count64, is_left=True)
        return state

    elif mnemonic == 'shr':
        # SHR：逻辑右移
        count64 = _shift_count_64()
        if operands['is_memory'] and not operands['dest_reg']:
            addr = _effective_address()
            mem_size = operands.get('memory_size')
            lhs = _load_memory_by_size(addr, mem_size)
            result = LShR(lhs, count64)
            state.x86_memory = _store_memory_by_size(addr, mem_size, result)
            _set_shift_flags(lhs, result, count64, is_left=False)
            return state

        if not operands['dest_reg']:
            raise ValueError(f"SHR instruction must have destination operand: {operands}")

        dest_reg = operands['dest_reg']
        dest_size = operands.get('dest_size')
        lhs = _read_register_by_size(dest_reg, dest_size)
        result = LShR(lhs, count64)
        _write_register_by_size(dest_reg, result, dest_size)
        _set_shift_flags(lhs, result, count64, is_left=False)
        return state

    elif mnemonic == 'not':
        # NOT：按位取反，不影响标志位
        if operands['is_memory'] and not operands['dest_reg']:
            addr = _effective_address()
            mem_size = operands.get('memory_size')
            value = _load_memory_by_size(addr, mem_size)
            state.x86_memory = _store_memory_by_size(addr, mem_size, ~value)
            return state

        if not operands['dest_reg']:
            raise ValueError(f"NOT instruction must have destination operand: {operands}")

        dest_reg = operands['dest_reg']
        dest_size = operands.get('dest_size')
        value = _read_register_by_size(dest_reg, dest_size)
        _write_register_by_size(dest_reg, ~value, dest_size)
        return state

    elif mnemonic == 'bswap':
        # BSWAP：按字节反转寄存器
        if not operands['dest_reg']:
            raise ValueError(f"BSWAP instruction must have register operand: {operands}")

        dest_reg = operands['dest_reg']
        value = state.x86_registers.get_register(dest_reg)
        state.x86_registers.set_register(dest_reg, _bswap64(value))
        return state

    elif mnemonic.startswith('set'):
        # SETcc：根据标志位写入 0/1 到 8-bit 目的操作数，不修改标志位
        cond = _setcc_condition(mnemonic)
        value64 = ZeroExt(63, _bool_to_bv1(cond))

        if operands['is_memory'] and not operands['dest_reg']:
            addr = _effective_address()
            mem_size = operands.get('memory_size') or 1
            state.x86_memory = _store_memory_by_size(addr, mem_size, value64)
            return state

        if operands['dest_reg']:
            dest_size = operands.get('dest_size') or 1
            _write_register_by_size(operands['dest_reg'], value64, dest_size)
            return state

        raise ValueError(f"SETcc instruction must have register/memory destination: {operands}")

    elif mnemonic in ['jb', 'jae', 'ja', 'jbe', 'je', 'jne', 'jl', 'jle', 'jg', 'jge', 'jmp']:
        # 控制流指令 - 原样返回状态
        # 这些将在控制流级别处理
        return state
    elif mnemonic == 'nop':
        return state

    else:
        raise ValueError(f"Unsupported instruction in x86_instruction_to_z3: {mnemonic}")
