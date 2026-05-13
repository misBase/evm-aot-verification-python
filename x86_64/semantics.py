"""
x86-64指令语义建模。

本模块使用Z3为x86-64指令提供语义建模。
"""

import capstone
from z3 import BitVec, BitVecVal, Concat, Extract, If, ZeroExt, LShR, UDiv, URem, Not, And, Or, Select
from typing import List, Dict, Optional, Any, Tuple
from .models import X86Block, X86Instruction, Register
from .aot_profile import GO_HPC_EVM_PROFILE
from .disassembler import disassemble_hex, parse_operands
from common.uint256 import Uint256
from state.smt_state import SMTState, MemoryDomain, MemoryDomainError, PointerTag


def _classify_domain(base_reg) -> Optional[MemoryDomain]:
    """根据 base_reg 把内存访问路由到对应 Z3 Array。

    Go AOT ABI 规定：
    - R13 -> callEngine 结构体
    - R14 -> EVM 栈窗口
    - R15 -> EVM 256-bit memory

    其它寄存器或 None（含 RIP-relative、绝对地址）返回 None；
    `_load/_store_memory_by_size` 在 None 上会抛 MemoryDomainError。
    """
    if base_reg == Register.R13:
        return MemoryDomain.CALLENGINE
    if base_reg == Register.R14:
        return MemoryDomain.STACK
    if base_reg == Register.R15:
        return MemoryDomain.EVM
    return None


# RETURN指令的常量
_CALLENGINE_OFFSETS = GO_HPC_EVM_PROFILE.offsets

EVM_NATIVE_CALL_STATUS_CODE_RETURNED = GO_HPC_EVM_PROFILE.status_codes["returned"]
EVM_NATIVE_CALL_STATUS_CODE_REVERTED = GO_HPC_EVM_PROFILE.status_codes["reverted"]
EVM_NATIVE_CALL_STATUS_CODE_INVALID = GO_HPC_EVM_PROFILE.status_codes["invalid"]
EVM_CALL_ENGINE_EXIT_CONTEXT_NATIVE_CALL_STATUS_CODE_OFFSET = _CALLENGINE_OFFSETS["status_code"]
EVM_CALL_ENGINE_STACK_CONTEXT_STACK_POINTER_OFFSET = _CALLENGINE_OFFSETS["stack_pointer"]
AMD64_RESERVED_REGISTER_FOR_CALL_ENGINE = Register.R13  # 指向callEngine实例的指针

# 由 Go prologue `add r14, [r13+0x30]` 使用。
CALLENGINE_STACK_POINTER_BYTE_OFFSET = _CALLENGINE_OFFSETS["stack_byte_offset"]

# callEngine 字段 side-channel：识别到 mov [r13+offset], imm/reg 时同步到 SMTState 的显式字段。
# (offset, expected_size_bytes) -> side-channel attribute name
_CALLENGINE_FIELD_MAP = {
    (_CALLENGINE_OFFSETS["memory_base"],                    8): "callengine_memory_base",
    (_CALLENGINE_OFFSETS["memory_size"],                    8): "callengine_memory_size_bytes",
    (_CALLENGINE_OFFSETS["last_gas_cost"],                  8): "callengine_memory_gas_used",
    (_CALLENGINE_OFFSETS["stack_pointer"],                  8): "callengine_stack_pointer_limbs",
    (CALLENGINE_STACK_POINTER_BYTE_OFFSET,                  8): "callengine_stack_byte_offset",
    (_CALLENGINE_OFFSETS["stack_base"],                     8): "callengine_stack_base",
    (_CALLENGINE_OFFSETS["callvalue"],                      8): "callengine_callvalue",
    (_CALLENGINE_OFFSETS["gas_remaining"],                  8): "callengine_gas_remaining",
    (_CALLENGINE_OFFSETS["self_address_pointer"],           8): "callengine_self_address_pointer",
    (_CALLENGINE_OFFSETS["origin_address_pointer"],         8): "callengine_origin_address_pointer",
    (_CALLENGINE_OFFSETS["caller_address_pointer"],         8): "callengine_caller_address_pointer",
    (_CALLENGINE_OFFSETS["input_pointer"],                  8): "callengine_input_pointer",
    (_CALLENGINE_OFFSETS["input_size"],                     8): "callengine_input_size_bytes",
    (_CALLENGINE_OFFSETS["code_pointer"],                   8): "callengine_code_pointer",
    (_CALLENGINE_OFFSETS["code_size"],                      8): "callengine_code_size_bytes",
    (_CALLENGINE_OFFSETS["return_data_pointer"],            8): "callengine_return_data_pointer",
    (_CALLENGINE_OFFSETS["return_data_size"],               8): "callengine_return_data_size_bytes",
    (_CALLENGINE_OFFSETS["status_code"],                    1): "callengine_status_code",
    (_CALLENGINE_OFFSETS["builtin_function_index"],         4): "callengine_builtin_func_index",
    (_CALLENGINE_OFFSETS["go_function_index"],              4): "callengine_go_func_index",
    (_CALLENGINE_OFFSETS["return_address"],                 8): "callengine_return_address",
    (_CALLENGINE_OFFSETS["arch_grow_number"],               8): "callengine_builtin_arg0",
}

_POINTER_TAG_BY_CALLENGINE_OFFSET = {
    _CALLENGINE_OFFSETS["memory_base"]: PointerTag.EVM_PTR,
    _CALLENGINE_OFFSETS["stack_base"]: PointerTag.STACK_PTR,
    _CALLENGINE_OFFSETS["self_address_pointer"]: PointerTag.SELF_ADDRESS_PTR,
    _CALLENGINE_OFFSETS["origin_address_pointer"]: PointerTag.ORIGIN_ADDRESS_PTR,
    _CALLENGINE_OFFSETS["caller_address_pointer"]: PointerTag.CALLER_ADDRESS_PTR,
    _CALLENGINE_OFFSETS["input_pointer"]: PointerTag.CALLDATA_PTR,
    _CALLENGINE_OFFSETS["code_pointer"]: PointerTag.CODE_PTR,
    _CALLENGINE_OFFSETS["return_data_pointer"]: PointerTag.RETURNDATA_PTR,
}

_READONLY_SOURCE_ATTRS = {
    PointerTag.CALLDATA_PTR: ("callengine_input_pointer", "calldata"),
    PointerTag.CODE_PTR: ("callengine_code_pointer", "code"),
    PointerTag.RETURNDATA_PTR: ("callengine_return_data_pointer", "return_data"),
}

_ADDRESS_SOURCE_ATTRS = {
    PointerTag.SELF_ADDRESS_PTR: ("callengine_self_address_pointer", "self_address"),
    PointerTag.ORIGIN_ADDRESS_PTR: ("callengine_origin_address_pointer", "origin_address"),
    PointerTag.CALLER_ADDRESS_PTR: ("callengine_caller_address_pointer", "caller_address"),
}

_READONLY_POINTER_TAGS = frozenset(_READONLY_SOURCE_ATTRS) | frozenset(_ADDRESS_SOURCE_ATTRS)

_WRITABLE_DOMAIN_BY_POINTER_TAG = {
    PointerTag.EVM_PTR: MemoryDomain.EVM,
    PointerTag.STACK_PTR: MemoryDomain.STACK,
}


def _maybe_update_callengine_field(state: SMTState, operands: dict, size_bytes: Optional[int],
                                   value64: "BitVec") -> None:
    """识别写入 [r13+KNOWN_OFFSET] 的指令，若命中则同步更新 SMTState 上的
    callEngine side-channel 字段。

    保留对 x86_memory 的 Store（由调用点自己做），此函数只写显式字段。
    适用于任何写内存的指令（mov/add/or/xor/shl/shr/not/setcc 等）。

    识别条件：base_reg == R13、无 index、offset 是 Python int、(offset, size) 命中表。
    """
    if operands.get('base_reg') != Register.R13:
        return
    if operands.get('index_reg') is not None:
        return
    off = operands.get('offset')
    if not isinstance(off, int):
        return
    key = (off, size_bytes)
    attr = _CALLENGINE_FIELD_MAP.get(key)
    if attr is None:
        return
    # 根据 size 取合适宽度的 slice
    if size_bytes == 1:
        setattr(state, attr, Extract(7, 0, value64))
    elif size_bytes == 4:
        setattr(state, attr, Extract(31, 0, value64))
    else:
        # 8 字节：value64 已经是 64-bit
        setattr(state, attr, value64)


def _maybe_read_callengine_field(state: SMTState, operands: dict,
                                 size_bytes: Optional[int]) -> Optional["BitVec"]:
    """识别读取 [r13+KNOWN_OFFSET] 的指令，若命中则直接走 side-channel 快路径。"""
    if operands.get('base_reg') != Register.R13:
        return None
    if operands.get('index_reg') is not None:
        return None
    off = operands.get('offset')
    if not isinstance(off, int):
        return None
    attr = _CALLENGINE_FIELD_MAP.get((off, size_bytes))
    if attr is None:
        return None

    value = getattr(state, attr)
    if size_bytes == 1:
        return ZeroExt(56, value)
    if size_bytes == 4:
        return ZeroExt(32, value)
    return value


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
        # ALU 单测桩约定：未路由的访存（base_reg ∉ {R13,R14,R15}，例如 [rax]）
        # 兜底到 stack 域，避免重写大量现有指令测试。
        state.unrouted_memory_domain = MemoryDomain.STACK

        # 写入初始内存（Python int key 转为 BitVecVal(64) 以支持负偏移的补码地址）
        # 测试桩约定：R13=R14=R15=0 时所有访存都按 STACK 域路由（被测指令必须用 [R14+offset] 形式）。
        for offset, val in initial_memory.items():
            addr = BitVecVal(offset, 64)
            state.x86_memory = state.x86_memory.store_limb(addr, val, domain=MemoryDomain.STACK)

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

    def _require_64_bit_operand(size_bytes: Optional[int], operand_kind: str) -> None:
        if size_bytes != 8:
            raise NotImplementedError(
                f"{mnemonic.upper()} only supports 64-bit operands; "
                f"{operand_kind}_size={size_bytes}"
            )

    def _get_register_pointer_tag(reg) -> PointerTag:
        if reg is None:
            return PointerTag.NONE
        return state.x86_registers.get_pointer_tag(reg)

    def _set_register_pointer_tag(reg, size_bytes: Optional[int], tag: PointerTag) -> None:
        if reg is None:
            return
        if size_bytes == 8 and tag != PointerTag.NONE:
            state.x86_registers.set_pointer_tag(reg, tag)
        else:
            state.x86_registers.clear_pointer_tag(reg)

    def _pointer_tag_for_callengine_pointer_load(size_bytes: Optional[int]) -> PointerTag:
        if operands.get('base_reg') != Register.R13 or size_bytes != 8:
            return PointerTag.NONE
        if operands.get('index_reg') is not None:
            return PointerTag.NONE
        offset = operands.get('offset')
        if not isinstance(offset, int):
            return PointerTag.NONE
        return _POINTER_TAG_BY_CALLENGINE_OFFSET.get(offset, PointerTag.NONE)

    def _resolve_pointer_tag_from_regs(base_reg, index_reg) -> PointerTag:
        base_tag = _get_register_pointer_tag(base_reg)
        index_tag = _get_register_pointer_tag(index_reg)
        tags = [tag for tag in (base_tag, index_tag) if tag != PointerTag.NONE]
        if not tags:
            return PointerTag.NONE
        if all(tag == tags[0] for tag in tags):
            return tags[0]
        return PointerTag.NONE

    def _resolve_mem_operand_pointer_tag() -> PointerTag:
        return _resolve_pointer_tag_from_regs(operands.get('base_reg'), operands.get('index_reg'))

    def _resolve_writable_domain_from_mem_operand() -> Optional[MemoryDomain]:
        """为 domain=None 的内存操作解析可写域 provenance。

        这里只接受显式白名单中的 writable tags；readonly tags 与未来新增 tags
        默认都不参与 writable routing，因此 readonly/writable 输入集合天然互斥。

        此 helper 依赖算术传播规则维护的一个不变式：有意义的 writable
        provenance 在地址算术后至多单侧保留。若 base/index 同时带 writable
        provenance，则视为歧义并拒绝路由。
        """
        writable_domains = []
        for reg in (operands.get('base_reg'), operands.get('index_reg')):
            tag = _get_register_pointer_tag(reg)
            domain = _WRITABLE_DOMAIN_BY_POINTER_TAG.get(tag)
            if domain is not None:
                writable_domains.append(domain)
        if len(writable_domains) == 1:
            return writable_domains[0]
        return None

    def _load_bytes_little_endian(bytes_list):
        size_bytes = len(bytes_list)
        if size_bytes == 1:
            return ZeroExt(56, bytes_list[0])
        if size_bytes == 2:
            return ZeroExt(48, Concat(bytes_list[1], bytes_list[0]))
        if size_bytes == 4:
            return ZeroExt(32, Concat(bytes_list[3], bytes_list[2], bytes_list[1], bytes_list[0]))
        return Concat(*reversed(bytes_list))

    def _load_bytes_from_array(byte_array, base_addr64, effective_addr64, size_bytes: int):
        source_offset = effective_addr64 - base_addr64
        # calldata/code/return_data 都按“低地址存低字节”的线性字节流建模；
        # 这里按小端序把连续字节重新拼回 64-bit/32-bit/16-bit 读取结果。
        bytes_list = [Select(byte_array, source_offset + BitVecVal(i, 64)) for i in range(size_bytes)]
        return _load_bytes_little_endian(bytes_list)

    def _select_address_byte(address_value, byte_index64):
        # Go common.Address 是 20-byte big-endian buffer；EVM stack value 是
        # zero-extended uint160，地址字节对应 value 的低 160 bits。
        #
        # AOT amd64 makeMem20ToStack maps the 20-byte buffer into uint256 limbs:
        #   mem:        -----> bigger address
        #          | 0-3 | 4-11 | 12-19 |
        #             |     |       |
        #   stack:  v3[4:8] v2      v1       (v4 = 0)
        #   loc: bigger address <-----
        selected = BitVecVal(0, 8)
        for byte_index in reversed(range(20)):
            high = 159 - 8 * byte_index
            low = high - 7
            selected = If(
                byte_index64 == BitVecVal(byte_index, 64),
                Extract(high, low, address_value),
                selected,
            )
        return selected

    def _load_bytes_from_address_value(address_value, base_addr64, effective_addr64, size_bytes: int):
        source_offset = effective_addr64 - base_addr64
        bytes_list = [
            _select_address_byte(address_value, source_offset + BitVecVal(i, 64))
            for i in range(size_bytes)
        ]
        return _load_bytes_little_endian(bytes_list)

    def _load_readonly_source_by_tag(tag: PointerTag, effective_addr64, size_bytes: Optional[int]):
        if tag == PointerTag.NONE or size_bytes is None:
            return None
        source_attrs = _READONLY_SOURCE_ATTRS.get(tag)
        if source_attrs is not None:
            pointer_attr, array_attr = source_attrs
            return _load_bytes_from_array(
                getattr(state, array_attr),
                getattr(state, pointer_attr),
                effective_addr64,
                size_bytes,
            )
        address_attrs = _ADDRESS_SOURCE_ATTRS.get(tag)
        if address_attrs is not None:
            pointer_attr, address_attr = address_attrs
            return _load_bytes_from_address_value(
                getattr(state, address_attr),
                getattr(state, pointer_attr),
                effective_addr64,
                size_bytes,
            )
        return None


    def _effective_address() -> Tuple[BitVec, Optional[MemoryDomain]]:
        """计算 effective address 并按 base_reg 推导 domain。

        domain=None 表示路由不出来（RIP-relative / 绝对地址 / 非 R13/R14/R15 base）。
        LEA 路径忽略 domain；_load_memory_by_size / _store_memory_by_size 在 domain=None
        时抛 MemoryDomainError。
        """
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
            domain: Optional[MemoryDomain] = None  # 仅 lea 用，此分支不会被 load/store 调用
        elif base_reg is None:
            addr = offset
            domain = None
        else:
            addr = state.x86_registers.get_register(base_reg) + offset
            domain = _classify_domain(base_reg)

        index_reg = operands.get('index_reg')
        if index_reg is not None:
            scale = operands.get('scale', 1) or 1
            index_val = state.x86_registers.get_register(index_reg)
            if scale != 1:
                index_val = index_val * BitVecVal(scale, 64)
            addr = addr + index_val
        return addr, domain

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

    def _update_adc_flags(lhs64, rhs64, result64, carry_out):
        # ADC OF uses the original rhs; folding CF into rhs can wrap its sign bit.
        overflow = Extract(63, 63, (~(lhs64 ^ rhs64)) & (lhs64 ^ result64))
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

        overflow = Extract(63, 63, (lhs64 ^ rhs64) & (lhs64 ^ result64))

        state.x86_registers.set_flag('CF', borrow)
        state.x86_registers.set_flag('OF', overflow)
        state.x86_registers.set_flag('ZF', _bool_to_bv1(result64 == BitVecVal(0, 64)))
        state.x86_registers.set_flag('SF', Extract(63, 63, result64))

    def _require_domain(domain: Optional[MemoryDomain], size_bytes: Optional[int]) -> MemoryDomain:
        if domain is not None:
            return domain
        # 测试桩 fallback：仅对显式声明 unrouted_memory_domain 的 SMTState 生效。
        # 生产路径（create_initial_state 创建的 state）这一字段为 None，触发抛错。
        fallback = getattr(state, "unrouted_memory_domain", None)
        if fallback is not None:
            return fallback
        raise MemoryDomainError(
            f"unrouted memory access (mnemonic={insn.mnemonic}, "
            f"base_reg={operands.get('base_reg')}, size={size_bytes})",
            base_reg=operands.get('base_reg'),
            size_bytes=size_bytes,
            disasm=str(insn),
        )

    def _load_memory_by_size(addr64, domain: Optional[MemoryDomain], size_bytes: Optional[int]):
        # callEngine side-channel 优先（避开穿透 Array Store 链）
        callengine_value = _maybe_read_callengine_field(state, operands, size_bytes)
        if callengine_value is not None:
            return callengine_value
        if domain is None:
            readonly_tag = _resolve_mem_operand_pointer_tag()
            readonly_value = _load_readonly_source_by_tag(readonly_tag, addr64, size_bytes)
            if readonly_value is not None:
                return readonly_value
            # readonly tags 不在 writable whitelist 中，因此这里的顺序只是
            # defense in depth，而不是 correctness dependency。
            domain = _resolve_writable_domain_from_mem_operand()
        d = _require_domain(domain, size_bytes)
        if size_bytes == 1:
            return ZeroExt(56, state.x86_memory.load_byte(addr64, domain=d))
        if size_bytes == 2:
            b0 = state.x86_memory.load_byte(addr64, domain=d)
            b1 = state.x86_memory.load_byte(addr64 + BitVecVal(1, 64), domain=d)
            return ZeroExt(48, Concat(b1, b0))
        if size_bytes == 4:
            b0 = state.x86_memory.load_byte(addr64, domain=d)
            b1 = state.x86_memory.load_byte(addr64 + BitVecVal(1, 64), domain=d)
            b2 = state.x86_memory.load_byte(addr64 + BitVecVal(2, 64), domain=d)
            b3 = state.x86_memory.load_byte(addr64 + BitVecVal(3, 64), domain=d)
            return ZeroExt(32, Concat(b3, b2, b1, b0))
        return state.x86_memory.load_limb(addr64, domain=d)

    def _store_memory_by_size(addr64, domain: Optional[MemoryDomain],
                              size_bytes: Optional[int], value64):
        if domain is None:
            readonly_tag = _resolve_mem_operand_pointer_tag()
            if readonly_tag in _READONLY_POINTER_TAGS:
                raise MemoryDomainError(
                    f"cannot write through readonly source pointer (mnemonic={insn.mnemonic}, "
                    f"tag={readonly_tag})",
                    base_reg=operands.get('base_reg'),
                    size_bytes=size_bytes,
                    disasm=str(insn),
                )
            # readonly tags 不在 writable whitelist 中，因此这里的顺序只是
            # defense in depth，而不是 correctness dependency。
            domain = _resolve_writable_domain_from_mem_operand()
        d = _require_domain(domain, size_bytes)
        if size_bytes == 1:
            return state.x86_memory.store_byte(addr64, Extract(7, 0, value64), domain=d)
        if size_bytes == 2:
            mem = state.x86_memory
            mem = mem.store_byte(addr64, Extract(7, 0, value64), domain=d)
            mem = mem.store_byte(addr64 + BitVecVal(1, 64), Extract(15, 8, value64), domain=d)
            return mem
        if size_bytes == 4:
            mem = state.x86_memory
            mem = mem.store_byte(addr64, Extract(7, 0, value64), domain=d)
            mem = mem.store_byte(addr64 + BitVecVal(1, 64), Extract(15, 8, value64), domain=d)
            mem = mem.store_byte(addr64 + BitVecVal(2, 64), Extract(23, 16, value64), domain=d)
            mem = mem.store_byte(addr64 + BitVecVal(3, 64), Extract(31, 24, value64), domain=d)
            return mem
        return state.x86_memory.store_limb(addr64, value64, domain=d)

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

    def _propagate_add_reg_reg_pointer_tag(dest_tag: PointerTag,
                                           src_tag: PointerTag) -> PointerTag:
        if dest_tag == PointerTag.NONE and src_tag != PointerTag.NONE:
            return src_tag
        if dest_tag != PointerTag.NONE and src_tag == PointerTag.NONE:
            return dest_tag
        return PointerTag.NONE
    
    if mnemonic == 'mov':
        # MOV：将值从源移动到目标
        if operands['is_memory'] and operands['dest_reg']:
            # MOV reg, [base+offset]
            dest_reg = operands['dest_reg']
            dest_size = operands.get('dest_size')
            memory_size = operands.get('memory_size')
            memory_offset, memory_domain = _effective_address()
            mem_val = _load_memory_by_size(memory_offset, memory_domain, memory_size)
            _write_register_by_size(dest_reg, mem_val, dest_size)
            _set_register_pointer_tag(
                dest_reg,
                dest_size,
                _pointer_tag_for_callengine_pointer_load(memory_size),
            )

        elif operands['is_memory'] and operands['src_reg']:
            # MOV [base+offset], reg
            src_reg = operands['src_reg']
            src_size = operands.get('src_size')
            memory_size = operands.get('memory_size')
            memory_offset, memory_domain = _effective_address()

            reg_val = _read_register_by_size(src_reg, src_size)
            new_memory_state = _store_memory_by_size(memory_offset, memory_domain, memory_size, reg_val)
            state.x86_memory = new_memory_state
            _maybe_update_callengine_field(state, operands, memory_size, reg_val)
        
        elif operands['dest_reg'] and operands['src_reg']:
            # MOV reg1, reg2
            dest_reg = operands['dest_reg']
            dest_size = operands.get('dest_size')
            src_reg = operands['src_reg']
            src_size = operands.get('src_size')
            src_val = _read_register_by_size(src_reg, src_size)
            _write_register_by_size(dest_reg, src_val, dest_size)
            copied_tag = (
                _get_register_pointer_tag(src_reg)
                if dest_size == 8 and src_size == 8
                else PointerTag.NONE
            )
            _set_register_pointer_tag(dest_reg, dest_size, copied_tag)

        elif operands['dest_reg'] and operands['immediate'] is not None:
            # MOV reg, immediate
            dest_reg = operands['dest_reg']
            dest_size = operands.get('dest_size')
            imm_val = _imm_to_bv64(dest_size)
            _write_register_by_size(dest_reg, imm_val, dest_size)
        
        elif operands['is_memory'] and operands['immediate'] is not None:
            # MOV [base+offset], immediate
            memory_size = operands.get('memory_size')
            memory_offset, memory_domain = _effective_address()
            imm_val = _imm_to_bv64(memory_size)
            state.x86_memory = _store_memory_by_size(memory_offset, memory_domain, memory_size, imm_val)
            _maybe_update_callengine_field(state, operands, memory_size, imm_val)
        
        return state

    elif mnemonic == 'movzx':
        # MOVZX：零扩展移动
        if not operands['dest_reg']:
            raise ValueError(f"MOVZX instruction must have register destination: {operands}")

        dest_reg = operands['dest_reg']
        dest_size = operands.get('dest_size')

        if operands['is_memory']:
            mem_addr, mem_domain = _effective_address()
            src_val = _load_memory_by_size(mem_addr, mem_domain, operands.get('memory_size'))
        elif operands['src_reg']:
            src_val = _read_register_by_size(operands['src_reg'], operands.get('src_size'))
        else:
            raise ValueError(f"Unsupported MOVZX operand combination: {operands}")

        _write_register_by_size(dest_reg, src_val, dest_size)
        _set_register_pointer_tag(dest_reg, dest_size, PointerTag.NONE)
        return state

    elif mnemonic == 'lea':
        # LEA：只计算有效地址，不访问内存且不修改标志位
        # LEA 不进 _load/_store_memory_by_size，因此忽略 domain（包括 RIP-relative 与非 R13/R14/R15 base）
        if not operands['dest_reg'] or not operands['is_memory']:
            raise ValueError(f"Unsupported LEA operand combination: {operands}")

        dest_reg = operands['dest_reg']
        dest_size = operands.get('dest_size')
        effective_addr, _domain = _effective_address()
        _write_register_by_size(dest_reg, effective_addr, dest_size)
        _set_register_pointer_tag(dest_reg, dest_size, _resolve_mem_operand_pointer_tag())
        return state
    
    elif mnemonic == 'add':
        # ADD：将源加到目标，设置进位标志
        if operands['is_memory'] and not operands['dest_reg']:
            # ADD [base+offset], reg/imm
            memory_size = operands.get('memory_size')
            _require_64_bit_operand(memory_size, 'memory')
            memory_offset, memory_domain = _effective_address()
            lhs_val = _load_memory_by_size(memory_offset, memory_domain, memory_size)

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

            state.x86_memory = _store_memory_by_size(memory_offset, memory_domain, memory_size, result)
            _update_add_like_flags(lhs_val, rhs_val, result, carry_out)
            _maybe_update_callengine_field(state, operands, memory_size, result)
            return state

        if not operands['dest_reg']:
            raise ValueError(f"ADD instruction must have register destination: {operands}")

        dest_reg = operands['dest_reg']
        dest_size = operands.get('dest_size')
        _require_64_bit_operand(dest_size, 'dest')
        reg_val = _read_register_by_size(dest_reg, dest_size)
        dest_tag = _get_register_pointer_tag(dest_reg)
        
        if operands['is_memory']:
            # ADD reg, [base+offset]
            memory_offset, memory_domain = _effective_address()
            mem_val = _load_memory_by_size(memory_offset, memory_domain, operands.get('memory_size'))

            # 执行加法（64位，带进位生成）
            reg_ext = Concat(BitVecVal(0, 1), reg_val)
            mem_ext = Concat(BitVecVal(0, 1), mem_val)
            sum_ext = reg_ext + mem_ext

            # 提取结果和进位
            result = Extract(63, 0, sum_ext)
            carry_out = Extract(64, 64, sum_ext)

            # 更新寄存器和标志
            _write_register_by_size(dest_reg, result, dest_size)
            # memory operand 的 tag 仅用于 routing，不表示读出来的值本身是指针；
            # 这里保持现有行为，只保留 destination 自身的 provenance。
            _set_register_pointer_tag(dest_reg, dest_size, dest_tag)
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
            src_tag = _get_register_pointer_tag(src_reg)
            result_tag = _propagate_add_reg_reg_pointer_tag(dest_tag, src_tag)
            _set_register_pointer_tag(dest_reg, dest_size, result_tag)
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
            _set_register_pointer_tag(dest_reg, dest_size, dest_tag)
            _update_add_like_flags(reg_val, imm_val, result, carry_out)
        
        return state
    
    elif mnemonic == 'adc':
        # ADC：带进位加法
        if not operands['dest_reg']:
            raise ValueError(f"ADC instruction must have register destination: {operands}")
        
        dest_reg = operands['dest_reg']
        dest_size = operands.get('dest_size')
        _require_64_bit_operand(dest_size, 'dest')
        reg_val = _read_register_by_size(dest_reg, dest_size)
        carry_in = state.x86_registers.get_flag('CF')

        if operands['is_memory']:
            mem_addr, mem_domain = _effective_address()
            rhs_val = _load_memory_by_size(mem_addr, mem_domain, operands.get('memory_size'))
        elif operands['src_reg']:
            rhs_val = _read_register_by_size(operands['src_reg'], operands.get('src_size'))
        elif operands['immediate'] is not None:
            rhs_val = _imm_to_bv64(dest_size)
        else:
            raise ValueError(f"Unsupported ADC operand combination: {operands}")

        # 执行带进位加法
        reg_ext = Concat(BitVecVal(0, 1), reg_val)
        rhs_ext = Concat(BitVecVal(0, 1), rhs_val)
        carry_ext = Concat(BitVecVal(0, 64), carry_in)
        sum_ext = reg_ext + rhs_ext + carry_ext
        
        result = Extract(63, 0, sum_ext)
        carry_out = Extract(64, 64, sum_ext)
        
        _write_register_by_size(dest_reg, result, dest_size)
        _update_adc_flags(reg_val, rhs_val, result, carry_out)
        
        return state

    elif mnemonic == 'sbb':
        # SBB：带借位减法
        if not operands['dest_reg']:
            raise ValueError(f"SBB instruction must have register destination: {operands}")

        dest_reg = operands['dest_reg']
        dest_size = operands.get('dest_size')
        _require_64_bit_operand(dest_size, 'dest')
        lhs = _read_register_by_size(dest_reg, dest_size)
        carry_in = state.x86_registers.get_flag('CF')

        if operands['is_memory']:
            mem_addr, mem_domain = _effective_address()
            rhs = _load_memory_by_size(mem_addr, mem_domain, operands.get('memory_size'))
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
        _require_64_bit_operand(dest_size, 'dest')
        reg_val = _read_register_by_size(dest_reg, dest_size)
        dest_tag = _get_register_pointer_tag(dest_reg)

        if operands['is_memory']:
            mem_addr, mem_domain = _effective_address()
            rhs_val = _load_memory_by_size(mem_addr, mem_domain, operands.get('memory_size'))
        elif operands['src_reg']:
            rhs_val = _read_register_by_size(operands['src_reg'], operands.get('src_size'))
        elif operands['immediate'] is not None:
            rhs_val = _imm_to_bv64(dest_size)
        else:
            raise ValueError(f"Unsupported SUB operand combination: {operands}")

        result = reg_val - rhs_val
        _write_register_by_size(dest_reg, result, dest_size)
        if operands['immediate'] is not None:
            _set_register_pointer_tag(dest_reg, dest_size, dest_tag)
        _update_sub_like_flags(reg_val, rhs_val, result)

        return state

    elif mnemonic == 'inc':
        # INC：目标 + 1，不修改 CF
        if not operands['dest_reg']:
            raise ValueError(f"INC instruction must have register destination: {operands}")

        dest_reg = operands['dest_reg']
        dest_size = operands.get('dest_size')
        _require_64_bit_operand(dest_size, 'dest')
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
        _require_64_bit_operand(dest_size, 'dest')
        reg_val = _read_register_by_size(dest_reg, dest_size)
        
        if operands['is_memory']:
            mem_addr, mem_domain = _effective_address()
            rhs_val = _load_memory_by_size(mem_addr, mem_domain, operands.get('memory_size'))
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

        dest_size = operands.get('dest_size')
        _require_64_bit_operand(dest_size, 'dest')
        lhs = _read_register_by_size(operands['dest_reg'], dest_size)
        if operands['src_reg']:
            rhs = _read_register_by_size(operands['src_reg'], operands.get('src_size'))
        elif operands['immediate'] is not None:
            rhs = _imm_to_bv64(operands.get('dest_size'))
        elif operands['is_memory']:
            mem_addr, mem_domain = _effective_address()
            rhs = _load_memory_by_size(mem_addr, mem_domain, operands.get('memory_size'))
        else:
            raise ValueError(f"Unsupported TEST operand combination: {operands}")

        _update_logic_flags(lhs & rhs)
        return state
    
    elif mnemonic == 'ret':
        # RET 指令：检查退出状态码，并在需要时提取返回/回退数据
        # 优先读取 callEngine side-channel，避免在 ret 上再次穿透 x86_memory 的长 Store 链。
        status_code = state.callengine_status_code
        
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
        sp_bv = state.callengine_stack_pointer_limbs

        # 使用当前 sp 反推出逻辑栈顶两项的物理地址
        limb_size = BitVecVal(8, 64)
        stack0_base = r14_value + (sp_bv - BitVecVal(4, 64)) * limb_size
        stack1_base = r14_value + (sp_bv - BitVecVal(8, 64)) * limb_size
        # Go runtime 在这里消费的是 PopUint64()，只观察每个 256-bit 栈值的低 64-bit limb。
        # 直接读取 z0 可显著减轻 return 条件和 return data 公式的体积。
        offset_bv = state.x86_memory.load_64bit(stack0_base, domain=MemoryDomain.STACK)
        length_bv = state.x86_memory.load_64bit(stack1_base, domain=MemoryDomain.STACK)
        
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
            memory_size = operands.get('memory_size')
            _require_64_bit_operand(memory_size, 'memory')
            mem_addr, mem_domain = _effective_address()
            op_val = _load_memory_by_size(mem_addr, mem_domain, memory_size)
        elif operands['dest_reg']:
            dest_size = operands.get('dest_size')
            _require_64_bit_operand(dest_size, 'dest')
            op_val = _read_register_by_size(operands['dest_reg'], dest_size)
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
            memory_size = operands.get('memory_size')
            _require_64_bit_operand(memory_size, 'memory')
            mem_addr, mem_domain = _effective_address()
            divisor = _load_memory_by_size(mem_addr, mem_domain, memory_size)
        elif operands['dest_reg']:
            dest_size = operands.get('dest_size')
            _require_64_bit_operand(dest_size, 'dest')
            divisor = _read_register_by_size(operands['dest_reg'], dest_size)
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
        _require_64_bit_operand(dest_size, 'dest')
        reg_val = _read_register_by_size(dest_reg, dest_size)

        if operands['is_memory']:
            # AND reg, [base+offset]
            memory_offset, memory_domain = _effective_address()
            mem_val = _load_memory_by_size(memory_offset, memory_domain, operands.get('memory_size'))
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
        _require_64_bit_operand(dest_size, 'dest')
        reg_val = _read_register_by_size(dest_reg, dest_size)

        if operands['is_memory']:
            # OR reg, [base+offset]
            memory_offset, memory_domain = _effective_address()
            mem_val = _load_memory_by_size(memory_offset, memory_domain, operands.get('memory_size'))
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
        _require_64_bit_operand(dest_size, 'dest')
        reg_val = _read_register_by_size(dest_reg, dest_size)

        if operands['is_memory']:
            # XOR reg, [base+offset]
            memory_offset, memory_domain = _effective_address()
            mem_val = _load_memory_by_size(memory_offset, memory_domain, operands.get('memory_size'))
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
        if operands['is_memory'] and not operands['dest_reg']:
            mem_size = operands.get('memory_size')
            _require_64_bit_operand(mem_size, 'memory')
            count64 = _shift_count_64()
            addr, addr_domain = _effective_address()
            lhs = _load_memory_by_size(addr, addr_domain, mem_size)
            result = lhs << count64
            state.x86_memory = _store_memory_by_size(addr, addr_domain, mem_size, result)
            _set_shift_flags(lhs, result, count64, is_left=True)
            _maybe_update_callengine_field(state, operands, mem_size, result)
            return state

        if not operands['dest_reg']:
            raise ValueError(f"SHL instruction must have destination operand: {operands}")

        dest_reg = operands['dest_reg']
        dest_size = operands.get('dest_size')
        _require_64_bit_operand(dest_size, 'dest')
        count64 = _shift_count_64()
        lhs = _read_register_by_size(dest_reg, dest_size)
        result = lhs << count64
        _write_register_by_size(dest_reg, result, dest_size)
        _set_shift_flags(lhs, result, count64, is_left=True)
        return state

    elif mnemonic == 'shr':
        # SHR：逻辑右移
        if operands['is_memory'] and not operands['dest_reg']:
            mem_size = operands.get('memory_size')
            _require_64_bit_operand(mem_size, 'memory')
            count64 = _shift_count_64()
            addr, addr_domain = _effective_address()
            lhs = _load_memory_by_size(addr, addr_domain, mem_size)
            result = LShR(lhs, count64)
            state.x86_memory = _store_memory_by_size(addr, addr_domain, mem_size, result)
            _set_shift_flags(lhs, result, count64, is_left=False)
            _maybe_update_callengine_field(state, operands, mem_size, result)
            return state

        if not operands['dest_reg']:
            raise ValueError(f"SHR instruction must have destination operand: {operands}")

        dest_reg = operands['dest_reg']
        dest_size = operands.get('dest_size')
        _require_64_bit_operand(dest_size, 'dest')
        count64 = _shift_count_64()
        lhs = _read_register_by_size(dest_reg, dest_size)
        result = LShR(lhs, count64)
        _write_register_by_size(dest_reg, result, dest_size)
        _set_shift_flags(lhs, result, count64, is_left=False)
        return state

    elif mnemonic == 'not':
        # NOT：按位取反，不影响标志位
        if operands['is_memory'] and not operands['dest_reg']:
            addr, addr_domain = _effective_address()
            mem_size = operands.get('memory_size')
            value = _load_memory_by_size(addr, addr_domain, mem_size)
            result = ~value
            state.x86_memory = _store_memory_by_size(addr, addr_domain, mem_size, result)
            _maybe_update_callengine_field(state, operands, mem_size, result)
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
            addr, addr_domain = _effective_address()
            mem_size = operands.get('memory_size') or 1
            state.x86_memory = _store_memory_by_size(addr, addr_domain, mem_size, value64)
            _maybe_update_callengine_field(state, operands, mem_size, value64)
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
