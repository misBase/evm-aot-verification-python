"""
x86-64指令反汇编器。

本模块提供使用Capstone将十六进制编码的机器码反汇编为
X86Instruction对象的函数。
"""

import capstone
from typing import List
from .models import X86Instruction, Register


# 将Capstone寄存器ID映射到我们的Register枚举
# 注意：Go编译器只生成64位指令，因此只需要64位寄存器映射
REGISTER_MAP = {
    capstone.x86.X86_REG_RAX: Register.RAX,
    capstone.x86.X86_REG_RCX: Register.RCX,
    capstone.x86.X86_REG_RDX: Register.RDX,
    capstone.x86.X86_REG_RBX: Register.RBX,
    capstone.x86.X86_REG_RSI: Register.RSI,
    capstone.x86.X86_REG_RDI: Register.RDI,
    capstone.x86.X86_REG_R8: Register.R8,
    capstone.x86.X86_REG_R9: Register.R9,
    capstone.x86.X86_REG_R10: Register.R10,
    capstone.x86.X86_REG_R11: Register.R11,
    capstone.x86.X86_REG_R12: Register.R12,
    capstone.x86.X86_REG_R13: Register.R13,
    capstone.x86.X86_REG_R14: Register.R14,
    capstone.x86.X86_REG_R15: Register.R15,
}


def disassemble_hex(hex_str: str, base_addr: int = 0) -> List[X86Instruction]:
    """将十六进制编码的机器码反汇编为X86Instruction对象。
    
    Args:
        hex_str: 十六进制字符串（带或不带空格/0x前缀）
        base_addr: 指令的基址（默认：0）
        
    Returns:
        X86Instruction对象列表
        
    Example:
        >>> hex_code = "488b46c0 480346e0"
        >>> instructions = disassemble_hex(hex_code, base_addr=0x6c)
        >>> len(instructions)
        2
    """
    # 清理十六进制字符串（移除空格、0x前缀）
    hex_clean = hex_str.replace(' ', '').replace('0x', '').replace('0X', '')
    
    # 将十六进制字符串转换为字节
    try:
        code_bytes = bytes.fromhex(hex_clean)
    except ValueError as e:
        raise ValueError(f"Invalid hex string: {hex_str}") from e
    
    # 初始化x86-64的Capstone反汇编器
    md = capstone.Cs(capstone.CS_ARCH_X86, capstone.CS_MODE_64)
    md.detail = True  # 启用详细指令信息

    instructions = []

    for insn in md.disasm(code_bytes, base_addr):
        # 获取助记符
        mnemonic = insn.mnemonic.lower()

        # 获取操作数字符串
        # Capstone 5.0.6能正确识别所有寄存器，不需要任何修复
        op_str = insn.op_str
        
        # 获取指令字节
        insn_bytes = bytes(insn.bytes)

        # 创建X86Instruction对象，保存原始Capstone指令
        instruction = X86Instruction(
            addr=insn.address,
            mnemonic=mnemonic,
            op_str=op_str,
            bytes=insn_bytes,
            size=insn.size,
            _cs_insn=insn  # 保存原始Capstone指令对象
        )

        instructions.append(instruction)

    return instructions


def parse_operands(instruction: X86Instruction) -> dict:
    """使用Capstone操作数结构解析指令操作数。

    Args:
        instruction: X86Instruction对象（包含Capstone指令对象）

    Returns:
        包含解析操作数的字典：
        - 'dest_reg': Register枚举（如果目标是寄存器）
        - 'src_reg': Register枚举（如果源是寄存器）
        - 'base_reg': Register枚举（如果是带基址的内存操作数）
        - 'index_reg': Register枚举（如果有索引寄存器）
        - 'scale': int（索引寄存器的缩放因子）
        - 'offset': int（如果是带偏移量的内存操作数）
        - 'is_memory': bool（如果操作数是内存访问）
        - 'immediate': int（如果操作数是立即值）
        - 'jump_target': int（如果操作数是跳转目标地址）
        - 'is_indirect': bool（如果是间接跳转，即跳转目标是寄存器或内存）

    Example:
        >>> insn = disassemble_hex("498b46c0")[0]
        >>> parse_operands(insn)
        {'dest_reg': Register.RAX, 'base_reg': Register.R14, 'offset': -64, 'is_memory': True}
    """
    result = {
        'dest_reg': None,
        'src_reg': None,
        'base_reg': None,
        'index_reg': None,
        'scale': 1,
        'offset': 0,
        'is_memory': False,
        'immediate': None,
        'jump_target': None,
        'is_indirect': False
    }

    # 获取Capstone指令对象
    cs_insn = instruction._cs_insn
    if cs_insn is None or not hasattr(cs_insn, 'operands'):
        return result

    # 遍历操作数
    for i, op in enumerate(cs_insn.operands):
        if op.type == capstone.x86.X86_OP_REG:
            # 寄存器操作数
            reg_id = op.reg
            reg_enum = REGISTER_MAP.get(reg_id)

            # 第一个操作数通常是目标
            if i == 0:
                result['dest_reg'] = reg_enum
            else:
                result['src_reg'] = reg_enum

            # 检查是否是间接跳转（跳转指令的第一个操作数是寄存器）
            if (i == 0 and instruction.mnemonic in ['jmp', 'jb', 'jae', 'je', 'jne', 'jl', 'jle', 'jg', 'jge', 'call']):
                result['is_indirect'] = True

        elif op.type == capstone.x86.X86_OP_MEM:
            # 内存操作数
            result['is_memory'] = True

            # 基址寄存器
            if op.mem.base != 0:
                result['base_reg'] = REGISTER_MAP.get(op.mem.base)

            # 索引寄存器
            if op.mem.index != 0:
                result['index_reg'] = REGISTER_MAP.get(op.mem.index)

            # 缩放因子
            result['scale'] = op.mem.scale

            # 偏移量
            result['offset'] = op.mem.disp

            # 检查是否是间接跳转（跳转指令的第一个操作数是内存）
            if (i == 0 and instruction.mnemonic in ['jmp', 'jb', 'jae', 'je', 'jne', 'jl', 'jle', 'jg', 'jge', 'call']):
                result['is_indirect'] = True

        elif op.type == capstone.x86.X86_OP_IMM:
            # 立即数
            result['immediate'] = op.imm

            # 对于跳转指令，Capstone的op.imm已经包含了绝对跳转目标地址
            if instruction.mnemonic in ['jmp', 'jb', 'jae', 'je', 'jne', 'jl', 'jle', 'jg', 'jge', 'call']:
                result['jump_target'] = op.imm

    return result

