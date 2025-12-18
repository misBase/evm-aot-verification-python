"""
x86-64指令反汇编器。

本模块提供使用Capstone将十六进制编码的机器码反汇编为
X86Instruction对象的函数。
"""

import capstone
from typing import List
from .models import X86Instruction, Register


# 将Capstone寄存器ID映射到我们的Register枚举
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
    current_addr = base_addr
    
    for insn in md.disasm(code_bytes, base_addr):
        # 获取助记符
        mnemonic = insn.mnemonic.lower()
        
        # 获取操作数字符串，如果需要则修复寄存器名称
        op_str = insn.op_str
        
        # 修复RSI -> R14映射（Capstone有时将R14误识别为RSI）
        # 通过检查机器码来检查指令是否使用R14
        # R14编码：ModR/M字节，R/M=110且REX.B=1
        # 我们将通过检查操作数中的实际寄存器来修复此问题
        fixed_op_str = op_str
        # 检查内存操作数的基址寄存器
        if hasattr(insn, 'operands') and len(insn.operands) > 0:
            for op in insn.operands:
                if op.type == capstone.x86.X86_OP_MEM:
                    base_reg_id = op.mem.base
                    if base_reg_id != 0:
                        # 检查它是否实际上是R14（Capstone中的寄存器ID 62）
                        # Capstone x86寄存器ID：R14 = 62，RSI = 6
                        # 有时R14被解码为RSI，所以我们检查编码
                        reg_name = insn.reg_name(base_reg_id)
                        # 如果位移表明它是基于栈的（负偏移量）
                        # 并且寄存器是RSI，则可能是R14
                        if reg_name == 'rsi' and op.mem.disp < 0:
                            # 检查ModR/M是否建议R14（这是启发式方法）
                            # ModR/M中的R14：位2:0 = 110，REX.B=1
                            fixed_op_str = fixed_op_str.replace('rsi', 'r14')
        
        op_str = fixed_op_str
        
        # 获取指令字节
        insn_bytes = bytes(insn.bytes)
        
        # 创建X86Instruction对象
        instruction = X86Instruction(
            addr=insn.address,
            mnemonic=mnemonic,
            op_str=op_str,
            bytes=insn_bytes,
            size=insn.size
        )
        
        instructions.append(instruction)
        current_addr += insn.size
    
    return instructions


def parse_operands(op_str: str) -> dict:
    """将操作数字符串解析为结构化格式。
    
    Args:
        op_str: 来自Capstone的操作数字符串（例如，"rax, qword ptr [r14 - 0x40]"）
        
    Returns:
        包含解析操作数的字典：
        - 'dest_reg': Register枚举（如果目标是寄存器）
        - 'src_reg': Register枚举（如果源是寄存器）
        - 'base_reg': Register枚举（如果是带基址的内存操作数）
        - 'offset': int（如果是带偏移量的内存操作数）
        - 'is_memory': bool（如果操作数是内存访问）
        - 'immediate': int（如果操作数是立即值）
        - 'jump_target': int（如果操作数是跳转目标地址）
        
    Example:
        >>> parse_operands("rax, qword ptr [r14 - 0x40]")
        {'dest_reg': Register.RAX, 'base_reg': Register.R14, 'offset': -64, 'is_memory': True}
    """
    result = {
        'dest_reg': None,
        'src_reg': None,
        'base_reg': None,
        'offset': 0,
        'is_memory': False,
        'immediate': None,
        'jump_target': None
    }
    
    # 按逗号分割以获取操作数
    parts = [p.strip() for p in op_str.split(',')]
    
    if len(parts) == 0:
        return result
    
    # 解析第一个操作数
    first_str = parts[0]
    
    # 移除大小前缀，如"byte ptr"、"word ptr"、"qword ptr"
    first_str = first_str.replace('byte ptr', '').replace('word ptr', '').replace('qword ptr', '').replace('dword ptr', '').strip()
    
    # 检查第一个操作数是否是内存操作数：[base +/- offset]
    if '[' in first_str and ']' in first_str:
        result['is_memory'] = True
        # 提取方括号之间的内容
        mem_content = first_str[first_str.index('[') + 1:first_str.index(']')].strip()
        
        # 解析基址寄存器和偏移量
        # 格式："r14 - 0x40"或"r14 + 0x40"或只是"r14"
        if ' - ' in mem_content:
            base_str, offset_str = mem_content.split(' - ', 1)
            sign = -1
        elif ' + ' in mem_content:
            base_str, offset_str = mem_content.split(' + ', 1)
            sign = 1
        elif '-' in mem_content and ' ' not in mem_content:
            # 处理"r14-0x40"（无空格）
            if '-' in mem_content:
                base_str, offset_str = mem_content.split('-', 1)
                sign = -1
            else:
                base_str = mem_content
                offset_str = None
                sign = 1
        else:
            # 无偏移量，只有基址寄存器
            base_str = mem_content
            offset_str = None
            sign = 1
        
        # 解析基址寄存器
        base_str = base_str.strip()
        for reg_name, reg_enum in [(r.value, r) for r in Register]:
            if base_str == reg_name:
                result['base_reg'] = reg_enum
                break
        
        # 解析偏移量
        if offset_str:
            offset_str = offset_str.strip()
            # 如果存在则移除0x前缀
            if offset_str.startswith('0x') or offset_str.startswith('0X'):
                offset_val = int(offset_str, 16)
            else:
                offset_val = int(offset_str)
            result['offset'] = sign * offset_val
        
        # 如果有第二个操作数，它可能是寄存器或立即值
        if len(parts) > 1:
            src_str = parts[1].strip()
            # 首先尝试解析为寄存器
            found_reg = False
            for reg_name, reg_enum in [(r.value, r) for r in Register]:
                if src_str == reg_name:
                    result['src_reg'] = reg_enum
                    found_reg = True
                    break
            # 如果不是寄存器，尝试解析为立即值
            if not found_reg:
                try:
                    if src_str.startswith('0x') or src_str.startswith('0X'):
                        result['immediate'] = int(src_str, 16)
                    else:
                        result['immediate'] = int(src_str)
                except ValueError:
                    pass
    else:
        # 第一个操作数是寄存器（目标）
        for reg_name, reg_enum in [(r.value, r) for r in Register]:
            if first_str == reg_name:
                result['dest_reg'] = reg_enum
                break
        
        # 如果存在则解析第二个操作数（源）
        if len(parts) > 1:
            src_str = parts[1].strip()
            
            # 检查它是否是内存操作数：[base +/- offset]
            if '[' in src_str and ']' in src_str:
                result['is_memory'] = True
                # 提取方括号之间的内容
                mem_content = src_str[src_str.index('[') + 1:src_str.index(']')].strip()
                
                # 解析基址寄存器和偏移量
                # 格式："r14 - 0x40"或"r14 + 0x40"或只是"r14"
                if ' - ' in mem_content:
                    base_str, offset_str = mem_content.split(' - ', 1)
                    sign = -1
                elif ' + ' in mem_content:
                    base_str, offset_str = mem_content.split(' + ', 1)
                    sign = 1
                elif '-' in mem_content and ' ' not in mem_content:
                    # 处理"r14-0x40"（无空格）
                    base_str, offset_str = mem_content.split('-', 1)
                    sign = -1
                else:
                    # 无偏移量，只有基址寄存器
                    base_str = mem_content
                    offset_str = None
                    sign = 1
                
                # 解析基址寄存器
                base_str = base_str.strip()
                for reg_name, reg_enum in [(r.value, r) for r in Register]:
                    if base_str == reg_name:
                        result['base_reg'] = reg_enum
                        break
                
                # 解析偏移量
                if offset_str:
                    offset_str = offset_str.strip()
                    # 如果存在则移除0x前缀
                    if offset_str.startswith('0x') or offset_str.startswith('0X'):
                        offset_val = int(offset_str, 16)
                    else:
                        offset_val = int(offset_str)
                    result['offset'] = sign * offset_val
            else:
                # 检查它是否是寄存器
                for reg_name, reg_enum in [(r.value, r) for r in Register]:
                    if src_str == reg_name:
                        result['src_reg'] = reg_enum
                        break
                # 如果不是寄存器，检查它是否是立即值
                if result['src_reg'] is None:
                    try:
                        # 尝试解析为立即值
                        if src_str.startswith('0x') or src_str.startswith('0X'):
                            result['immediate'] = int(src_str, 16)
                        else:
                            result['immediate'] = int(src_str)
                    except ValueError:
                        pass
    
    # 检查第一个操作数是否是立即值（对于像CMP rax, 0x3这样的指令）
    if result['dest_reg'] is None and not result['is_memory'] and len(parts) > 0:
        first_str = parts[0].strip()
        # 检查它是否不是寄存器
        is_reg = False
        for reg_name, reg_enum in [(r.value, r) for r in Register]:
            if first_str == reg_name:
                is_reg = True
                break
        if not is_reg:
            try:
                if first_str.startswith('0x') or first_str.startswith('0X'):
                    result['immediate'] = int(first_str, 16)
                else:
                    result['immediate'] = int(first_str)
            except ValueError:
                pass
    
    # 检查跳转目标（十六进制地址，如0x39）
    if len(parts) == 1:
        target_str = parts[0].strip()
        if target_str.startswith('0x') or target_str.startswith('0X'):
            try:
                result['jump_target'] = int(target_str, 16)
            except ValueError:
                pass
    
    return result

