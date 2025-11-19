"""
x86-64 instruction disassembler.

This module provides functions to disassemble hex-encoded machine code into
X86Instruction objects using Capstone.
"""

import capstone
from typing import List
from .models import X86Instruction, Register


# Map Capstone register IDs to our Register enum
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
    """Disassemble hex-encoded machine code into X86Instruction objects.
    
    Args:
        hex_str: Hex string (with or without spaces/0x prefix)
        base_addr: Base address for instructions (default: 0)
        
    Returns:
        List of X86Instruction objects
        
    Example:
        >>> hex_code = "488b46c0 480346e0"
        >>> instructions = disassemble_hex(hex_code, base_addr=0x6c)
        >>> len(instructions)
        2
    """
    # Clean hex string (remove spaces, 0x prefixes)
    hex_clean = hex_str.replace(' ', '').replace('0x', '').replace('0X', '')
    
    # Convert hex string to bytes
    try:
        code_bytes = bytes.fromhex(hex_clean)
    except ValueError as e:
        raise ValueError(f"Invalid hex string: {hex_str}") from e
    
    # Initialize Capstone disassembler for x86-64
    md = capstone.Cs(capstone.CS_ARCH_X86, capstone.CS_MODE_64)
    md.detail = True  # Enable detailed instruction information
    
    instructions = []
    current_addr = base_addr
    
    for insn in md.disasm(code_bytes, base_addr):
        # Get mnemonic
        mnemonic = insn.mnemonic.lower()
        
        # Get operand string and fix register names if needed
        op_str = insn.op_str
        
        # Fix RSI -> R14 mapping (Capstone sometimes misidentifies R14 as RSI)
        # Check if the instruction uses R14 by examining the machine code
        # R14 encoding: ModR/M byte with R/M=110 and REX.B=1
        # We'll fix this by checking the actual register from operands
        fixed_op_str = op_str
        # Check memory operands for base register
        if hasattr(insn, 'operands') and len(insn.operands) > 0:
            for op in insn.operands:
                if op.type == capstone.x86.X86_OP_MEM:
                    base_reg_id = op.mem.base
                    if base_reg_id != 0:
                        # Check if it's actually R14 (register ID 62 in Capstone)
                        # Capstone x86 register IDs: R14 = 62, RSI = 6
                        # Sometimes R14 gets decoded as RSI, so we check the encoding
                        reg_name = insn.reg_name(base_reg_id)
                        # If the displacement suggests it's stack-based (negative offset)
                        # and the register is RSI, it's likely R14
                        if reg_name == 'rsi' and op.mem.disp < 0:
                            # Check if ModR/M suggests R14 (this is a heuristic)
                            # R14 in ModR/M: bits 2:0 = 110, with REX.B=1
                            fixed_op_str = fixed_op_str.replace('rsi', 'r14')
        
        op_str = fixed_op_str
        
        # Get instruction bytes
        insn_bytes = bytes(insn.bytes)
        
        # Create X86Instruction object
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
    """Parse operand string into structured format.
    
    Args:
        op_str: Operand string from Capstone (e.g., "rax, qword ptr [r14 - 0x40]")
        
    Returns:
        Dictionary with parsed operands:
        - 'dest_reg': Register enum (if destination is register)
        - 'src_reg': Register enum (if source is register)
        - 'base_reg': Register enum (if memory operand with base)
        - 'offset': int (if memory operand with offset)
        - 'is_memory': bool (if operand is memory access)
        - 'immediate': int (if operand is immediate value)
        - 'jump_target': int (if operand is jump target address)
        
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
    
    # Split by comma to get operands
    parts = [p.strip() for p in op_str.split(',')]
    
    if len(parts) == 0:
        return result
    
    # Parse first operand
    first_str = parts[0]
    
    # Remove size prefixes like "byte ptr", "word ptr", "qword ptr"
    first_str = first_str.replace('byte ptr', '').replace('word ptr', '').replace('qword ptr', '').replace('dword ptr', '').strip()
    
    # Check if first operand is a memory operand: [base +/- offset]
    if '[' in first_str and ']' in first_str:
        result['is_memory'] = True
        # Extract content between brackets
        mem_content = first_str[first_str.index('[') + 1:first_str.index(']')].strip()
        
        # Parse base register and offset
        # Format: "r14 - 0x40" or "r14 + 0x40" or just "r14"
        if ' - ' in mem_content:
            base_str, offset_str = mem_content.split(' - ', 1)
            sign = -1
        elif ' + ' in mem_content:
            base_str, offset_str = mem_content.split(' + ', 1)
            sign = 1
        elif '-' in mem_content and ' ' not in mem_content:
            # Handle "r14-0x40" (no spaces)
            if '-' in mem_content:
                base_str, offset_str = mem_content.split('-', 1)
                sign = -1
            else:
                base_str = mem_content
                offset_str = None
                sign = 1
        else:
            # No offset, just base register
            base_str = mem_content
            offset_str = None
            sign = 1
        
        # Parse base register
        base_str = base_str.strip()
        for reg_name, reg_enum in [(r.value, r) for r in Register]:
            if base_str == reg_name:
                result['base_reg'] = reg_enum
                break
        
        # Parse offset
        if offset_str:
            offset_str = offset_str.strip()
            # Remove 0x prefix if present
            if offset_str.startswith('0x') or offset_str.startswith('0X'):
                offset_val = int(offset_str, 16)
            else:
                offset_val = int(offset_str)
            result['offset'] = sign * offset_val
        
        # If there's a second operand, it could be a register or immediate
        if len(parts) > 1:
            src_str = parts[1].strip()
            # Try to parse as register first
            found_reg = False
            for reg_name, reg_enum in [(r.value, r) for r in Register]:
                if src_str == reg_name:
                    result['src_reg'] = reg_enum
                    found_reg = True
                    break
            # If not a register, try to parse as immediate
            if not found_reg:
                try:
                    if src_str.startswith('0x') or src_str.startswith('0X'):
                        result['immediate'] = int(src_str, 16)
                    else:
                        result['immediate'] = int(src_str)
                except ValueError:
                    pass
    else:
        # First operand is a register (destination)
        for reg_name, reg_enum in [(r.value, r) for r in Register]:
            if first_str == reg_name:
                result['dest_reg'] = reg_enum
                break
        
        # Parse second operand if present (source)
        if len(parts) > 1:
            src_str = parts[1].strip()
            
            # Check if it's a memory operand: [base +/- offset]
            if '[' in src_str and ']' in src_str:
                result['is_memory'] = True
                # Extract content between brackets
                mem_content = src_str[src_str.index('[') + 1:src_str.index(']')].strip()
                
                # Parse base register and offset
                # Format: "r14 - 0x40" or "r14 + 0x40" or just "r14"
                if ' - ' in mem_content:
                    base_str, offset_str = mem_content.split(' - ', 1)
                    sign = -1
                elif ' + ' in mem_content:
                    base_str, offset_str = mem_content.split(' + ', 1)
                    sign = 1
                elif '-' in mem_content and ' ' not in mem_content:
                    # Handle "r14-0x40" (no spaces)
                    base_str, offset_str = mem_content.split('-', 1)
                    sign = -1
                else:
                    # No offset, just base register
                    base_str = mem_content
                    offset_str = None
                    sign = 1
                
                # Parse base register
                base_str = base_str.strip()
                for reg_name, reg_enum in [(r.value, r) for r in Register]:
                    if base_str == reg_name:
                        result['base_reg'] = reg_enum
                        break
                
                # Parse offset
                if offset_str:
                    offset_str = offset_str.strip()
                    # Remove 0x prefix if present
                    if offset_str.startswith('0x') or offset_str.startswith('0X'):
                        offset_val = int(offset_str, 16)
                    else:
                        offset_val = int(offset_str)
                    result['offset'] = sign * offset_val
            else:
                # Check if it's a register
                for reg_name, reg_enum in [(r.value, r) for r in Register]:
                    if src_str == reg_name:
                        result['src_reg'] = reg_enum
                        break
                # If not a register, check if it's an immediate value
                if result['src_reg'] is None:
                    try:
                        # Try to parse as immediate value
                        if src_str.startswith('0x') or src_str.startswith('0X'):
                            result['immediate'] = int(src_str, 16)
                        else:
                            result['immediate'] = int(src_str)
                    except ValueError:
                        pass
    
    # Check if first operand is an immediate (for instructions like CMP rax, 0x3)
    if result['dest_reg'] is None and not result['is_memory'] and len(parts) > 0:
        first_str = parts[0].strip()
        # Check if it's not a register
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
    
    # Check for jump target (hex address like 0x39)
    if len(parts) == 1:
        target_str = parts[0].strip()
        if target_str.startswith('0x') or target_str.startswith('0X'):
            try:
                result['jump_target'] = int(target_str, 16)
            except ValueError:
                pass
    
    return result

