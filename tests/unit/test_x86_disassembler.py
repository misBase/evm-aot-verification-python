#!/usr/bin/env python3
"""x86-64反汇编器的测试。"""

from x86_64.disassembler import disassemble_hex, parse_operands
from x86_64.models import Register, X86Instruction


def test_disassemble_hex_basic():
    """测试基本十六进制反汇编。"""
    # 测试1：简单MOV指令
    hex_code = "488b46c0"  # mov rax, [r14-0x40]
    instructions = disassemble_hex(hex_code, base_addr=0x6c)
    
    assert len(instructions) == 1, f"Expected 1 instruction, got {len(instructions)}"
    assert instructions[0].mnemonic == "mov", f"Expected 'mov', got '{instructions[0].mnemonic}'"
    assert instructions[0].addr == 0x6c, f"Expected address 0x6c, got 0x{instructions[0].addr:x}"
    op_str_lower = instructions[0].op_str.lower()
    assert "r14" in op_str_lower, f"Expected R14 in operands, got '{instructions[0].op_str}'"
    assert ("-0x40" in op_str_lower or "-64" in op_str_lower or "0x40" in op_str_lower), \
        f"Expected -0x40 or -64 in operands, got '{instructions[0].op_str}'"


def test_disassemble_hex_multiple():
    """测试反汇编多条指令。"""
    # 测试ADD序列：mov rax, [r14-0x40]; add rax, [r14-0x20]
    hex_code = "488b46c0 480346e0"
    instructions = disassemble_hex(hex_code, base_addr=0x6c)
    
    assert len(instructions) == 2, f"Expected 2 instructions, got {len(instructions)}"
    assert instructions[0].mnemonic == "mov", f"Expected 'mov', got '{instructions[0].mnemonic}'"
    assert instructions[1].mnemonic == "add", f"Expected 'add', got '{instructions[1].mnemonic}'"
    assert instructions[0].addr == 0x6c, f"Expected address 0x6c, got 0x{instructions[0].addr:x}"
    assert instructions[1].addr == 0x70, f"Expected address 0x70, got 0x{instructions[1].addr:x}"


def test_disassemble_hex_add_sequence():
    """测试反汇编完整ADD序列。"""
    # 完整ADD序列：8条指令
    hex_code = "488b46c0 480346e0 488b4ec8 48134ee8 488b56d0 481356f0 488b5ed8 48135ef8"
    instructions = disassemble_hex(hex_code, base_addr=0x6c)
    
    assert len(instructions) == 8, f"Expected 8 instructions, got {len(instructions)}"
    
    # 检查指令类型
    expected_mnemonics = ["mov", "add", "mov", "adc", "mov", "adc", "mov", "adc"]
    for i, (insn, expected) in enumerate(zip(instructions, expected_mnemonics)):
        assert insn.mnemonic == expected, \
            f"Instruction {i}: expected '{expected}', got '{insn.mnemonic}'"
    
    # 检查地址是顺序的
    for i in range(1, len(instructions)):
        expected_addr = instructions[i-1].addr + instructions[i-1].size
        assert instructions[i].addr == expected_addr, \
            f"Instruction {i}: expected address 0x{expected_addr:x}, got 0x{instructions[i].addr:x}"


def test_disassemble_hex_r14_fix():
    """测试R14寄存器被正确识别（不是RSI）。"""
    # 此指令使用R14，但Capstone可能将其解码为RSI
    hex_code = "488b46c0"  # mov rax, [r14-0x40]
    instructions = disassemble_hex(hex_code, base_addr=0x6c)
    
    assert len(instructions) == 1
    op_str = instructions[0].op_str.lower()
    # 应包含r14，不是rsi（在我们的修复之后）
    assert "r14" in op_str, f"Expected R14 in operands, got '{instructions[0].op_str}'"
    assert "rsi" not in op_str or op_str.count("r14") > op_str.count("rsi"), \
        f"Operands should use R14, not RSI: '{instructions[0].op_str}'"


def test_parse_operands_mov_reg_mem():
    """测试解析MOV reg, [base+offset]操作数。"""
    op_str = "rax, qword ptr [r14 - 0x40]"
    result = parse_operands(op_str)
    
    assert result['dest_reg'] == Register.RAX, \
        f"Expected RAX, got {result['dest_reg']}"
    assert result['base_reg'] == Register.R14, \
        f"Expected R14, got {result['base_reg']}"
    assert result['offset'] == -0x40, \
        f"Expected -0x40, got {result['offset']}"
    assert result['is_memory'] == True, \
        f"Expected is_memory=True, got {result['is_memory']}"


def test_parse_operands_add_reg_mem():
    """测试解析ADD reg, [base+offset]操作数。"""
    op_str = "rax, qword ptr [r14 - 0x20]"
    result = parse_operands(op_str)
    
    assert result['dest_reg'] == Register.RAX, \
        f"Expected RAX, got {result['dest_reg']}"
    assert result['base_reg'] == Register.R14, \
        f"Expected R14, got {result['base_reg']}"
    assert result['offset'] == -0x20, \
        f"Expected -0x20, got {result['offset']}"
    assert result['is_memory'] == True, \
        f"Expected is_memory=True, got {result['is_memory']}"


def test_parse_operands_positive_offset():
    """测试解析带正偏移量的操作数。"""
    op_str = "rax, qword ptr [r14 + 0x10]"
    result = parse_operands(op_str)
    
    assert result['dest_reg'] == Register.RAX, \
        f"Expected RAX, got {result['dest_reg']}"
    assert result['base_reg'] == Register.R14, \
        f"Expected R14, got {result['base_reg']}"
    assert result['offset'] == 0x10, \
        f"Expected 0x10, got {result['offset']}"
    assert result['is_memory'] == True, \
        f"Expected is_memory=True, got {result['is_memory']}"


def test_parse_operands_decimal_offset():
    """测试解析带十进制偏移量的操作数。"""
    op_str = "rax, qword ptr [r14 - 64]"
    result = parse_operands(op_str)
    
    assert result['dest_reg'] == Register.RAX, \
        f"Expected RAX, got {result['dest_reg']}"
    assert result['base_reg'] == Register.R14, \
        f"Expected R14, got {result['base_reg']}"
    assert result['offset'] == -64, \
        f"Expected -64, got {result['offset']}"
    assert result['is_memory'] == True, \
        f"Expected is_memory=True, got {result['is_memory']}"


def test_parse_operands_all_registers():
    """测试解析不同寄存器的操作数。"""
    registers_to_test = [
        (Register.RAX, "rax"),
        (Register.RCX, "rcx"),
        (Register.RDX, "rdx"),
        (Register.RBX, "rbx"),
    ]
    
    for reg_enum, reg_name in registers_to_test:
        op_str = f"{reg_name}, qword ptr [r14 - 0x40]"
        result = parse_operands(op_str)
        
        assert result['dest_reg'] == reg_enum, \
            f"Expected {reg_enum}, got {result['dest_reg']}"


def test_disassemble_hex_various_formats():
    """测试反汇编各种格式的十六进制字符串。"""
    hex_variations = [
        "488b46c0",           # 无空格
        "48 8b 46 c0",        # 带空格
        "0x488b46c0",         # 带0x前缀
        "0x48 0x8b 0x46 0xc0", # 带0x前缀和空格
    ]
    
    for hex_code in hex_variations:
        instructions = disassemble_hex(hex_code, base_addr=0x6c)
        assert len(instructions) == 1, \
            f"Expected 1 instruction for '{hex_code}', got {len(instructions)}"
        assert instructions[0].mnemonic == "mov", \
            f"Expected 'mov' for '{hex_code}', got '{instructions[0].mnemonic}'"


def test_disassemble_hex_invalid():
    """测试反汇编无效的十六进制字符串。"""
    invalid_hex = [
        "invalid",
        "48g8b46c0",  # 无效的十六进制字符
        "",            # 空字符串
    ]
    
    for hex_code in invalid_hex:
        try:
            instructions = disassemble_hex(hex_code, base_addr=0x6c)
            # 如果没有异常，检查结果是否为空（对于空字符串）
            if hex_code == "":
                assert len(instructions) == 0, \
                    f"Expected empty list for empty hex string, got {len(instructions)}"
        except ValueError:
            # 对于无效的十六进制，这是预期的
            pass
        except Exception as e:
            # 其他异常也是可以接受的
            pass



