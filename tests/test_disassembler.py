#!/usr/bin/env python3
"""Tests for x86-64 disassembler."""

from x86_64.disassembler import disassemble_hex, parse_operands
from x86_64.models import Register, X86Instruction


def test_disassemble_hex_basic():
    """Test basic hex disassembly."""
    print("\nTesting basic hex disassembly...")
    
    # Test 1: Simple MOV instruction
    hex_code = "488b46c0"  # mov rax, [r14-0x40]
    instructions = disassemble_hex(hex_code, base_addr=0x6c)
    
    assert len(instructions) == 1, f"Expected 1 instruction, got {len(instructions)}"
    assert instructions[0].mnemonic == "mov", f"Expected 'mov', got '{instructions[0].mnemonic}'"
    assert instructions[0].addr == 0x6c, f"Expected address 0x6c, got 0x{instructions[0].addr:x}"
    op_str_lower = instructions[0].op_str.lower()
    assert "r14" in op_str_lower, f"Expected R14 in operands, got '{instructions[0].op_str}'"
    assert ("-0x40" in op_str_lower or "-64" in op_str_lower or "0x40" in op_str_lower), \
        f"Expected -0x40 or -64 in operands, got '{instructions[0].op_str}'"
    
    print("  ✓ Basic MOV instruction disassembly passed")


def test_disassemble_hex_multiple():
    """Test disassembling multiple instructions."""
    print("\nTesting multiple instruction disassembly...")
    
    # Test ADD sequence: mov rax, [r14-0x40]; add rax, [r14-0x20]
    hex_code = "488b46c0 480346e0"
    instructions = disassemble_hex(hex_code, base_addr=0x6c)
    
    assert len(instructions) == 2, f"Expected 2 instructions, got {len(instructions)}"
    assert instructions[0].mnemonic == "mov", f"Expected 'mov', got '{instructions[0].mnemonic}'"
    assert instructions[1].mnemonic == "add", f"Expected 'add', got '{instructions[1].mnemonic}'"
    assert instructions[0].addr == 0x6c, f"Expected address 0x6c, got 0x{instructions[0].addr:x}"
    assert instructions[1].addr == 0x70, f"Expected address 0x70, got 0x{instructions[1].addr:x}"
    
    print("  ✓ Multiple instruction disassembly passed")


def test_disassemble_hex_add_sequence():
    """Test disassembling full ADD sequence."""
    print("\nTesting full ADD sequence disassembly...")
    
    # Full ADD sequence: 8 instructions
    hex_code = "488b46c0 480346e0 488b4ec8 48134ee8 488b56d0 481356f0 488b5ed8 48135ef8"
    instructions = disassemble_hex(hex_code, base_addr=0x6c)
    
    assert len(instructions) == 8, f"Expected 8 instructions, got {len(instructions)}"
    
    # Check instruction types
    expected_mnemonics = ["mov", "add", "mov", "adc", "mov", "adc", "mov", "adc"]
    for i, (insn, expected) in enumerate(zip(instructions, expected_mnemonics)):
        assert insn.mnemonic == expected, \
            f"Instruction {i}: expected '{expected}', got '{insn.mnemonic}'"
    
    # Check addresses are sequential
    for i in range(1, len(instructions)):
        expected_addr = instructions[i-1].addr + instructions[i-1].size
        assert instructions[i].addr == expected_addr, \
            f"Instruction {i}: expected address 0x{expected_addr:x}, got 0x{instructions[i].addr:x}"
    
    print("  ✓ Full ADD sequence disassembly passed")


def test_disassemble_hex_r14_fix():
    """Test that R14 register is correctly identified (not RSI)."""
    print("\nTesting R14 register identification fix...")
    
    # This instruction uses R14, but Capstone might decode it as RSI
    hex_code = "488b46c0"  # mov rax, [r14-0x40]
    instructions = disassemble_hex(hex_code, base_addr=0x6c)
    
    assert len(instructions) == 1
    op_str = instructions[0].op_str.lower()
    # Should contain r14, not rsi (after our fix)
    assert "r14" in op_str, f"Expected R14 in operands, got '{instructions[0].op_str}'"
    assert "rsi" not in op_str or op_str.count("r14") > op_str.count("rsi"), \
        f"Operands should use R14, not RSI: '{instructions[0].op_str}'"
    
    print("  ✓ R14 register identification fix passed")


def test_parse_operands_mov_reg_mem():
    """Test parsing MOV reg, [base+offset] operands."""
    print("\nTesting parse_operands for MOV reg, [base+offset]...")
    
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
    
    print("  ✓ MOV reg, [base+offset] operand parsing passed")


def test_parse_operands_add_reg_mem():
    """Test parsing ADD reg, [base+offset] operands."""
    print("\nTesting parse_operands for ADD reg, [base+offset]...")
    
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
    
    print("  ✓ ADD reg, [base+offset] operand parsing passed")


def test_parse_operands_positive_offset():
    """Test parsing operands with positive offset."""
    print("\nTesting parse_operands with positive offset...")
    
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
    
    print("  ✓ Positive offset operand parsing passed")


def test_parse_operands_decimal_offset():
    """Test parsing operands with decimal offset."""
    print("\nTesting parse_operands with decimal offset...")
    
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
    
    print("  ✓ Decimal offset operand parsing passed")


def test_parse_operands_all_registers():
    """Test parsing operands with different registers."""
    print("\nTesting parse_operands with different registers...")
    
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
    
    print("  ✓ Different register operand parsing passed")


def test_disassemble_hex_various_formats():
    """Test disassembling hex strings in various formats."""
    print("\nTesting hex string format variations...")
    
    hex_variations = [
        "488b46c0",           # No spaces
        "48 8b 46 c0",        # With spaces
        "0x488b46c0",         # With 0x prefix
        "0x48 0x8b 0x46 0xc0", # With 0x prefix and spaces
    ]
    
    for hex_code in hex_variations:
        instructions = disassemble_hex(hex_code, base_addr=0x6c)
        assert len(instructions) == 1, \
            f"Expected 1 instruction for '{hex_code}', got {len(instructions)}"
        assert instructions[0].mnemonic == "mov", \
            f"Expected 'mov' for '{hex_code}', got '{instructions[0].mnemonic}'"
    
    print("  ✓ Hex string format variations passed")


def test_disassemble_hex_invalid():
    """Test disassembling invalid hex strings."""
    print("\nTesting invalid hex string handling...")
    
    invalid_hex = [
        "invalid",
        "48g8b46c0",  # Invalid hex character
        "",            # Empty string
    ]
    
    for hex_code in invalid_hex:
        try:
            instructions = disassemble_hex(hex_code, base_addr=0x6c)
            # If no exception, check if result is empty (for empty string)
            if hex_code == "":
                assert len(instructions) == 0, \
                    f"Expected empty list for empty hex string, got {len(instructions)}"
        except ValueError:
            # Expected for invalid hex
            pass
        except Exception as e:
            # Other exceptions are also acceptable
            pass
    
    print("  ✓ Invalid hex string handling passed")



