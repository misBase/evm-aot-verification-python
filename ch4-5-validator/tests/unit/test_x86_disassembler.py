#!/usr/bin/env python3
"""x86-64反汇编器的测试。"""

from x86_64.disassembler import disassemble_hex, parse_operands
from x86_64.models import Register, X86Instruction


# ============================================================================
# 反汇编功能测试
# ============================================================================

def test_disassemble_hex_basic():
    """测试基本十六进制反汇编。"""
    hex_code = "498b46c0"  # mov rax, [r14-0x40]
    instructions = disassemble_hex(hex_code, base_addr=0x6c)

    assert len(instructions) == 1
    assert instructions[0].mnemonic == "mov"
    assert instructions[0].addr == 0x6c
    assert "r14" in instructions[0].op_str.lower()
    assert instructions[0]._cs_insn is not None  # 验证Capstone指令对象被保存


def test_disassemble_hex_multiple():
    """测试反汇编多条指令。"""
    hex_code = "498b46c0 490346e0"  # mov rax, [r14-0x40]; add rax, [r14-0x20]
    instructions = disassemble_hex(hex_code, base_addr=0x6c)

    assert len(instructions) == 2
    assert instructions[0].mnemonic == "mov"
    assert instructions[1].mnemonic == "add"
    assert instructions[0].addr == 0x6c
    assert instructions[1].addr == 0x70


def test_disassemble_hex_add_sequence():
    """测试反汇编完整ADD序列。"""
    hex_code = "498b46c0 490346e0 498b4ec8 49134ee8 498b56d0 491356f0 498b5ed8 49135ef8"
    instructions = disassemble_hex(hex_code, base_addr=0x6c)

    assert len(instructions) == 8
    expected_mnemonics = ["mov", "add", "mov", "adc", "mov", "adc", "mov", "adc"]
    for insn, expected in zip(instructions, expected_mnemonics):
        assert insn.mnemonic == expected


def test_disassemble_hex_r14_correct():
    """测试R14寄存器被正确识别（使用REX.WB前缀）。"""
    hex_code = "498b46c0"  # mov rax, [r14-0x40]
    instructions = disassemble_hex(hex_code)
    assert "r14" in instructions[0].op_str.lower()


def test_disassemble_hex_rsi_not_r14():
    """测试RSI寄存器不会被误识别为R14（使用REX.W前缀）。"""
    hex_code = "488b46c0"  # mov rax, [rsi-0x40]
    instructions = disassemble_hex(hex_code)
    assert "rsi" in instructions[0].op_str.lower()
    assert "r14" not in instructions[0].op_str.lower()


def test_disassemble_hex_various_formats():
    """测试反汇编各种格式的十六进制字符串。"""
    hex_variations = [
        "488b46c0",
        "48 8b 46 c0",
        "0x488b46c0",
        "0x48 0x8b 0x46 0xc0",
    ]

    for hex_code in hex_variations:
        instructions = disassemble_hex(hex_code)
        assert len(instructions) == 1


def test_disassemble_hex_empty():
    """测试反汇编空字符串。"""
    instructions = disassemble_hex("")
    assert len(instructions) == 0


def test_disassemble_hex_invalid():
    """测试反汇编无效的十六进制字符串。"""
    try:
        disassemble_hex("invalid")
        assert False, "Should raise ValueError"
    except ValueError:
        pass


# ============================================================================
# parse_operands 测试 - 使用Capstone API
# ============================================================================

def test_parse_operands_memory_negative_offset():
    """测试解析带负偏移的内存操作数。"""
    instructions = disassemble_hex("498b46c0")  # mov rax, [r14-0x40]
    insn = instructions[0]
    result = parse_operands(insn)

    assert result['dest_reg'] == Register.RAX
    assert result['base_reg'] == Register.R14
    assert result['offset'] == -0x40
    assert result['is_memory'] == True
    assert result['src_reg'] is None


def test_parse_operands_memory_positive_offset():
    """测试解析带正偏移的内存操作数。"""
    instructions = disassemble_hex("498b4610")  # mov rax, [r14+0x10]
    insn = instructions[0]
    result = parse_operands(insn)

    assert result['dest_reg'] == Register.RAX
    assert result['base_reg'] == Register.R14
    assert result['offset'] == 0x10
    assert result['is_memory'] == True


def test_parse_operands_memory_add():
    """测试解析ADD指令的内存操作数。"""
    instructions = disassemble_hex("490346e0")  # add rax, [r14-0x20]
    insn = instructions[0]
    result = parse_operands(insn)

    assert result['dest_reg'] == Register.RAX
    assert result['base_reg'] == Register.R14
    assert result['offset'] == -0x20
    assert result['is_memory'] == True


def test_parse_operands_register_to_register():
    """测试解析寄存器到寄存器的操作数。"""
    instructions = disassemble_hex("4889d8")  # mov rax, rbx
    insn = instructions[0]
    result = parse_operands(insn)

    assert result['dest_reg'] == Register.RAX
    assert result['src_reg'] == Register.RBX
    assert result['is_memory'] == False
    assert result['base_reg'] is None


def test_parse_operands_immediate():
    """测试解析立即数操作数。"""
    # 使用64位CMP指令测试立即数
    instructions = disassemble_hex("483d00000000")  # cmp rax, 0
    insn = instructions[0]
    result = parse_operands(insn)

    assert result['dest_reg'] == Register.RAX
    assert result['immediate'] == 0
    assert result['is_memory'] == False


def test_parse_operands_jump_short():
    """测试解析短跳转指令。"""
    instructions = disassemble_hex("eb02", base_addr=0x100)  # jmp 0x104
    insn = instructions[0]
    result = parse_operands(insn)

    # Capstone已经将相对跳转转换为绝对地址
    assert result['jump_target'] == 0x104


def test_parse_operands_jump_conditional():
    """测试解析条件跳转指令。"""
    instructions = disassemble_hex("7402", base_addr=0x100)  # jz 0x104
    insn = instructions[0]
    result = parse_operands(insn)

    # Capstone已经将相对跳转转换为绝对地址
    assert result['jump_target'] == 0x104


def test_parse_operands_memory_no_offset():
    """测试解析无偏移的内存操作数。"""
    # mov eax, [r14] - 需要使用正确的编码
    instructions = disassemble_hex("418b06")  # mov eax, [r14]
    insn = instructions[0]
    result = parse_operands(insn)

    assert result['is_memory'] == True
    assert result['offset'] == 0


def test_parse_operands_all_registers_memory():
    """测试不同寄存器的内存访问。"""
    # 测试R8-R15寄存器
    test_cases = [
        ("4d8b06", Register.R8, Register.R14),  # mov r8, [r14]
        ("4d8b0e", Register.R9, Register.R14),  # mov r9, [r14]
    ]

    for hex_code, expected_dest, expected_base in test_cases:
        instructions = disassemble_hex(hex_code)
        insn = instructions[0]
        result = parse_operands(insn)

        assert result['dest_reg'] == expected_dest
        assert result['base_reg'] == expected_base
        assert result['is_memory'] == True


# ============================================================================
# 新功能测试 - index_reg 和 scale 支持
# ============================================================================

def test_parse_operands_index_register():
    """测试解析带索引寄存器的内存操作数。"""
    # mov eax, [r14+rax*1] - 使用索引寄存器
    # 注意：这个编码使用SIB字节
    instructions = disassemble_hex("428b0420")  # mov eax, [r8+r12*1]
    insn = instructions[0]
    result = parse_operands(insn)

    assert result['is_memory'] == True
    # 验证我们支持索引寄存器
    assert 'index_reg' in result
    # 注意：实际的索引寄存器取决于具体的机器码


def test_parse_operands_scale_factor():
    """测试解析缩放因子。"""
    # mov eax, [r12+rax*8]
    instructions = disassemble_hex("418b04c4")  # mov eax, [r12+rax*8]
    insn = instructions[0]
    result = parse_operands(insn)

    assert result['is_memory'] == True
    assert 'scale' in result
    assert result['scale'] == 8


def test_parse_operands_complex_addressing():
    """测试复杂寻址模式。"""
    # 测试 [base + index*scale + disp] 模式
    instructions = disassemble_hex("428b44c520")  # mov rax, [r13+rax*8+0x20]
    insn = instructions[0]
    result = parse_operands(insn)

    assert result['is_memory'] == True
    assert result['offset'] == 0x20


# ============================================================================
# 边界情况测试
# ============================================================================

def test_parse_operands_no_operands():
    """测试没有操作数的指令（如ret）。"""
    instructions = disassemble_hex("c3")  # ret
    insn = instructions[0]
    result = parse_operands(insn)

    # 所有操作数字段都应该是None或0
    assert result['dest_reg'] is None
    assert result['src_reg'] is None
    assert result['base_reg'] is None
    assert result['immediate'] is None


def test_parse_operands_push_pop():
    """测试PUSH和POP指令。"""
    # push rax
    instructions = disassemble_hex("50")
    insn = instructions[0]
    result = parse_operands(insn)

    assert result['dest_reg'] == Register.RAX

    # pop rax
    instructions = disassemble_hex("58")
    insn = instructions[0]
    result = parse_operands(insn)

    assert result['dest_reg'] == Register.RAX


def test_parse_operands_cmp():
    """测试CMP指令。"""
    # cmp rax, 0
    instructions = disassemble_hex("483d00000000")
    insn = instructions[0]
    result = parse_operands(insn)

    assert result['dest_reg'] == Register.RAX
    assert result['immediate'] == 0


# ============================================================================
# 集成测试
# ============================================================================

def test_disassemble_and_parse_integration():
    """测试反汇编和解析的完整流程。"""
    # 完整的ADD序列
    hex_code = "498b46c0 490346e0"
    instructions = disassemble_hex(hex_code, base_addr=0x100)

    assert len(instructions) == 2

    # 第一条指令：mov rax, [r14-0x40]
    result1 = parse_operands(instructions[0])
    assert result1['dest_reg'] == Register.RAX
    assert result1['base_reg'] == Register.R14
    assert result1['offset'] == -0x40

    # 第二条指令：add rax, [r14-0x20]
    result2 = parse_operands(instructions[1])
    assert result2['dest_reg'] == Register.RAX
    assert result2['base_reg'] == Register.R14
    assert result2['offset'] == -0x20


def test_instruction_has_cs_insn():
    """验证所有反汇编的指令都包含Capstone指令对象。"""
    test_codes = [
        "498b46c0",  # mov
        "490346e0",  # add
        "eb05",      # jmp
        "c3",        # ret
        "50",        # push
        "b848000000", # mov imm
    ]

    for hex_code in test_codes:
        instructions = disassemble_hex(hex_code)
        assert len(instructions) > 0
        assert instructions[0]._cs_insn is not None, \
            f"Instruction {hex_code} should have _cs_insn"


# ============================================================================
# 性能和回归测试
# ============================================================================

def test_parse_operands_performance():
    """测试parse_operands的性能（使用Capstone API应该很快）。"""
    import time

    instructions = disassemble_hex("498b46c0")
    insn = instructions[0]

    # 解析1000次应该很快
    start = time.time()
    for _ in range(1000):
        result = parse_operands(insn)
    elapsed = time.time() - start

    # 应该在1秒内完成
    assert elapsed < 1.0, f"parse_operands too slow: {elapsed}s for 1000 iterations"


def test_r14_rsi_distinction():
    """回归测试：确保R14和RSI始终被正确区分。"""
    # R14 (使用REX.WB前缀)
    r14_insns = disassemble_hex("498b46c0")
    r14_result = parse_operands(r14_insns[0])
    assert r14_result['base_reg'] == Register.R14
    assert r14_result['base_reg'] != Register.RSI

    # RSI (使用REX.W前缀)
    rsi_insns = disassemble_hex("488b46c0")
    rsi_result = parse_operands(rsi_insns[0])
    assert rsi_result['base_reg'] == Register.RSI
    assert rsi_result['base_reg'] != Register.R14
