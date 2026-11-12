#!/usr/bin/env python3
"""测试 x86-64 基本块识别功能。"""

import pytest

from x86_64.cfg import identify_basic_blocks
from x86_64.disassembler import disassemble_hex, parse_operands


class TestIdentifyBasicBlocks:
    """测试 identify_basic_blocks 函数。"""

    def disasm_at(self, hex_code: str, base_addr: int = 0):
        """辅助函数：反汇编机器码。"""
        return disassemble_hex(hex_code, base_addr=base_addr)

    def get_jump_targets(self, instructions):
        """获取所有跳转目标（调试用）。"""
        targets = []
        for insn in instructions:
            ops = parse_operands(insn)
            if ops.get('jump_target') is not None:
                targets.append(ops['jump_target'])
        return targets

    def test_empty_instruction_list(self):
        """测试空指令列表。"""
        blocks = identify_basic_blocks([])
        assert blocks == []

    def test_linear_sequence_single_block(self):
        """测试直线代码序列（无跳转）应产生单个基本块。"""
        hex_code = "48c7c001000000 48c7c302000000 c3"
        instructions = self.disasm_at(hex_code, base_addr=0x00)

        blocks = identify_basic_blocks(instructions)

        assert len(blocks) == 1
        assert blocks[0].start_addr == 0x00
        assert blocks[0].is_jump_target is False

    def test_unconditional_jump_creates_blocks(self):
        """测试无条件跳转应产生多个基本块。"""
        # jmp 0x12 @ 0x07, 跳转目标是 0x12
        hex_code = "48c7c001000000 e906000000 48c7c302000000 909090 48c7c103000000"
        instructions = self.disasm_at(hex_code, base_addr=0x00)

        blocks = identify_basic_blocks(instructions)

        # 3 个基本块：0x00, 0x0c, 0x12
        assert len(blocks) == 3

        assert blocks[0].start_addr == 0x00
        assert blocks[0].is_jump_target is False
        assert blocks[0].instructions[-1].mnemonic == "jmp"

        assert blocks[1].start_addr == 0x0c
        assert blocks[1].is_jump_target is True

        assert blocks[2].start_addr == 0x12  # 跳转目标
        assert blocks[2].is_jump_target is True

    def test_conditional_jump_creates_blocks(self):
        """测试条件跳转应产生多个基本块。"""
        # jae 0x0f @ 0x0a (短跳转，偏移 0x03，从 0x0c 开始)
        hex_code = "48c7c001000000 4885c0 7303 48c7c302000000 90 48c7c103000000"
        instructions = self.disasm_at(hex_code, base_addr=0x00)

        blocks = identify_basic_blocks(instructions)

        assert len(blocks) == 3

        assert blocks[0].start_addr == 0x00
        assert blocks[0].is_jump_target is False

        assert blocks[1].start_addr == 0x0c
        assert blocks[1].is_jump_target is True

        assert blocks[2].start_addr == 0x0f  # 跳转目标
        assert blocks[2].is_jump_target is True

    def test_ret_creates_new_block(self):
        """测试 ret 后的指令应该开始新块。"""
        hex_code = "48c7c001000000 c3 48c7c302000000"
        instructions = self.disasm_at(hex_code, base_addr=0x00)

        blocks = identify_basic_blocks(instructions)

        assert len(blocks) == 2

        assert blocks[0].start_addr == 0x00
        assert blocks[0].is_jump_target is False
        assert blocks[0].instructions[-1].mnemonic == "ret"

        assert blocks[1].start_addr == 0x08
        assert blocks[1].is_jump_target is True

    def test_multiple_jump_targets_same_destination(self):
        """测试多个跳转到同一目标。"""
        # jmp 0x14 @ 0x00 (偏移 0x0f = 15)
        # jmp 0x14 @ 0x05 (偏移 0x0a = 10)
        hex_code = "e90f000000 e90a000000 909090 48c7c001000000 48c7c302000000"
        instructions = self.disasm_at(hex_code, base_addr=0x00)

        targets = self.get_jump_targets(instructions)
        assert targets == [0x14, 0x14]  # 两个 jmp 都到 0x14

        blocks = identify_basic_blocks(instructions)

        # 4 个基本块：0x00, 0x05, 0x0a, 0x14
        assert len(blocks) == 4

        block_starts = [b.start_addr for b in blocks]
        assert 0x00 in block_starts
        assert 0x05 in block_starts
        assert 0x0a in block_starts
        assert 0x14 in block_starts

        # 找到目标块
        target_blocks = [b for b in blocks if b.start_addr == 0x14]
        assert len(target_blocks) == 1
        assert target_blocks[0].is_jump_target is True

    def test_all_conditional_jump_types(self):
        """测试所有支持的条件跳转类型。"""
        jump_opcodes = {
            'jb': '72',
            'jae': '73',
            'je': '74',
            'jne': '75',
            'jl': '7c',
            'jle': '7e',
            'jg': '7f',
            'jge': '7d',
        }

        for mnemonic, opcode in jump_opcodes.items():
            # jcc 0x0f @ 0x07 (短跳转，偏移 0x06 = 6)
            hex_code = f"48c7c001000000 {opcode}06 48c7c302000000 90 48c7c103000000"
            instructions = self.disasm_at(hex_code, base_addr=0x00)

            targets = self.get_jump_targets(instructions)
            assert targets == [0x0f], f"{mnemonic}: targets = {targets}"

            blocks = identify_basic_blocks(instructions)

            # 条件跳转应该创建 3 个块
            assert len(blocks) == 3, f"Failed for {mnemonic}: got {len(blocks)} blocks, starts={[hex(b.start_addr) for b in blocks]}"
            assert blocks[0].end_addr == 0x09
            assert blocks[1].start_addr == 0x09
            assert blocks[2].start_addr == 0x0f

    def test_complex_control_flow(self):
        """测试复杂控制流（多个跳转和 ret）。"""
        # jae @ 0x0d 跳到 0x16, jmp @ 0x16 跳到 0x21
        hex_code = (
            "48c7c001000000"     # mov rax, 1 @ 0x00 (7)
            "483d00000000"        # cmp rax, 0 @ 0x07 (5)
            "7307"                # jae 0x16   @ 0x0c (2, 短跳)
            "48c7c302000000"      # mov rbx, 2 @ 0x0e (7)
            "eb09"                # jmp 0x21   @ 0x15 (2, 短跳)
            "c3"                  # ret        @ 0x17 (1)
            "48c7c103000000"      # mov rcx, 3 @ 0x18 (7)
            "c3"                  # ret        @ 0x1f (1)
        )
        instructions = self.disasm_at(hex_code, base_addr=0x00)

        blocks = identify_basic_blocks(instructions)

        # 5 个基本块：0x00, 0x0f (jae后), 0x16 (jae目标+jmp), 0x18 (jmp后), 0x19 (ret后)
        assert len(blocks) == 5
        block_starts = [b.start_addr for b in blocks]
        assert 0x00 in block_starts
        assert 0x0f in block_starts  # jae 后
        assert 0x16 in block_starts  # jae目标 (在指令中间)
        assert 0x18 in block_starts  # jmp 后
        assert 0x19 in block_starts  # ret 后 (0x18 + 1)

    def test_block_contains_correct_instructions(self):
        """测试基本块包含正确的指令。"""
        hex_code = "48c7c001000000 e906000000 48c7c302000000 909090 48c7c103000000"
        instructions = self.disasm_at(hex_code, base_addr=0x00)

        blocks = identify_basic_blocks(instructions)

        # 第一个块应该包含 mov 和 jmp
        assert len(blocks[0].instructions) == 2
        assert blocks[0].instructions[0].mnemonic == "mov"
        assert blocks[0].instructions[1].mnemonic == "jmp"

        # 第二个块应该包含 mov rbx（到 0x12 之前）
        assert blocks[1].start_addr == 0x0c
        assert blocks[1].end_addr == 0x12
        assert len(blocks[1].instructions) == 1
        assert blocks[1].instructions[0].mnemonic == "mov"

        # 第三个块应该从 0x12 开始
        assert blocks[2].start_addr == 0x12

    def test_is_jump_target_flag(self):
        """测试 is_jump_target 标志设置正确。"""
        hex_code = "e906000000 48c7c001000000 c3"
        instructions = self.disasm_at(hex_code, base_addr=0x00)

        blocks = identify_basic_blocks(instructions)

        # 第一个块是入口点，不是跳转目标
        assert blocks[0].is_jump_target is False

        # 其他块都是跳转目标
        assert blocks[1].is_jump_target is True
        assert blocks[2].is_jump_target is True

    def test_backward_jump(self):
        """测试向后跳转（循环）。"""
        # jl 0x08 @ 0x14 (短跳，偏移 -12)
        hex_code = (
            "48c7c000000000"     # mov rax, 0 @ 0x00 (7)
            "48c7c001000000"      # mov rax, 1 @ 0x07 (7, 循环开始)
            "483d0a000000"        # cmp rax, 10 @ 0x0e (5)
            "7cf2"                # jl 0x08    @ 0x13 (2, 向后跳)
            "c3"                  # ret        @ 0x15 (1)
        )
        instructions = self.disasm_at(hex_code, base_addr=0x00)

        targets = self.get_jump_targets(instructions)
        assert targets == [0x08]

        blocks = identify_basic_blocks(instructions)

        # 3 个基本块：0x00, 0x08, 0x16
        # 0x08 在 mov 指令中间，但仍会被识别为基本块起始
        assert len(blocks) == 3
        block_starts = [b.start_addr for b in blocks]
        assert 0x00 in block_starts
        assert 0x08 in block_starts
        assert 0x16 in block_starts

    def test_near_and_far_jumps(self):
        """测试短跳转和近跳转。"""
        # 短跳转 (8-bit offset)
        hex_short = "48c7c001000000 7205 48c7c302000000 90 48c7c103000000"
        instructions = self.disasm_at(hex_short, base_addr=0x00)
        blocks = identify_basic_blocks(instructions)
        assert len(blocks) == 3

        # 近跳转 (32-bit offset)
        # jmp 0x15 @ 0x07 (偏移 0x09)
        hex_near = "48c7c001000000 0f8209000000 48c7c302000000 909090909090909090 48c7c103000000"
        instructions = self.disasm_at(hex_near, base_addr=0x00)
        blocks = identify_basic_blocks(instructions)
        assert len(blocks) == 3

    def test_fallthrough_without_target(self):
        """测试没有明确目标的跳转后的 fallthrough。"""
        # 间接跳转（通过寄存器）- 无法静态确定目标
        # 但跳转后的指令仍应开始新块
        hex_code = "48c7c001000000 ff20 c3"  # mov @ 0x00, jmp rax @ 0x07, ret @ 0x09
        instructions = self.disasm_at(hex_code, base_addr=0x00)

        blocks = identify_basic_blocks(instructions)

        # 应该有 2 个块：jmp 和 jmp 后 (0x09)
        assert len(blocks) == 2
        assert blocks[0].instructions[-1].mnemonic == "jmp"
        assert blocks[1].start_addr == 0x09

    def test_concrete_example_from_compiler(self):
        """测试一个来自编译器的真实例子。"""
        # 模拟编译器输出：检查标签，跳转
        hex_code = (
            "488b46f8"            # mov rax, [rsi-8] @ 0x00 (4)
            "4839c0"              # cmp rax, rax      @ 0x04 (3)
            "7503"                # jne 0x0c          @ 0x07 (2, 跳到 0x0c)
            "c3"                  # ret               @ 0x09 (1)
            "90"                  # nop               @ 0x0a (1)
            "48c7c001000000"      # mov rax, 1        @ 0x0b (7, jne target 实际在 0x0c)
            "c3"                  # ret               @ 0x12 (1)
        )
        instructions = self.disasm_at(hex_code, base_addr=0x00)

        blocks = identify_basic_blocks(instructions)

        # 4 个基本块：0x00, 0x09 (ret后), 0x0a (nop+部分mov), 0x0c (jne target+部分mov)
        # 注意：0x0c 在 mov 指令中间，所以 0x0a 的块包含 nop，0x0c 开始新块
        assert len(blocks) == 4

        assert blocks[0].start_addr == 0x00
        assert blocks[0].instructions[-1].mnemonic == "jne"

        assert blocks[1].start_addr == 0x09
        assert blocks[1].instructions[0].mnemonic == "ret"

        assert blocks[2].start_addr == 0x0a  # nop (ret后)

        assert blocks[3].start_addr == 0x0c  # jne target
        assert blocks[3].is_jump_target is True

    def test_jump_instruction_variants(self):
        """测试不同类型的跳转指令。"""
        # 测试所有支持的跳转助记符
        jump_mnemonics = [
            ('jmp', 'e902000000'),      # 近跳转
            ('jb', '7202'),              # 短跳转 jb
            ('jae', '7302'),             # 短跳转 jae
            ('je', '7402'),              # 短跳转 je
            ('jne', '7502'),             # 短跳转 jne
            ('jl', '7c02'),              # 短跳转 jl
            ('jle', '7e02'),             # 短跳转 jle
            ('jg', '7f02'),              # 短跳转 jg
            ('jge', '7d02'),             # 短跳转 jge
        ]

        for mnemonic, opcode in jump_mnemonics:
            # 指令序列 + 跳转 + 目标
            if mnemonic == 'jmp':
                hex_code = f"48c7c001000000 {opcode} 48c7c302000000 c3"
            else:
                hex_code = f"48c7c001000000 4885c0 {opcode} 48c7c302000000 c3"

            instructions = self.disasm_at(hex_code, base_addr=0x00)
            blocks = identify_basic_blocks(instructions)

            # 每种跳转都应该创建多个基本块
            assert len(blocks) >= 2, f"{mnemonic} should create at least 2 blocks, got {len(blocks)}"

    def test_real_compiler_output_complex_function(self):
        """测试来自真实编译器的复杂函数输出。

        这是一个实际的 Go 编译器生成的 x86-64 代码，包含：
        - 多个条件分支 (jb, jae)
        - 多个 ret 指令
        - 复杂的控制流
        - 256位算术运算 (adc 指令)
        """
        hex_code = (
            "4d8b75384d0375304d8b7d10498b45704883f80372234883e80349894570"
            "498b45304883f8407222483d21800000732b4d8b75384901c6eb3341c685"
            "e00000000c49c7452800000000c341c685e00000000e49c7452800000000"
            "c341c685e00000000f49c7452800000000c3498b46c0490346e0498b4ec8"
            "49134ee8498b56d0491356f0498b5ed849135ef8498946c049894ec8498"
            "956d049895ed841c685e00000000249c74528fcffffffc3"
        )
        instructions = self.disasm_at(hex_code, base_addr=0x00)

        blocks = identify_basic_blocks(instructions)

        # 应该有 8 个基本块：
        # 0x00: 入口块 (到 jb @ 0x14)
        # 0x16: jb 后 (到 jb @ 0x26)
        # 0x28: jb 后 (到 jae @ 0x2e)
        # 0x30: jae 后 (到 jmp @ 0x37)
        # 0x39: 第一个 jb 目标 (ret)
        # 0x4a: 第二个 jb 目标 (ret)
        # 0x5b: jae 目标 (ret)
        # 0x6c: jmp 目标 + 最后的 ret
        assert len(blocks) == 8

        # 验证基本块的起始地址
        block_starts = [b.start_addr for b in blocks]
        expected_starts = [0x00, 0x16, 0x28, 0x30, 0x39, 0x4a, 0x5b, 0x6c]
        for expected in expected_starts:
            assert expected in block_starts, f"Expected block at 0x{expected:x}"

        # 第一个块包含初始化代码和第一个条件跳转
        assert blocks[0].start_addr == 0x00
        assert blocks[0].is_jump_target is False  # 入口块
        assert len(blocks[0].instructions) == 6
        assert blocks[0].instructions[-1].mnemonic == "jb"

        # 最后一个块包含 adc 序列和 ret
        last_block = next(b for b in blocks if b.start_addr == 0x6c)
        assert last_block.is_jump_target is True
        assert last_block.instructions[-1].mnemonic == "ret"

        # 验证包含 adc 的块（256位加法）
        adc_instructions = [insn for insn in last_block.instructions if insn.mnemonic == "adc"]
        assert len(adc_instructions) == 3, "Should have 3 adc instructions for 256-bit addition"
