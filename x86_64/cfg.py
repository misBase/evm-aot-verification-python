"""
x86-64 基本块识别。

本模块为 x86-64 程序提供基本块识别功能。
"""

from typing import List, Set
from .models import X86Block, X86Instruction
from .disassembler import parse_operands


def identify_basic_blocks(instructions: List[X86Instruction]) -> List[X86Block]:
    """从指令序列中识别基本块。

    基本块边界：
    - 开始：程序入口、跳转目标、ret后的指令
    - 结束：jmp、条件跳转（jb/jae）、ret

    Args:
        instructions: x86-64指令列表

    Returns:
        X86Block对象列表
    """
    if not instructions:
        return []

    # 查找块起始地址
    block_starts: Set[int] = {instructions[0].addr}  # 程序入口

    # 查找跳转目标和ret后的指令
    for i, insn in enumerate(instructions):
        mnemonic = insn.mnemonic.lower()

        if mnemonic in ['jmp', 'jb', 'jae', 'je', 'jne', 'jl', 'jle', 'jg', 'jge']:
            # 跳转指令：提取目标
            operands = parse_operands(insn)
            target = operands.get('jump_target')
            if target is not None:
                block_starts.add(target)

            # 跳转后的指令也是块起始（顺序执行）
            if i + 1 < len(instructions):
                block_starts.add(instructions[i + 1].addr)

        elif mnemonic == 'ret':
            # ret后的指令是块起始
            if i + 1 < len(instructions):
                block_starts.add(instructions[i + 1].addr)

    # 排序块起始地址
    sorted_starts = sorted(block_starts)

    # 创建块
    blocks = []
    for i, start_addr in enumerate(sorted_starts):
        # 查找结束地址（下一个块起始或程序结束）
        if i + 1 < len(sorted_starts):
            end_addr = sorted_starts[i + 1]
        else:
            # 最后一个块：在最后一条指令处结束
            last_insn = instructions[-1]
            end_addr = last_insn.addr + last_insn.size

        # 收集此块中的指令
        block_instructions = []
        for insn in instructions:
            if start_addr <= insn.addr < end_addr:
                block_instructions.append(insn)

        if block_instructions:
            block = X86Block(
                start_addr=start_addr,
                end_addr=end_addr,
                instructions=block_instructions,
                is_jump_target=(start_addr != instructions[0].addr)  # 除第一个外都是跳转目标
            )
            blocks.append(block)

    return blocks
