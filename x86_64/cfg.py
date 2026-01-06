"""
x86-64控制流图（CFG）构建和路径分析。

本模块为x86-64程序提供基本块识别和CFG构建。
"""

from typing import List, Dict, Set, Tuple, Optional
from z3 import BoolRef, BoolVal, And, Or, Not, BitVecVal
from .models import X86Block, X86Instruction
from .disassembler import parse_operands


class X86CFG:
    """x86-64程序的控制流图。"""
    
    def __init__(self, blocks: List[X86Block]):
        """从块初始化CFG。
        
        Args:
            blocks: x86-64块列表
        """
        self.blocks = blocks
        self.blocks_by_addr: Dict[int, X86Block] = {block.start_addr: block for block in blocks}
        
        # 构建CFG：块 -> (successor_block, condition)元组列表
        # condition是BoolRef（无条件为True，条件为符号）
        self.successors: Dict[int, List[Tuple[X86Block, BoolRef]]] = {}
        self._build_cfg()
    
    def _build_cfg(self):
        """从块构建控制流图。"""
        # 为所有块初始化后继节点
        for block in self.blocks:
            self.successors[block.start_addr] = []
        
        # 基于跳转指令查找后继节点
        for i, block in enumerate(self.blocks):
            if not block.instructions:
                continue
            
            last_insn = block.instructions[-1]
            mnemonic = last_insn.mnemonic.lower()
            
            if mnemonic == 'jmp':
                # 无条件跳转
                target = self._extract_jump_target(last_insn)
                if target is not None:
                    target_block = self._find_block_by_addr(target)
                    if target_block:
                        self.successors[block.start_addr].append((target_block, BoolVal(True)))
            
            elif mnemonic in ['jb', 'jae', 'je', 'jne', 'jl', 'jle', 'jg', 'jge']:
                # 条件跳转：两个后继节点（跳转路径和顺序执行路径）
                target = self._extract_jump_target(last_insn)
                condition = self._build_jump_condition(last_insn, mnemonic)
                
                # 跳转路径：跳转到目标
                if target is not None:
                    target_block = self._find_block_by_addr(target)
                    if target_block:
                        self.successors[block.start_addr].append((target_block, condition))
                
                # 顺序执行路径：下一个块
                if i + 1 < len(self.blocks):
                    next_block = self.blocks[i + 1]
                    # 对顺序执行路径取反条件
                    fall_through_condition = Not(condition)
                    self.successors[block.start_addr].append((next_block, fall_through_condition))
            
            elif mnemonic == 'ret':
                # 返回：无后继节点
                pass
            
            else:
                # 普通指令：顺序执行到下一个块
                if i + 1 < len(self.blocks):
                    next_block = self.blocks[i + 1]
                    self.successors[block.start_addr].append((next_block, BoolVal(True)))
    
    def _extract_jump_target(self, insn: X86Instruction) -> Optional[int]:
        """从指令中提取跳转目标地址。

        Args:
            insn: 跳转指令

        Returns:
            目标地址，如果未找到则返回None
        """
        operands = parse_operands(insn)
        if operands.get('jump_target') is not None:
            return operands['jump_target']
        return None
    
    def _build_jump_condition(self, insn: X86Instruction, mnemonic: str) -> BoolRef:
        """为条件跳转构建符号条件。
        
        Args:
            insn: 跳转指令
            mnemonic: 指令助记符（jb、jae等）
            
        Returns:
            符号条件（BoolRef）
        """
        # 目前，返回一个符号条件
        # 在完整实现中，我们将从先前的CMP指令中提取条件
        # 并根据跳转类型构建适当的条件
        
        # 创建符号条件变量
        # 这将增强以跟踪实际的CMP条件
        from z3 import Bool
        condition_var = Bool(f"jump_cond_{insn.addr:x}")
        return condition_var
    
    def _find_block_by_addr(self, addr: int) -> Optional[X86Block]:
        """查找包含或起始于给定地址的块。
        
        Args:
            addr: 要查找的地址
            
        Returns:
            包含该地址的块，如果未找到则返回None
        """
        # 首先尝试精确匹配
        if addr in self.blocks_by_addr:
            return self.blocks_by_addr[addr]
        
        # 查找包含该地址的块
        for block in self.blocks:
            if block.start_addr <= addr < block.end_addr:
                return block
        
        return None
    
    def get_entry_block(self) -> Optional[X86Block]:
        """获取入口块（第一个块）。
        
        Returns:
            入口块，如果没有块则返回None
        """
        return self.blocks[0] if self.blocks else None
    
    def get_return_blocks(self) -> List[X86Block]:
        """获取所有以ret指令结尾的块。
        
        Returns:
            返回块列表
        """
        ret_blocks = []
        for block in self.blocks:
            if not block.instructions:
                continue
            last_insn = block.instructions[-1]
            if last_insn.mnemonic.lower() == 'ret':
                ret_blocks.append(block)
        return ret_blocks
    
    def find_all_paths(self, entry: Optional[X86Block] = None,
                      terminals: Optional[List[X86Block]] = None) -> List[Tuple[List[X86Block], BoolRef]]:
        """查找从入口到终端块的所有路径。
        
        Args:
            entry: 入口块（默认：第一个块）
            terminals: 终端块（默认：所有返回块）
            
        Returns:
            (path, condition)元组列表，其中：
            - path: 按执行顺序排列的块列表
            - condition: 此路径的符号条件（跳转条件的合取）
        """
        if entry is None:
            entry = self.get_entry_block()
        if entry is None:
            return []
        
        if terminals is None:
            terminals = self.get_return_blocks()
        
        if not terminals:
            # 如果没有显式终端，使用最后一个块
            terminals = [self.blocks[-1]] if self.blocks else []
        
        all_paths = []
        visited = set()
        
        def dfs(current: X86Block, path: List[X86Block], condition: BoolRef):
            """深度优先搜索以查找所有路径。"""
            # 避免循环（简单检查）
            if current in path:
                return
            
            current_path = path + [current]
            
            # 检查是否到达终端
            if current in terminals:
                all_paths.append((current_path, condition))
                return
            
            # 探索后继节点
            for successor, succ_condition in self.successors.get(current.start_addr, []):
                # 合并条件：当前条件AND后继条件
                new_condition = And(condition, succ_condition)
                dfs(successor, current_path, new_condition)
        
        # 从入口开始DFS
        dfs(entry, [], BoolVal(True))
        
        return all_paths
    
    def get_successors(self, block: X86Block) -> List[Tuple[X86Block, BoolRef]]:
        """获取给定块的后继块及其条件。
        
        Args:
            block: 要获取后继节点的块
            
        Returns:
            (successor_block, condition)元组列表
        """
        return self.successors.get(block.start_addr, [])


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


def build_x86_cfg(instructions: List[X86Instruction]) -> X86CFG:
    """从x86-64指令构建CFG。
    
    Args:
        instructions: x86-64指令列表
        
    Returns:
        X86CFG实例
    """
    blocks = identify_basic_blocks(instructions)
    return X86CFG(blocks)

