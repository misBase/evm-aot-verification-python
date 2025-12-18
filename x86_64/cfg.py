"""
x86-64 Control Flow Graph (CFG) construction and path analysis.

This module provides basic block identification and CFG construction for x86-64 programs.
"""

from typing import List, Dict, Set, Tuple, Optional
from z3 import BoolRef, BoolVal, And, Or, Not, BitVecVal
from .models import X86Block, X86Instruction
from .disassembler import parse_operands


class X86CFG:
    """Control Flow Graph for x86-64 programs."""
    
    def __init__(self, blocks: List[X86Block]):
        """Initialize CFG from blocks.
        
        Args:
            blocks: List of x86-64 blocks
        """
        self.blocks = blocks
        self.blocks_by_addr: Dict[int, X86Block] = {block.start_addr: block for block in blocks}
        
        # Build CFG: block -> list of (successor_block, condition) tuples
        # condition is BoolRef (True for unconditional, symbolic for conditional)
        self.successors: Dict[int, List[Tuple[X86Block, BoolRef]]] = {}
        self._build_cfg()
    
    def _build_cfg(self):
        """Build control flow graph from blocks."""
        # Initialize successors for all blocks
        for block in self.blocks:
            self.successors[block.start_addr] = []
        
        # Find successors based on jump instructions
        for i, block in enumerate(self.blocks):
            if not block.instructions:
                continue
            
            last_insn = block.instructions[-1]
            mnemonic = last_insn.mnemonic.lower()
            
            if mnemonic == 'jmp':
                # Unconditional jump
                target = self._extract_jump_target(last_insn)
                if target is not None:
                    target_block = self._find_block_by_addr(target)
                    if target_block:
                        self.successors[block.start_addr].append((target_block, BoolVal(True)))
            
            elif mnemonic in ['jb', 'jae', 'je', 'jne', 'jl', 'jle', 'jg', 'jge']:
                # Conditional jump: two successors (taken and fall-through)
                target = self._extract_jump_target(last_insn)
                condition = self._build_jump_condition(last_insn, mnemonic)
                
                # Taken path: jump to target
                if target is not None:
                    target_block = self._find_block_by_addr(target)
                    if target_block:
                        self.successors[block.start_addr].append((target_block, condition))
                
                # Fall-through path: next block
                if i + 1 < len(self.blocks):
                    next_block = self.blocks[i + 1]
                    # Negate condition for fall-through
                    fall_through_condition = Not(condition)
                    self.successors[block.start_addr].append((next_block, fall_through_condition))
            
            elif mnemonic == 'ret':
                # Return: no successors
                pass
            
            else:
                # Normal instruction: fall through to next block
                if i + 1 < len(self.blocks):
                    next_block = self.blocks[i + 1]
                    self.successors[block.start_addr].append((next_block, BoolVal(True)))
    
    def _extract_jump_target(self, insn: X86Instruction) -> Optional[int]:
        """Extract jump target address from instruction.
        
        Args:
            insn: Jump instruction
            
        Returns:
            Target address, or None if not found
        """
        operands = parse_operands(insn.op_str)
        if operands.get('jump_target') is not None:
            return operands['jump_target']
        return None
    
    def _build_jump_condition(self, insn: X86Instruction, mnemonic: str) -> BoolRef:
        """Build symbolic condition for conditional jump.
        
        Args:
            insn: Jump instruction
            mnemonic: Instruction mnemonic (jb, jae, etc.)
            
        Returns:
            Symbolic condition (BoolRef)
        """
        # For now, return a symbolic condition
        # In a full implementation, we would extract the condition from the previous CMP instruction
        # and build the appropriate condition based on the jump type
        
        # Create a symbolic condition variable
        # This will be enhanced to track actual CMP conditions
        from z3 import Bool
        condition_var = Bool(f"jump_cond_{insn.addr:x}")
        return condition_var
    
    def _find_block_by_addr(self, addr: int) -> Optional[X86Block]:
        """Find block containing or starting at given address.
        
        Args:
            addr: Address to find
            
        Returns:
            Block containing the address, or None
        """
        # First try exact match
        if addr in self.blocks_by_addr:
            return self.blocks_by_addr[addr]
        
        # Find block containing the address
        for block in self.blocks:
            if block.start_addr <= addr < block.end_addr:
                return block
        
        return None
    
    def get_entry_block(self) -> Optional[X86Block]:
        """Get the entry block (first block).
        
        Returns:
            Entry block, or None if no blocks
        """
        return self.blocks[0] if self.blocks else None
    
    def get_return_blocks(self) -> List[X86Block]:
        """Get all blocks ending with ret instruction.
        
        Returns:
            List of return blocks
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
        """Find all paths from entry to terminal blocks.
        
        Args:
            entry: Entry block (default: first block)
            terminals: Terminal blocks (default: all return blocks)
            
        Returns:
            List of (path, condition) tuples where:
            - path: List of blocks in execution order
            - condition: Symbolic condition for this path (conjunction of jump conditions)
        """
        if entry is None:
            entry = self.get_entry_block()
        if entry is None:
            return []
        
        if terminals is None:
            terminals = self.get_return_blocks()
        
        if not terminals:
            # If no explicit terminals, use last block
            terminals = [self.blocks[-1]] if self.blocks else []
        
        all_paths = []
        visited = set()
        
        def dfs(current: X86Block, path: List[X86Block], condition: BoolRef):
            """Depth-first search to find all paths."""
            # Avoid cycles (simple check)
            if current in path:
                return
            
            current_path = path + [current]
            
            # Check if we reached a terminal
            if current in terminals:
                all_paths.append((current_path, condition))
                return
            
            # Explore successors
            for successor, succ_condition in self.successors.get(current.start_addr, []):
                # Combine conditions: current condition AND successor condition
                new_condition = And(condition, succ_condition)
                dfs(successor, current_path, new_condition)
        
        # Start DFS from entry
        dfs(entry, [], BoolVal(True))
        
        return all_paths
    
    def get_successors(self, block: X86Block) -> List[Tuple[X86Block, BoolRef]]:
        """Get successor blocks with conditions for a given block.
        
        Args:
            block: Block to get successors for
            
        Returns:
            List of (successor_block, condition) tuples
        """
        return self.successors.get(block.start_addr, [])


def identify_basic_blocks(instructions: List[X86Instruction]) -> List[X86Block]:
    """Identify basic blocks from instruction sequence.
    
    Basic block boundaries:
    - Start: program entry, jump target, instruction after ret
    - End: jmp, conditional jump (jb/jae), ret
    
    Args:
        instructions: List of x86-64 instructions
        
    Returns:
        List of X86Block objects
    """
    if not instructions:
        return []
    
    # Find block start addresses
    block_starts: Set[int] = {instructions[0].addr}  # Program entry
    
    # Find jump targets and instructions after ret
    for i, insn in enumerate(instructions):
        mnemonic = insn.mnemonic.lower()
        
        if mnemonic in ['jmp', 'jb', 'jae', 'je', 'jne', 'jl', 'jle', 'jg', 'jge']:
            # Jump instruction: extract target
            operands = parse_operands(insn.op_str)
            target = operands.get('jump_target')
            if target is not None:
                block_starts.add(target)
            
            # Instruction after jump is also a block start (fall-through)
            if i + 1 < len(instructions):
                block_starts.add(instructions[i + 1].addr)
        
        elif mnemonic == 'ret':
            # Instruction after ret is a block start
            if i + 1 < len(instructions):
                block_starts.add(instructions[i + 1].addr)
    
    # Sort block starts
    sorted_starts = sorted(block_starts)
    
    # Create blocks
    blocks = []
    for i, start_addr in enumerate(sorted_starts):
        # Find end address (next block start or end of program)
        if i + 1 < len(sorted_starts):
            end_addr = sorted_starts[i + 1]
        else:
            # Last block: end at last instruction
            last_insn = instructions[-1]
            end_addr = last_insn.addr + last_insn.size
        
        # Collect instructions in this block
        block_instructions = []
        for insn in instructions:
            if start_addr <= insn.addr < end_addr:
                block_instructions.append(insn)
        
        if block_instructions:
            block = X86Block(
                start_addr=start_addr,
                end_addr=end_addr,
                instructions=block_instructions,
                is_jump_target=(start_addr != instructions[0].addr)  # All except first are jump targets
            )
            blocks.append(block)
    
    return blocks


def build_x86_cfg(instructions: List[X86Instruction]) -> X86CFG:
    """Build CFG from x86-64 instructions.
    
    Args:
        instructions: List of x86-64 instructions
        
    Returns:
        X86CFG instance
    """
    blocks = identify_basic_blocks(instructions)
    return X86CFG(blocks)

