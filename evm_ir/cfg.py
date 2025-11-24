"""
EVM IR Control Flow Graph (CFG) construction and path analysis.

This module provides CFG construction and path finding for EVM IR programs.
Level 2: CFG-level path merging.
"""

from typing import List, Dict, Set, Tuple, Optional
from .models import EVMBlock, EvmOperator
from z3 import BoolRef, BoolVal, And, Or, Not


class IRCFG:
    """Control Flow Graph for EVM IR blocks."""
    
    def __init__(self, blocks: List[EVMBlock]):
        """Initialize CFG from blocks.
        
        Args:
            blocks: List of EVM blocks
        """
        self.blocks = blocks
        self.blocks_by_pc: Dict[int, EVMBlock] = {block.pc: block for block in blocks}
        
        # Build CFG: block -> list of successor blocks
        self.successors: Dict[EVMBlock, List[EVMBlock]] = {}
        self._build_cfg()
    
    def _build_cfg(self):
        """Build control flow graph from blocks."""
        # Initialize successors for all blocks
        for block in self.blocks:
            self.successors[block] = []
        
        # Find successors based on JUMP/JUMPI operations
        for i, block in enumerate(self.blocks):
            # Check last operation in block
            if not block.operations:
                continue
            
            last_op = block.operations[-1]
            kind = last_op.kind.upper()
            
            if kind == "JUMP":
                # Unconditional jump: find target block
                # JUMP pops a value from stack, which should be a TAG param
                # For now, we'll need to track this symbolically
                # For simplicity, assume sequential execution if no explicit target
                if i + 1 < len(self.blocks):
                    self.successors[block].append(self.blocks[i + 1])
            
            elif kind == "JUMPI":
                # Conditional jump: two successors (taken and fall-through)
                # JUMPI pops condition and target from stack
                # Taken: jump to target
                # Fall-through: next block
                if i + 1 < len(self.blocks):
                    self.successors[block].append(self.blocks[i + 1])
                # Note: Actual jump target would need to be resolved from stack
                # For now, we assume sequential execution
            
            elif kind in ["STOP", "RETURN", "REVERT", "SELFDESTRUCT"]:
                # Terminal block: no successors
                pass
            
            else:
                # Normal block: fall through to next block
                if i + 1 < len(self.blocks):
                    self.successors[block].append(self.blocks[i + 1])
    
    def get_entry_block(self) -> EVMBlock:
        """Get the entry block (first block).
        
        Returns:
            Entry block
        """
        if not self.blocks:
            raise ValueError("No blocks in CFG")
        return self.blocks[0]
    
    def get_terminal_blocks(self) -> List[EVMBlock]:
        """Get all terminal blocks (blocks ending with STOP/RETURN/REVERT).
        
        Returns:
            List of terminal blocks
        """
        terminals = []
        for block in self.blocks:
            if not block.operations:
                continue
            last_op = block.operations[-1]
            if last_op.kind.upper() in ["STOP", "RETURN", "REVERT", "SELFDESTRUCT"]:
                terminals.append(block)
        return terminals
    
    def find_all_paths(self, entry: Optional[EVMBlock] = None, 
                      terminals: Optional[List[EVMBlock]] = None) -> List[Tuple[List[EVMBlock], BoolRef]]:
        """Find all paths from entry to terminal blocks.
        
        Args:
            entry: Entry block (default: first block)
            terminals: Terminal blocks (default: all terminal blocks)
            
        Returns:
            List of (path, condition) tuples where:
            - path: List of blocks in execution order
            - condition: Symbolic condition for this path (from JUMPI operations)
        """
        if entry is None:
            entry = self.get_entry_block()
        if terminals is None:
            terminals = self.get_terminal_blocks()
        
        if not terminals:
            # If no explicit terminals, use last block
            terminals = [self.blocks[-1]] if self.blocks else []
        
        all_paths = []
        visited = set()
        
        def dfs(current: EVMBlock, path: List[EVMBlock], condition: BoolRef):
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
            for successor in self.successors.get(current, []):
                # For now, condition is always True (we'll enhance this with JUMPI conditions later)
                dfs(successor, current_path, condition)
        
        # Start DFS from entry
        dfs(entry, [], BoolVal(True))
        
        return all_paths
    
    def get_successors(self, block: EVMBlock) -> List[EVMBlock]:
        """Get successor blocks for a given block.
        
        Args:
            block: Block to get successors for
            
        Returns:
            List of successor blocks
        """
        return self.successors.get(block, [])


def build_ir_cfg(blocks: List[EVMBlock]) -> IRCFG:
    """Build CFG from IR blocks.
    
    Args:
        blocks: List of EVM blocks
        
    Returns:
        IRCFG instance
    """
    return IRCFG(blocks)

