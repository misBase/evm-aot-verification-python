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
        self.successors: Dict[int, List[EVMBlock]] = {}
        self._build_cfg()
    
    def _build_cfg(self):
        """Build control flow graph from blocks."""
        # Initialize successors for all blocks
        for block in self.blocks:
            self.successors[block.pc] = []
        
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
                    self.successors[block.pc].append(self.blocks[i + 1])
            
            elif kind == "JUMPI":
                # Conditional jump: two successors (taken and fall-through)
                # JUMPI pops condition and target from stack
                # Taken: jump to target
                # Fall-through: next block
                if i + 1 < len(self.blocks):
                    self.successors[block.pc].append(self.blocks[i + 1])
                # Note: Actual jump target would need to be resolved from stack
                # For now, we assume sequential execution
            
            elif kind in ["STOP", "RETURN", "REVERT", "SELFDESTRUCT"]:
                # Terminal block: no successors
                pass
            
            else:
                # Normal block: fall through to next block
                if i + 1 < len(self.blocks):
                    self.successors[block.pc].append(self.blocks[i + 1])
    
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
            for successor in self.successors.get(current.pc, []):
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
        return self.successors.get(block.pc, [])
    
    def detect_loops(self) -> List[Tuple[List[EVMBlock], str]]:
        """Detect all loops in the CFG and classify them.
        
        Returns:
            List of (loop_blocks, loop_type) tuples where:
            - loop_blocks: List of blocks in the loop
            - loop_type: "static_bounded", "dynamically_bounded", or "unbounded"
        """
        # Find strongly connected components (SCCs) which represent loops
        sccs = self._find_strongly_connected_components()
        
        loops = []
        for scc in sccs:
            # A loop is an SCC with more than one block, or a self-loop
            if len(scc) > 1 or self._is_self_loop(scc[0]):
                loop_type = self._classify_loop(scc)
                loops.append((scc, loop_type))
        
        return loops
    
    def validate_loops(self):
        """Validate loops, raise exception for unsupported loop types.
        
        This should be called before symbolic execution to detect and reject
        unsupported loops (unbounded and dynamically bounded).
        
        Raises:
            UnsupportedLoopError: If unbounded or dynamically bounded loops are detected
        """
        from utils.exceptions import UnsupportedLoopError
        
        loops = self.detect_loops()
        
        for loop_blocks, loop_type in loops:
            if loop_type == "unbounded":
                loop_info = f"Unbounded loop detected in blocks: {[b.pc for b in loop_blocks]}"
                raise UnsupportedLoopError(
                    "unbounded",
                    loop_info,
                    "Unbounded loops are not supported. Please use bounded loops or static loop unrolling."
                )
            elif loop_type == "dynamically_bounded":
                loop_info = f"Dynamically bounded loop detected in blocks: {[b.pc for b in loop_blocks]}"
                raise UnsupportedLoopError(
                    "dynamically_bounded",
                    loop_info,
                    "Dynamically bounded loops are not yet supported. Only static bounded loops are supported."
                )
            # static_bounded loops are supported, no error needed
    
    def _find_strongly_connected_components(self) -> List[List[EVMBlock]]:
        """Find all strongly connected components (SCCs) using Tarjan's algorithm.
        
        SCCs represent loops: if a set of blocks form an SCC, they can reach each other.
        
        Returns:
            List of SCCs, where each SCC is a list of blocks
        """
        # TODO: Implement Tarjan's algorithm for finding SCCs
        # For now, return empty list (no loops detected)
        # Algorithm outline:
        # 1. Use depth-first search with index and lowlink tracking
        # 2. When a node's lowlink equals its index, it's the root of an SCC
        # 3. Pop all nodes from stack until the root to form the SCC
        
        return []
    
    def _is_self_loop(self, block: EVMBlock) -> bool:
        """Check if a block is a self-loop (jumps to itself).
        
        Args:
            block: Block to check
            
        Returns:
            True if block jumps to itself, False otherwise
        """
        # Check if block is in its own successors
        return block in self.successors.get(block.pc, [])
    
    def _classify_loop(self, loop_blocks: List[EVMBlock]) -> str:
        """Classify loop type: static bounded, dynamically bounded, or unbounded.
        
        Classification strategy:
        1. Check if loop exit condition is constant or compile-time determinable
        2. Check if loop has explicit iteration variable and bound
        
        Args:
            loop_blocks: List of blocks in the loop
            
        Returns:
            "static_bounded", "dynamically_bounded", or "unbounded"
        """
        # TODO: Implement loop classification algorithm
        # For now, return "unbounded" as a conservative default
        # Algorithm outline:
        # 1. Analyze exit conditions in loop blocks (JUMPI instructions)
        # 2. Check if exit condition is constant (static bounded)
        # 3. Check if exit condition has symbolic but bounded variable (dynamically bounded)
        # 4. Otherwise, classify as unbounded
        
        # Check for exit conditions
        exit_conditions = []
        for block in loop_blocks:
            if not block.operations:
                continue
            last_op = block.operations[-1]
            if last_op.kind.upper() == "JUMPI":
                exit_conditions.append(block)
        
        if not exit_conditions:
            # No exit conditions found, likely unbounded
            return "unbounded"
        
        # Check if loop has iteration counter
        has_counter = self._has_iteration_counter(loop_blocks)
        
        if has_counter:
            # Has iteration counter, but need to check if bound is constant
            # For now, conservatively classify as dynamically bounded
            return "dynamically_bounded"
        
        # No clear iteration pattern, classify as unbounded
        return "unbounded"
    
    def _has_iteration_counter(self, loop_blocks: List[EVMBlock]) -> bool:
        """Check if loop has an iteration counter.
        
        This is a simplified check. A more sophisticated implementation would:
        - Look for PUSH, ADD, SUB operations that form a counter pattern
        - Track variable modifications within the loop
        
        Args:
            loop_blocks: List of blocks in the loop
            
        Returns:
            True if loop appears to have an iteration counter, False otherwise
        """
        # TODO: Implement iteration counter detection
        # For now, return False (cannot determine)
        # Algorithm outline:
        # 1. Look for operations that increment/decrement a value (ADD/SUB with constant)
        # 2. Check if this value is used in exit condition
        # 3. Pattern: PUSH initial_value, loop: ADD/SUB constant, compare with bound
        
        return False


def build_ir_cfg(blocks: List[EVMBlock]) -> IRCFG:
    """Build CFG from IR blocks.
    
    Args:
        blocks: List of EVM blocks
        
    Returns:
        IRCFG instance
    """
    return IRCFG(blocks)

