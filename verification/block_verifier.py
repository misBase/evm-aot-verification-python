"""
Block equivalence verifier.

This module provides block-level verification functionality.
"""

from z3 import BitVec
from typing import Tuple, Optional, Dict, Any
from evm_ir.models import EVMBlock
from evm_ir.semantics import EVMIRSemantics
from x86_64.models import X86Block
from x86_64.semantics import X86SemanticsModel
from .refinement_checker import RefinementChecker


class BlockEquivalenceChecker:
    """Verifies equivalence between EVM and x86 blocks."""
    
    def __init__(self, timeout_ms: int = 60000, verbose: bool = False):
        """Initialize the block equivalence checker.
        
        Args:
            timeout_ms: SMT solver timeout in milliseconds
            verbose: Enable verbose output
        """
        self.evm_semantics = EVMIRSemantics()
        self.x86_semantics = X86SemanticsModel()
        self.refinement_checker = RefinementChecker(timeout_ms=timeout_ms, verbose=verbose)
    
    def verify_block_pair(self,
                         evm_block: EVMBlock,
                         x86_block: X86Block,
                         input_stack: Optional[list] = None) -> Tuple[bool, Optional[str]]:
        """Verify that an EVM block and x86 block are semantically equivalent.
        
        Args:
            evm_block: EVM block to verify
            x86_block: Corresponding x86 block
            input_stack: Optional input stack state (if None, creates symbolic inputs)
            
        Returns:
            (verified, message) where verified is True if blocks are equivalent
        """
        # Build EVM block semantics
        if input_stack is None:
            # Create symbolic inputs based on block requirements
            # For ADD blocks, we need 2 inputs
            from common.uint256 import Uint256
            val1 = Uint256.symbolic(f"evm_block_{evm_block.pc}_val1")
            val2 = Uint256.symbolic(f"evm_block_{evm_block.pc}_val2")
            input_stack = [val1.to_bv256(), val2.to_bv256()]
        
        evm_result = self.evm_semantics.build_block_semantics(evm_block, input_stack)
        evm_formula = evm_result['semantic_formula']
        
        # Build x86 block semantics
        # Convert input stack to x86 memory layout
        from common.uint256 import Uint256
        mem_vars = {}
        
        # For ADD blocks, we expect 2 values on the stack
        if len(input_stack) >= 2:
            # Split into limbs
            val1_bv = input_stack[0]
            val2_bv = input_stack[1]
            
            val1_uint = Uint256.from_bv256(val1_bv)
            val2_uint = Uint256.from_bv256(val2_bv)
            
            # Map to x86 memory layout
            mem_vars[-0x40] = val1_uint.z0
            mem_vars[-0x38] = val1_uint.z1
            mem_vars[-0x30] = val1_uint.z2
            mem_vars[-0x28] = val1_uint.z3
            mem_vars[-0x20] = val2_uint.z0
            mem_vars[-0x18] = val2_uint.z1
            mem_vars[-0x10] = val2_uint.z2
            mem_vars[-0x08] = val2_uint.z3
        
        x86_result = self.x86_semantics.build_block_semantics(x86_block, mem_vars)
        x86_formula = x86_result['semantic_formula']
        
        # Check refinement
        return self.refinement_checker.check_refinement(evm_formula, x86_formula)

