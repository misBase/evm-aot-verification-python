"""
Program equivalence verifier.

This module provides program-level verification functionality,
operating on entire programs rather than individual blocks.
"""

from z3 import BitVec
from typing import Tuple, Optional, Dict, Any, List
from evm_ir.program import EVMProgram
from x86_64.program import X86Program
from .refinement_checker import RefinementChecker


class ProgramEquivalenceChecker:
    """Verifies equivalence between EVM and x86 programs."""
    
    def __init__(self, timeout_ms: int = 60000, verbose: bool = False):
        """Initialize the program equivalence checker.
        
        Args:
            timeout_ms: SMT solver timeout in milliseconds
            verbose: Enable verbose output
        """
        self.refinement_checker = RefinementChecker(timeout_ms=timeout_ms, verbose=verbose)
        self.verbose = verbose
    
    def verify_program_pair(self,
                           evm_program: EVMProgram,
                           x86_program: X86Program,
                           input_stack: Optional[List[BitVec]] = None) -> Tuple[bool, Optional[str]]:
        """Verify that an EVM program and x86 program are semantically equivalent.
        
        This performs whole-program verification by building semantic models
        for the entire EVM IR sequence and the entire x86-64 machine code sequence,
        then proving they are equivalent using Z3.
        
        Args:
            evm_program: EVM program to verify
            x86_program: Corresponding x86 program
            input_stack: Optional input stack state (if None, creates symbolic inputs)
            
        Returns:
            (verified, message) where verified is True if programs are equivalent
        """
        if self.verbose:
            print(f"\n=== Program-Level Verification ===")
            print(f"EVM Program: {evm_program}")
            print(f"x86 Program: {x86_program}")
        
        # Build EVM program semantics
        if input_stack is None:
            # Create symbolic inputs based on program requirements
            # For ADD programs, we need 2 inputs
            from common.uint256 import Uint256
            val1 = Uint256.symbolic("program_val1")
            val2 = Uint256.symbolic("program_val2")
            input_stack = [val1.to_bv256(), val2.to_bv256()]
        
        if self.verbose:
            print("\n[1] Building EVM program semantics...")
        
        evm_result = evm_program.build_program_semantics(input_stack)
        evm_formula = evm_result['semantic_formula']
        
        if self.verbose:
            print(f"    Executed {len(evm_result.get('executed_blocks', []))} EVM blocks")
            print(f"    Final stack depth: {evm_result.get('output_count', 0)}")
        
        # Build x86 program semantics
        # Convert input stack to x86 memory layout
        from common.uint256 import Uint256
        
        if self.verbose:
            print("\n[2] Building x86 program semantics...")
        
        # Split input stack into limbs for x86 memory layout
        if len(input_stack) >= 2:
            val1_bv = input_stack[0]
            val2_bv = input_stack[1]
            
            val1_uint = Uint256.from_bv256(val1_bv)
            val2_uint = Uint256.from_bv256(val2_bv)
            
            # Use program-level semantics builder
            x86_result = x86_program.build_program_semantics_from_limbs(
                [val1_uint.z0, val1_uint.z1, val1_uint.z2, val1_uint.z3],
                [val2_uint.z0, val2_uint.z1, val2_uint.z2, val2_uint.z3]
            )
            x86_formula = x86_result['semantic_formula']
        else:
            # Fallback: use default memory state
            initial_memory = {}
            x86_result = x86_program.build_program_semantics(initial_memory)
            x86_formula = x86_result['semantic_formula']
        
        if self.verbose:
            print(f"    Executed {len(x86_result.get('executed_instructions', []))} x86 instructions")
        
        # Check refinement
        if self.verbose:
            print("\n[3] Checking program equivalence with Z3...")
        
        return self.refinement_checker.check_refinement(evm_formula, x86_formula)
    
    def verify_operation_across_programs(self,
                                        evm_program: EVMProgram,
                                        x86_program: X86Program,
                                        operation_kind: str,
                                        input_stack: Optional[List[BitVec]] = None) -> Tuple[bool, Optional[str]]:
        """Verify a specific operation across both programs.
        
        This is useful for verifying specific operations (like ADD) that appear
        in both the EVM and x86 programs.
        
        Args:
            evm_program: EVM program to verify
            x86_program: x86 program to verify
            operation_kind: The operation to focus on (e.g., "ADD")
            input_stack: Optional input stack state
            
        Returns:
            (verified, message) where verified is True if operation is equivalent
        """
        if self.verbose:
            print(f"\n=== Verifying {operation_kind} Operation Across Programs ===")
        
        # Build EVM semantics for the specific operation
        if self.verbose:
            print(f"\n[1] Building EVM {operation_kind} semantics...")
        
        evm_result = evm_program.build_program_semantics_for_operation(
            operation_kind, 
            input_stack
        )
        evm_formula = evm_result['semantic_formula']
        
        # Build x86 semantics
        if self.verbose:
            print(f"\n[2] Building x86 program semantics...")
        
        # Get inputs from EVM result
        if input_stack is None and 'output_stack' in evm_result:
            # Reconstruct inputs from the operation requirements
            from common.uint256 import Uint256
            val1 = Uint256.symbolic("program_val1")
            val2 = Uint256.symbolic("program_val2")
            input_stack = [val1.to_bv256(), val2.to_bv256()]
        
        # Convert to x86 memory layout
        from common.uint256 import Uint256
        val1_uint = Uint256.from_bv256(input_stack[0])
        val2_uint = Uint256.from_bv256(input_stack[1])
        
        x86_result = x86_program.build_program_semantics_from_limbs(
            [val1_uint.z0, val1_uint.z1, val1_uint.z2, val1_uint.z3],
            [val2_uint.z0, val2_uint.z1, val2_uint.z2, val2_uint.z3]
        )
        x86_formula = x86_result['semantic_formula']
        
        # Check refinement
        if self.verbose:
            print(f"\n[3] Checking {operation_kind} equivalence with Z3...")
        
        return self.refinement_checker.check_refinement(evm_formula, x86_formula)

