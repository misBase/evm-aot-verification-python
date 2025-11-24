"""
Program equivalence verifier.

This module provides program-level verification functionality,
operating on entire programs rather than individual blocks.
"""

from z3 import BitVec, IntVal
from typing import Tuple, Optional
from evm_ir.program import EVMProgram
from x86_64.program import X86Program
from .refinement_checker import RefinementChecker
from ir.smt_state import SMTState
from verification.memory_mapping import StackMemoryMapper
from common.uint256 import Uint256


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
    
    @staticmethod
    def create_default_initial_state() -> SMTState:
        """Create a default initial SMT state with symbolic inputs.
        
        Creates a new state with:
        - Two symbolic 256-bit values on EVM stack
        - EVM stack mapped to x86 memory layout
        
        Returns:
            Initialized SMTState with symbolic inputs
        """
        initial_state = SMTState()
        
        # Create symbolic inputs for EVM stack
        val1 = Uint256.symbolic("program_val1")
        val2 = Uint256.symbolic("program_val2")
        input_stack = [val1.to_bv256(), val2.to_bv256()]
        
        # Initialize EVM stack with SP = 0
        initial_state.evm_stack.SP = IntVal(0)
        
        # Push initial stack values
        for stack_val in input_stack:
            initial_state.evm_stack = initial_state.evm_stack.push(stack_val)
        
        # Map EVM stack inputs to x86 memory layout
        for stack_index, stack_value in enumerate(input_stack):
            layout = StackMemoryMapper.stack_to_memory_layout(stack_value, stack_index)
            for offset, limb in layout.items():
                initial_state.x86_memory = initial_state.x86_memory.store_limb(offset, limb)
        
        return initial_state
    
    def verify_program_pair(self,
                           evm_program: EVMProgram,
                           x86_program: X86Program,
                           initial_state: SMTState) -> Tuple[bool, Optional[str]]:
        """Verify that an EVM program and x86 program are semantically equivalent.
        
        This performs whole-program verification using Alive2-style direct formula construction:
        1. Formula building: Use to_z3() to build Z3 formulas for both programs
        2. Output extraction: Extract results from EVM stack and x86 registers/memory
        3. Equivalence checking: Use Z3 to prove equivalence
        
        Args:
            evm_program: EVM program to verify
            x86_program: Corresponding x86 program
            initial_state: Initial SMT state with inputs already prepared
            
        Returns:
            (verified, message) where verified is True if programs are equivalent
        """
        if self.verbose:
            print(f"\n=== Program-Level Verification (Alive2-style) ===")
            print(f"EVM Program: {evm_program}")
            print(f"x86 Program: {x86_program}")
        
        # Step 1: Formula building - EVM (two-level path-aware)
        if self.verbose:
            print("\n[1] Building EVM program formula (two-level path-aware)...")
            print("    Level 1: Block-level TAG path merging (3 paths per block)")
            print("    Level 2: CFG-level path merging")
        
        evm_state, evm_result = evm_program.to_z3(initial_state)
        
        if self.verbose:
            print(f"    EVM stack depth: {evm_state.evm_stack.depth}")
            from z3 import BitVecVal
            evm_has_return = evm_state.return_length != BitVecVal(0, 64)
            print(f"    EVM return condition: length != 0 (symbolic, merged from all paths)")
            print(f"    EVM formula built (all paths merged)")
        
        # Step 2: Formula building - x86 (single-level path-aware)
        if self.verbose:
            print("\n[2] Building x86 program formula (path-aware)...")
            print("    Identifying basic blocks and CFG paths")
        
        x86_state, x86_result = x86_program.to_z3(initial_state)
        
        if self.verbose:
            from z3 import BitVecVal
            x86_has_return = x86_state.return_length != BitVecVal(0, 64)
            print(f"    x86 return condition: length != 0 (symbolic, merged from all paths)")
            print(f"    x86 formula built (all paths merged)")
        
        # Step 3: Output extraction (already done in to_z3, but verify)
        if self.verbose:
            print("\n[3] Extracting outputs...")
            if isinstance(evm_result, dict):
                print(f"    EVM result: direct memory comparison (offset, length, memory)")
            elif isinstance(evm_result, tuple):
                evm_data, evm_length = evm_result
                print(f"    EVM result: data ({evm_data.size()} bits), length ({evm_length.size()} bits)")
            else:
                print(f"    EVM result: {evm_result.size()}-bit BitVec")
            if isinstance(x86_result, dict):
                print(f"    x86 result: direct memory comparison (offset, length, memory, base_addr)")
            elif isinstance(x86_result, tuple):
                x86_data, x86_length = x86_result
                print(f"    x86 result: data ({x86_data.size()} bits), length ({x86_length.size()} bits)")
            else:
                print(f"    x86 result: {x86_result.size()}-bit BitVec")
        
        # Step 4: Equivalence checking
        if self.verbose:
            print("\n[4] Checking program equivalence with Z3...")
            print("    Comparing merged results from all paths (1-to-1 semantic matching)")
        
        return self.refinement_checker.check_refinement(evm_result, x86_result)
    
