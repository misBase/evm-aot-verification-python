"""
Refinement checker for verifying refinement relation between x86 and EVM semantics.

Verifies that x86 refines EVM: for all inputs, x86_output = EVM_output.
"""

from z3 import BitVec, SolverFor, Distinct, unsat, sat, set_option, Array, Select, And, ForAll
from typing import Tuple, Optional


class RefinementChecker:
    """Checks refinement relation between x86 and EVM semantics.
    
    Verifies that x86 refines EVM: for all inputs, x86_output = EVM_output.
    """
    
    def __init__(self, timeout_ms: int = 60000, verbose: bool = False):
        """Initialize the refinement checker.
        
        Args:
            timeout_ms: SMT solver timeout in milliseconds
            verbose: Enable verbose output
        """
        self.timeout_ms = timeout_ms
        self.verbose = verbose
        
        if verbose:
            set_option(verbose=10)
            set_option(proof=True)
        
        # Use QF_AUFBV (Arrays, Uninterpreted Functions, BitVectors) to support Array comparisons
        # QF_BV doesn't support Arrays, so we need QF_AUFBV
        self.solver = SolverFor("QF_AUFBV")
        self.solver.set("timeout", timeout_ms)
    
    def check_refinement(self, evm_result, x86_result) -> Tuple[bool, Optional[str]]:
        """Check if x86 refines EVM (x86_result = evm_result for all inputs).
        
        This verifies the refinement relation:
          ∀ inputs. x86_output(inputs) = evm_output(inputs)
          
        Supports both old format (single BitVec) and new format (Tuple of data and length).
        
        Args:
            evm_result: Either:
                - Logical formula for EVM output (256-bit BitVec) - old format
                - Tuple of (data, length) where:
                    - data: Logical formula for EVM output (fixed-size BitVec)
                    - length: Logical formula for EVM output length (64-bit BitVec)
            x86_result: Either:
                - Logical formula for x86 output (256-bit BitVec) - old format
                - Tuple of (data, length) where:
                    - data: Logical formula for x86 output (fixed-size BitVec)
                    - length: Logical formula for x86 output length (64-bit BitVec)
            
        Returns:
            (verified, message) where verified is True if refinement holds
        """
        # Handle new format: dict with memory reference (direct memory comparison)
        if isinstance(evm_result, dict) and isinstance(x86_result, dict):
            return self._check_refinement_direct_memory(evm_result, x86_result)
        # Handle intermediate format: tuple with Array/BitVec
        elif isinstance(evm_result, tuple) and isinstance(x86_result, tuple):
            return self._check_refinement_with_length(evm_result, x86_result)
        else:
            # Old format: backward compatibility
            return self._check_refinement_legacy(evm_result, x86_result)
    
    def _check_refinement_legacy(self, evm_result: BitVec, x86_result: BitVec) -> Tuple[bool, Optional[str]]:
        """Legacy refinement check for single BitVec results (backward compatibility)."""
        if evm_result.size() != 256 or x86_result.size() != 256:
            raise ValueError("Both results must be 256-bit BitVecs")
        
        # To prove refinement: show that there exists NO input where they differ
        # We check: ∃ inputs. evm_result ≠ x86_result
        # If UNSAT, then refinement holds (they are always equal)
        
        self.solver.reset()
        self.solver.add(Distinct(evm_result, x86_result))
        
        result = self.solver.check()
        
        if result == unsat:
            msg = "✓ VERIFIED: x86 refines EVM (semantically equivalent for all inputs)"
            return True, msg
        elif result == sat:
            model = self.solver.model()
            msg = "✗ COUNTEREXAMPLE FOUND: x86 does not refine EVM"
            return False, msg
        else:
            msg = "? UNKNOWN: Solver could not determine refinement"
            return False, msg
    
    def _check_refinement_with_length(self, evm_result, 
                                     x86_result) -> Tuple[bool, Optional[str]]:
        """Check refinement with length and data comparison.
        
        Args:
            evm_result: Tuple of (data, length) where:
                - data: Either Array[BitVec[64], BitVec[8]] or BitVec (for backward compatibility)
                - length: Logical formula for EVM output length (64-bit BitVec)
            x86_result: Tuple of (data, length) where:
                - data: Either Array[BitVec[64], BitVec[8]] or BitVec (for backward compatibility)
                - length: Logical formula for x86 output length (64-bit BitVec)
        
        Returns:
            (verified, message) where verified is True if refinement holds
        """
        evm_data, evm_length = evm_result
        x86_data, x86_length = x86_result
        
        if evm_length.size() != 64 or x86_length.size() != 64:
            raise ValueError("Length must be 64-bit BitVec")
        
        # First check: lengths must be equal
        # If lengths differ, programs are not equivalent
        self.solver.reset()
        self.solver.add(evm_length != x86_length)
        result = self.solver.check()
        
        if result == sat:
            # Lengths can differ - not equivalent
            return False, "✗ COUNTEREXAMPLE: Return lengths differ"
        
        # Second check: if lengths are equal, data must be equal
        # Handle both Array and BitVec formats
        self.solver.reset()
        self.solver.add(evm_length == x86_length)  # Lengths are equal
        
        # Check if data is Array or BitVec
        if isinstance(evm_data, Array) and isinstance(x86_data, Array):
            # Array format: compare only up to length bytes
            # We want to check: Exists i. (i < length) && (evm_data[i] != x86_data[i])
            # If UNSAT, then ForAll i. (i < length) => (evm_data[i] == x86_data[i])
            from z3 import BitVecVal, ULT
            
            # Create a symbolic index variable
            i = BitVec('return_data_index', 64)
            
            # Constraint: i < length
            index_in_range = ULT(i, evm_length)
            
            # Compare bytes at position i
            evm_byte = Select(evm_data, i)
            x86_byte = Select(x86_data, i)
            
            # Add constraints: i < length AND evm_data[i] != x86_data[i]
            # If this is satisfiable, we found a counterexample
            self.solver.add(index_in_range)
            self.solver.add(evm_byte != x86_byte)
            
        else:
            # BitVec format (backward compatibility): compare entire fixed-size data
            if evm_data.size() != x86_data.size():
                raise ValueError(f"Data sizes must match: EVM={evm_data.size()}, x86={x86_data.size()}")
            self.solver.add(Distinct(evm_data, x86_data))  # But data differs
        
        result = self.solver.check()
        
        if result == unsat:
            msg = "✓ VERIFIED: x86 refines EVM (lengths and data are equivalent for all inputs)"
            return True, msg
        elif result == sat:
            model = self.solver.model()
            msg = "✗ COUNTEREXAMPLE FOUND: x86 does not refine EVM (data differs)"
            return False, msg
        else:
            msg = "? UNKNOWN: Solver could not determine refinement"
            return False, msg
    
    def _check_refinement_direct_memory(self, evm_result: dict, x86_result: dict) -> Tuple[bool, Optional[str]]:
        """Check refinement by directly comparing memory contents.
        
        This is the optimized approach: instead of extracting all bytes to an Array,
        we directly compare memory contents using quantifiers:
          ForAll i. (0 <= i < length) => 
            EVM_memory[evm_offset + i] == x86_memory[x86_base_addr + x86_offset + i]
        
        Args:
            evm_result: Dict with keys:
                - 'offset': 64-bit BitVec offset in EVM memory (0 = no return)
                - 'length': 64-bit BitVec length (0 = no return)
                - 'memory': Array[BitVec[64], BitVec[8]] - EVM memory
                - 'base_addr': None (EVM uses direct offset, None means direct addressing)
                - 'has_return': BitVec condition (length != 0)
            x86_result: Dict with keys:
                - 'offset': 64-bit BitVec offset (0 = no return)
                - 'length': 64-bit BitVec length (0 = no return)
                - 'memory': Array[BitVec[64], BitVec[8]] - x86 memory
                - 'base_addr': 64-bit BitVec (R15 register value, EVM memory base pointer)
                - 'has_return': BitVec condition (length != 0)
        
        Returns:
            (verified, message) where verified is True if refinement holds
        """
        from z3 import ForAll, Implies, And, ULT, UGE, BitVec, Select, BitVecVal, sat, unsat
        
        evm_offset = evm_result['offset']
        evm_length = evm_result['length']
        evm_memory = evm_result['memory']
        evm_has_return = evm_result.get('has_return', evm_length != BitVecVal(0, 64))
        
        x86_offset = x86_result['offset']
        x86_length = x86_result['length']
        x86_memory = x86_result['memory']
        x86_base_addr = x86_result['base_addr']
        x86_has_return = x86_result.get('has_return', x86_length != BitVecVal(0, 64))
        
        # First check: return conditions must be equivalent
        # EVM returns if and only if x86 returns
        self.solver.reset()
        self.solver.add(evm_has_return != x86_has_return)
        result = self.solver.check()
        
        if result == sat:
            return False, "✗ COUNTEREXAMPLE: Return conditions differ (one returns, the other doesn't)"
        
        # Second check: if both return (or both don't return), lengths must be equal
        self.solver.reset()
        self.solver.add(evm_has_return)  # Assume both return
        self.solver.add(x86_has_return)
        self.solver.add(evm_length != x86_length)
        result = self.solver.check()
        
        if result == sat:
            return False, "✗ COUNTEREXAMPLE: Return lengths differ"
        
        # Third check: if lengths are equal and both return, memory contents must be equal
        # We want to check: ForAll i. (0 <= i < length) => 
        #   EVM_memory[evm_offset + i] == x86_memory[x86_base_addr + x86_offset + i]
        # 
        # We check the negation: Exists i. (0 <= i < length) AND 
        #   EVM_memory[evm_offset + i] != x86_memory[x86_base_addr + x86_offset + i]
        # If this is UNSAT, then the ForAll holds.
        
        self.solver.reset()
        self.solver.add(evm_has_return)  # Both return
        self.solver.add(x86_has_return)
        self.solver.add(evm_length == x86_length)  # Lengths are equal
        
        # Create symbolic index variable
        i = BitVec('return_data_index', 64)
        
        # Constraint: 0 <= i < length
        index_in_range = And(UGE(i, BitVecVal(0, 64)), ULT(i, evm_length))
        
        # Calculate memory addresses
        evm_addr = evm_offset + i
        x86_addr = x86_base_addr + x86_offset + i
        
        # Read bytes from memory
        evm_byte = Select(evm_memory, evm_addr)
        x86_byte = Select(x86_memory, x86_addr)
        
        # Add constraints: i in range AND evm_byte != x86_byte
        # If this is satisfiable, we found a counterexample
        self.solver.add(index_in_range)
        self.solver.add(evm_byte != x86_byte)
        
        result = self.solver.check()
        
        if result == unsat:
            msg = "✓ VERIFIED: x86 refines EVM (return conditions, lengths, and memory contents are equivalent for all inputs)"
            return True, msg
        elif result == sat:
            model = self.solver.model()
            msg = "✗ COUNTEREXAMPLE FOUND: x86 does not refine EVM (memory contents differ)"
            return False, msg
        else:
            msg = "? UNKNOWN: Solver could not determine refinement"
            return False, msg

