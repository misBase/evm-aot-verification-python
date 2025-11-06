"""
Refinement checker for verifying refinement relation between x86 and EVM semantics.

Verifies that x86 refines EVM: for all inputs, x86_output = EVM_output.
"""

from z3 import BitVec, SolverFor, Distinct, unsat, sat, set_option
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
        
        self.solver = SolverFor("QF_BV")
        self.solver.set("timeout", timeout_ms)
    
    def check_refinement(self, evm_result: BitVec, x86_result: BitVec) -> Tuple[bool, Optional[str]]:
        """Check if x86 refines EVM (x86_result = evm_result for all inputs).
        
        This verifies the refinement relation:
          ∀ inputs. x86_output(inputs) = evm_output(inputs)
          
        For deterministic operations like ADD, refinement is equivalent to equality.
        
        Args:
            evm_result: Logical formula for EVM output (256-bit BitVec)
            x86_result: Logical formula for x86 output (256-bit BitVec)
            
        Returns:
            (verified, message) where verified is True if refinement holds
        """
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

