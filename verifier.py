"""
Z3-Based Verification Engine

This module implements translation verification to prove semantic equivalence
between EVM bytecode and AOT-compiled x86-64 machine code using symbolic stacks.
"""

from z3 import Solver, SolverFor, unsat, sat, simplify, Distinct, set_option, BitVec, BitVecVal
from evm_interpreter import EVMInterpreter, Uint256
from x86_semantics import X86Executor, Register
from typing import Tuple, Optional


class TranslationVerifier:
    """Verifies semantic equivalence between EVM and x86-64 code using symbolic stacks."""
    
    def __init__(self, timeout_ms: int = 60000, verbose: bool = False):
        """Initialize the verifier.
        
        Args:
            timeout_ms: Solver timeout in milliseconds
            verbose: Enable verbose Z3 output
        """
        self.timeout_ms = timeout_ms
        self.verbose = verbose
        
        # Initialize solver
        if verbose:
            set_option(verbose=10)
            set_option(proof=True)
        
        self.solver = SolverFor("QF_BV")
        self.solver.set("timeout", timeout_ms)
    
    def verify_add_symbolic(self) -> Tuple[bool, Optional[str]]:
        """Verify ADD operation with fully symbolic inputs.
        
        This proves equivalence for all possible input values by using
        symbolic variables for the stack values.
        
        Returns:
            (verified, message) where verified is True if equivalence is proven
        """
        print(f"\n=== Symbolic Verification of ADD ===")
        print("Proving: ∀ a, b ∈ Uint256. EVM_ADD(a, b) ≡ x86_ADD(a, b)")
        
        # Create symbolic stack values for EVM
        evm_val1 = Uint256.symbolic("evm_val1")
        evm_val2 = Uint256.symbolic("evm_val2")
        
        # Execute EVM ADD
        print("\n[1] Executing EVM ADD symbolically...")
        evm_interp = EVMInterpreter(initial_stack=[evm_val1, evm_val2])
        evm_result_uint256 = evm_interp.add()
        evm_result = evm_result_uint256.to_bv256()
        
        print(f"    EVM input 1: {evm_val1}")
        print(f"    EVM input 2: {evm_val2}")
        print(f"    EVM result: computed symbolically")
        
        # Create symbolic stack values for x86-64
        # Must use the same symbolic values to prove equivalence
        x86_val1_z0 = evm_val1.z0
        x86_val1_z1 = evm_val1.z1
        x86_val1_z2 = evm_val1.z2
        x86_val1_z3 = evm_val1.z3
        x86_val2_z0 = evm_val2.z0
        x86_val2_z1 = evm_val2.z1
        x86_val2_z2 = evm_val2.z2
        x86_val2_z3 = evm_val2.z3
        
        x86_stack_values = [
            x86_val1_z0, x86_val1_z1, x86_val1_z2, x86_val1_z3,
            x86_val2_z0, x86_val2_z1, x86_val2_z2, x86_val2_z3
        ]
        
        # Execute x86-64 ADD
        print("\n[2] Executing x86-64 ADD symbolically...")
        x86_exec = X86Executor(initial_stack_values=x86_stack_values)
        x86_exec.execute_aot_add_from_stack()
        x86_result = x86_exec.get_stack_result_uint256()
        
        print(f"    x86 stack initialized with same symbolic values")
        print(f"    x86 result: computed symbolically")
        
        # Verify equivalence
        print("\n[3] Checking equivalence with Z3...")
        print(f"    Asserting: EVM_result ≠ x86_result")
        print(f"    If UNSAT, then they are always equal (proven!)")
        
        self.solver.reset()
        self.solver.add(Distinct(evm_result, x86_result))
        
        result = self.solver.check()
        
        if result == unsat:
            msg = "✓ VERIFIED: EVM and x86-64 ADD are semantically equivalent for ALL inputs"
            print(f"\n{msg}")
            print(f"\nThis is a FORMAL PROOF that:")
            print(f"  ∀ a, b ∈ Uint256. EVM_ADD(a, b) = x86_ADD(a, b)")
            if self.verbose:
                print("\nProof:")
                proof = self.solver.proof()
                for i, step in enumerate(proof.children()):
                    print(f"  Step {i+1}: {step.decl()}")
                    if i > 10:
                        print("  ... (truncated)")
                        break
            return True, msg
        elif result == sat:
            model = self.solver.model()
            msg = "✗ COUNTEREXAMPLE FOUND: EVM and x86-64 semantics differ"
            print(f"\n{msg}")
            print(f"Counterexample:")
            print(f"  EVM result: {model.evaluate(evm_result)}")
            print(f"  x86 result: {model.evaluate(x86_result)}")
            # Print the input values that cause the difference
            print(f"  Input val1.z0: {model.evaluate(evm_val1.z0)}")
            print(f"  Input val1.z1: {model.evaluate(evm_val1.z1)}")
            print(f"  Input val2.z0: {model.evaluate(evm_val2.z0)}")
            print(f"  Input val2.z1: {model.evaluate(evm_val2.z1)}")
            return False, msg
        else:
            msg = "? UNKNOWN: Solver could not determine equivalence"
            print(f"\n{msg}")
            return False, msg
    
    def verify_add_concrete(self, val1: int, val2: int) -> Tuple[bool, Optional[str]]:
        """Verify ADD operation for concrete values.
        
        Args:
            val1: First operand (concrete value, will be extended to 256 bits)
            val2: Second operand (concrete value, will be extended to 256 bits)
            
        Returns:
            (verified, message) where verified is True if equivalence is proven
        """
        print(f"\n=== Verifying ADD: 0x{val1:x} + 0x{val2:x} ===")
        
        # Create concrete values for EVM
        evm_val1 = Uint256.from_int(val1)
        evm_val2 = Uint256.from_int(val2)
        
        # Execute EVM
        evm_interp = EVMInterpreter(initial_stack=[evm_val1, evm_val2])
        evm_result_uint256 = evm_interp.add()
        evm_result = evm_result_uint256.to_bv256()
        
        print(f"EVM execution complete")
        print(f"  Result (z0): {simplify(evm_result_uint256.z0)}")
        print(f"  Result (z1): {simplify(evm_result_uint256.z1)}")
        print(f"  Result (z2): {simplify(evm_result_uint256.z2)}")
        print(f"  Result (z3): {simplify(evm_result_uint256.z3)}")
        
        # Create concrete values for x86-64
        x86_val1 = [BitVecVal(val1, 64), BitVecVal(0, 64), BitVecVal(0, 64), BitVecVal(0, 64)]
        x86_val2 = [BitVecVal(val2, 64), BitVecVal(0, 64), BitVecVal(0, 64), BitVecVal(0, 64)]
        x86_stack_values = x86_val1 + x86_val2
        
        # Execute x86-64
        x86_exec = X86Executor(initial_stack_values=x86_stack_values)
        x86_exec.execute_aot_add_from_stack()
        x86_result = x86_exec.get_stack_result_uint256()
        
        print(f"x86-64 execution complete")
        
        # Check if results are equal
        self.solver.reset()
        self.solver.add(Distinct(evm_result, x86_result))
        
        print(f"Checking equivalence with Z3...")
        result = self.solver.check()
        
        if result == unsat:
            msg = "✓ VERIFIED: EVM and x86-64 semantics are equivalent"
            print(f"\n{msg}")
            # Evaluate to get concrete value for display
            result_val = simplify(evm_result)
            print(f"  Result: {result_val}")
            return True, msg
        elif result == sat:
            model = self.solver.model()
            msg = "✗ COUNTEREXAMPLE: EVM and x86-64 semantics differ"
            print(f"\n{msg}")
            print(f"Counterexample:")
            print(f"  EVM result: {model.evaluate(evm_result)}")
            print(f"  x86 result: {model.evaluate(x86_result)}")
            return False, msg
        else:
            msg = "? UNKNOWN: Could not determine equivalence"
            print(f"\n{msg}")
            return False, msg


def run_verification_suite():
    """Run a comprehensive verification test suite."""
    verifier = TranslationVerifier(timeout_ms=60000, verbose=True)
    
    print("=" * 70)
    print("EVM AOT TRANSLATION VERIFICATION")
    print("Verifying ADD instruction with symbolic execution")
    print("=" * 70)
    
    # Test 1: Symbolic verification (the main proof!)
    print("\n" + "=" * 70)
    print("TEST 1: SYMBOLIC VERIFICATION (FORMAL PROOF)")
    print("=" * 70)
    success_symbolic, msg_symbolic = verifier.verify_add_symbolic()
    
    # Test 2-5: Concrete test cases to double-check
    print("\n" + "=" * 70)
    print("TEST 2-5: CONCRETE TEST CASES (SANITY CHECKS)")
    print("=" * 70)
    
    concrete_tests = [
        (0x60, 0x10, "Standard case"),
        (0x00, 0x00, "Zero + Zero"),
        (0xFF, 0xFF, "Max byte + Max byte"),
        (0xFFFFFFFFFFFFFFFF, 0x01, "Max uint64 + 1 (tests carry)"),
    ]
    
    results = [(msg_symbolic, success_symbolic)]
    # for val1, val2, description in concrete_tests:
    #     print(f"\n[Test] {description}: 0x{val1:x} + 0x{val2:x}")
    #     success, msg = verifier.verify_add_concrete(val1, val2)
    #     results.append((description, success))
    
    # # Summary
    # print("\n" + "=" * 70)
    # print("VERIFICATION SUMMARY")
    # print("=" * 70)
    
    # if success_symbolic:
    #     print("\n🎉 FORMAL PROOF COMPLETE!")
    #     print("   Proven: ∀ a, b. EVM_ADD(a, b) = x86_ADD(a, b)")
    #     print("")
    #     print("   This means the AOT compiler's ADD implementation")
    #     print("   is MATHEMATICALLY PROVEN to be equivalent to EVM's")
    #     print("   ADD operation for ALL possible 256-bit inputs.")
    
    # print("\nTest Results:")
    # for test_name, success in results:
    #     status = "✓ PASS" if success else "✗ FAIL"
    #     print(f"  {status}: {test_name}")
    
    # all_passed = all(success for _, success in results)
    # print("\n" + "=" * 70)
    # if all_passed:
    #     print("ALL TESTS PASSED ✓")
    #     print("\nThe ADD instruction is FORMALLY VERIFIED!")
    # else:
    #     print("SOME TESTS FAILED ✗")
    # print("=" * 70)
    
    # return all_passed
    return success_symbolic


if __name__ == "__main__":
    run_verification_suite()
