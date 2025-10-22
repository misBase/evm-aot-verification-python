#!/usr/bin/env python3
"""
EVM AOT Translation Verification - Main Entry Point

This script verifies the semantic equivalence between EVM bytecode
(PUSH 0x60 PUSH 0x10 ADD) and its AOT-compiled x86-64 machine code.

Usage:
    python main.py [--verbose] [--timeout MILLISECONDS]
"""

import argparse
import sys
from verifier import TranslationVerifier, run_verification_suite


def parse_args():
    """Parse command-line arguments."""
    parser = argparse.ArgumentParser(
        description="Verify EVM AOT compilation correctness using Z3",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python main.py                    # Run all verification tests
  python main.py --verbose          # Run with verbose Z3 output
  python main.py --timeout 30000    # Set 30-second timeout
  python main.py --single 0x60 0x10 # Verify single ADD operation

Test Case:
  EVM Bytecode: 0x01 (ADD instruction only, no PUSH)
  - Pops two 256-bit values from symbolic stack
  - Adds them with carry propagation
  - Pushes result back to stack

x86-64 AOT Code (disassembly section 0x6c-0xac):
  mov rax, [r14-0x40]   ; Load val1.z0 from stack
  add rax, [r14-0x20]   ; Add val2.z0
  mov rcx, [r14-0x38]   ; Load val1.z1
  adc rcx, [r14-0x18]   ; Add val2.z1 with carry
  mov rdx, [r14-0x30]   ; Load val1.z2
  adc rdx, [r14-0x10]   ; Add val2.z2 with carry
  mov rbx, [r14-0x28]   ; Load val1.z3
  adc rbx, [r14-0x08]   ; Add val2.z3 with carry
  mov [r14-0x40], rax   ; Store result (4x64-bit limbs)
  mov [r14-0x38], rcx
  mov [r14-0x30], rdx
  mov [r14-0x28], rbx
        """
    )
    
    parser.add_argument(
        '--verbose', '-v',
        action='store_true',
        help='Enable verbose Z3 output'
    )
    
    parser.add_argument(
        '--timeout', '-t',
        type=int,
        default=60000,
        metavar='MS',
        help='Z3 solver timeout in milliseconds (default: 60000)'
    )
    
    parser.add_argument(
        '--single', '-s',
        nargs=2,
        type=lambda x: int(x, 0),  # Accept hex or decimal
        metavar=('VAL1', 'VAL2'),
        help='Verify single ADD operation with given values (e.g., --single 0x60 0x10)'
    )
    
    return parser.parse_args()


def main():
    """Main entry point."""
    args = parse_args()
    
    print("=" * 70)
    print("EVM AOT TRANSLATION VERIFICATION")
    print("Semantic Equivalence Proof using Z3 SMT Solver")
    print("=" * 70)
    print(f"\nConfiguration:")
    print(f"  Timeout: {args.timeout}ms")
    print(f"  Verbose: {args.verbose}")
    print()
    
    if args.single:
        # Verify single test case
        val1, val2 = args.single
        print(f"Running single verification: 0x{val1:x} + 0x{val2:x}")
        
        verifier = TranslationVerifier(timeout_ms=args.timeout, verbose=args.verbose)
        success, message = verifier.verify_add_concrete(val1, val2)
        
        if success:
            print("\n✓ Verification SUCCEEDED")
            return 0
        else:
            print("\n✗ Verification FAILED")
            return 1
    else:
        # Run full test suite (including symbolic verification!)
        print("Running verification test suite...")
        print("This includes FORMAL PROOF using symbolic execution\n")
        all_passed = run_verification_suite()
        
        if all_passed:
            return 0
        else:
            return 1


if __name__ == "__main__":
    try:
        sys.exit(main())
    except KeyboardInterrupt:
        print("\n\nInterrupted by user")
        sys.exit(130)
    except Exception as e:
        print(f"\n\nError: {e}", file=sys.stderr)
        if '--verbose' in sys.argv or '-v' in sys.argv:
            import traceback
            traceback.print_exc()
        sys.exit(1)

