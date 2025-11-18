#!/usr/bin/env python3
"""
EVM AOT Translation Verification Tool

This script verifies the semantic equivalence between EVM IR (from JSON)
and AOT-compiled x86-64 machine code (from hex string).

Usage:
    python main.py <ir_json_path> <x86_hex> [--base-addr ADDR] [--timeout MS] [--verbose]
"""

import argparse
import sys
from evm_ir.program import EVMProgram
from evm_ir.json_parser import load_ir_from_json
from x86_64.program import X86Program
from verification.program_verifier import ProgramEquivalenceChecker


def parse_args():
    """Parse command-line arguments."""
    parser = argparse.ArgumentParser(
        description="Verify semantic equivalence between EVM IR and x86-64 machine code",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python main.py tests/data/example_ir.json 498b46c0490346e0...
  python main.py contract.ir.json 498b46c0... --base-addr 0x6c
  python main.py contract.ir.json 498b46c0... --timeout 30000 --verbose
        """
    )
    
    parser.add_argument(
        'ir_json_path',
        help='Path to EVM IR JSON file'
    )
    
    parser.add_argument(
        'x86_hex',
        help='x86-64 machine code as hex string'
    )
    
    parser.add_argument(
        '--base-addr',
        type=lambda x: int(x, 0),  # Accept hex or decimal
        default=0,
        metavar='ADDR',
        help='Base address for x86 code (default: 0)'
    )
    
    parser.add_argument(
        '--timeout', '-t',
        type=int,
        default=60000,
        metavar='MS',
        help='Z3 solver timeout in milliseconds (default: 60000)'
    )
    
    parser.add_argument(
        '--verbose', '-v',
        action='store_true',
        help='Enable verbose output'
    )
    
    return parser.parse_args()


def verify_programs(ir_json_path: str, x86_hex: str, base_addr: int, timeout_ms: int, verbose: bool):
    """Verify equivalence between EVM and x86 programs.
    
    Args:
        ir_json_path: Path to EVM IR JSON file
        x86_hex: Hex-encoded x86 machine code
        base_addr: Base address for x86 code
        timeout_ms: Solver timeout in milliseconds
        verbose: Enable verbose output
        
    Returns:
        (verified, message) where verified is True if programs are equivalent
    """
    if verbose:
        print(f"Loading EVM IR from: {ir_json_path}")
        print(f"Loading x86 code from hex: {x86_hex[:64]}..." if len(x86_hex) > 64 else f"Loading x86 code from hex: {x86_hex}")
        print(f"Base address: 0x{base_addr:x}")
        print(f"Timeout: {timeout_ms}ms")
        print()
    
    # Load EVM program from JSON
    try:
        compiler_result = load_ir_from_json(ir_json_path)
        evm_program = EVMProgram(compiler_result)
    except FileNotFoundError:
        return False, f"Error: File not found: {ir_json_path}"
    except Exception as e:
        return False, f"Error loading EVM IR: {e}"
    
    # Create x86 program from hex
    try:
        x86_program = X86Program.from_hex(x86_hex, base_addr=base_addr)
    except Exception as e:
        return False, f"Error parsing x86 hex: {e}"
    
    # Verify using ProgramEquivalenceChecker
    checker = ProgramEquivalenceChecker(timeout_ms=timeout_ms, verbose=verbose)
    return checker.verify_program_pair(evm_program, x86_program)


def main():
    """Main entry point."""
    args = parse_args()
    
    if args.verbose:
        print("=" * 70)
        print("EVM AOT TRANSLATION VERIFICATION")
        print("=" * 70)
        print()
    
    # Verify programs
    verified, message = verify_programs(
        args.ir_json_path,
        args.x86_hex,
        args.base_addr,
        args.timeout,
        args.verbose
    )
    
    # Output result
    if verified:
        print("✓ VERIFIED: Programs are semantically equivalent")
        if args.verbose and message:
            print(f"  {message}")
        return 0
    else:
        print("✗ VERIFICATION FAILED")
        if message:
            print(f"  {message}")
        return 1


if __name__ == "__main__":
    try:
        sys.exit(main())
    except KeyboardInterrupt:
        print("\n\nInterrupted by user", file=sys.stderr)
        sys.exit(130)
    except Exception as e:
        print(f"\n\nError: {e}", file=sys.stderr)
        if '--verbose' in sys.argv or '-v' in sys.argv:
            import traceback
            traceback.print_exc()
        sys.exit(1)
