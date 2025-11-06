#!/usr/bin/env python3
"""Test the main verifier."""

import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from verifier import TranslationVerifier
from z3 import simplify, BitVecVal


def test_verifier_import():
    """Test that verifier can be imported."""
    print("✓ Verifier imported successfully")


def test_verifier_add_concrete():
    """Test concrete ADD verification."""
    print("\nTesting concrete ADD verification...")
    
    verifier = TranslationVerifier(timeout_ms=10000, verbose=False)
    
    # Test with simple values
    verified, msg = verifier.verify_add_concrete(0x60, 0x10)
    
    print(f"  Result: {verified}")
    print(f"  Message: {msg[:50]}...")
    
    assert verified, "ADD verification should succeed"
    print("✓ Concrete ADD verification test passed")


def main():
    """Run all tests."""
    print("=" * 70)
    print("Testing Verifier")
    print("=" * 70)
    
    try:
        test_verifier_import()
        test_verifier_add_concrete()
        
        print("\n" + "=" * 70)
        print("All tests passed! ✓")
        print("=" * 70)
        return True
    except Exception as e:
        print(f"\n✗ Test failed with error: {e}")
        import traceback
        traceback.print_exc()
        return False


if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)

