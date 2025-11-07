#!/usr/bin/env python3
"""Test the main verifier."""

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



