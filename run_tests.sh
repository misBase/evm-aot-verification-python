#!/bin/bash
# Run all tests for the EVM AOT verification system

set -e

echo "=========================================="
echo "Running EVM AOT Verification Tests"
echo "=========================================="
echo ""

# Test 1: Basic tests
echo "[1/6] Running basic tests..."
python3 tests/test_basic.py
echo ""

# Test 2: IR JSON parsing tests
echo "[2/6] Running IR JSON parsing tests..."
python3 tests/test_ir_json.py
echo ""

# Test 3: Verifier tests
echo "[3/6] Running verifier tests..."
python3 tests/test_verifier.py
echo ""

# Test 4: ADD with carry tests
echo "[4/6] Running ADD with carry tests..."
python3 tests/test_add_carry.py
echo ""

# Test 5: Uint256.add_semantics() direct tests
echo "[5/6] Running Uint256.add_semantics() direct tests..."
python3 tests/test_uint256_add.py
echo ""

# Test 6: Disassembler tests
echo "[6/6] Running disassembler tests..."
python3 tests/test_disassembler.py
echo ""

echo "=========================================="
echo "All tests passed! ✓"
echo "=========================================="

