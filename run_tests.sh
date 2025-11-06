#!/bin/bash
# Run all tests for the EVM AOT verification system using pytest

set -e

echo "=========================================="
echo "Running EVM AOT Verification Tests"
echo "=========================================="
echo ""

# Run all tests using pytest
# -v: verbose output
# -s: show print statements
# --tb=short: shorter traceback format
pytest tests/ -v -s --tb=short

echo ""
echo "=========================================="
echo "All tests passed! ✓"
echo "=========================================="

