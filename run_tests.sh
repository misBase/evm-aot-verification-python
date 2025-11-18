#!/bin/bash
# Run all tests for the EVM AOT verification system using pytest

set -e

echo "=========================================="
echo "Running EVM AOT Verification Tests"
echo "=========================================="
echo ""

# Run all tests using pytest with python3
# -v: verbose output
# -s: show print statements
# --tb=short: shorter traceback format
python3 -m pytest tests/ -v -s --tb=short

