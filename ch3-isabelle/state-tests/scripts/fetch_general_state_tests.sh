#!/usr/bin/env bash
set -euo pipefail

BENCH_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TESTS_DIR="$BENCH_DIR/tests/ethereum-tests/GeneralStateTests"

if [ -d "$TESTS_DIR" ] && [ "$(find "$TESTS_DIR" -type f -name '*.json' | head -n 1)" ]; then
  exit 0
fi

mkdir -p "$BENCH_DIR/tests"
echo "[benchmark] fetching ethereum/tests GeneralStateTests into $TESTS_DIR"

if [ ! -d "$BENCH_DIR/tests/ethereum-tests/.git" ]; then
  git clone --depth 1 --filter=blob:none --sparse \
    https://github.com/ethereum/tests.git \
    "$BENCH_DIR/tests/ethereum-tests"
fi

git -C "$BENCH_DIR/tests/ethereum-tests" sparse-checkout set GeneralStateTests