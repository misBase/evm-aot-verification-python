#!/usr/bin/env bash
# Fetch the GeneralStateTests snapshot used in the paper: ethereum/tests at a fixed commit ships the state tests as
# fixtures_general_state_tests.tgz (2,642 JSON files); download it, check its hash and unpack it into tests/.
set -euo pipefail

COMMIT=c67e485ff8b5be9abc8ad15345ec21aa22e290d9
SHA256=82bc3cb1c23f48b2b8a2b3d9cb5d9b96ddf6c31683f75368173bee3b25a24274
URL="https://raw.githubusercontent.com/ethereum/tests/$COMMIT/fixtures_general_state_tests.tgz"

BENCH_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TESTS_DIR="$BENCH_DIR/tests/GeneralStateTests"

if [ -d "$TESTS_DIR" ] && [ "$(find "$TESTS_DIR" -type f -name '*.json' | head -n 1)" ]; then
  exit 0
fi

mkdir -p "$BENCH_DIR/tests"
ARCHIVE="$BENCH_DIR/tests/fixtures_general_state_tests.tgz"
echo "[benchmark] fetching ethereum/tests@$COMMIT fixtures_general_state_tests.tgz"
curl -fsSL -o "$ARCHIVE" "$URL"

actual="$( (sha256sum "$ARCHIVE" 2>/dev/null || shasum -a 256 "$ARCHIVE") | cut -d' ' -f1)"
if [ "$actual" != "$SHA256" ]; then
  echo "[benchmark] sha256 mismatch: got $actual, expected $SHA256" >&2
  exit 1
fi
tar -xzf "$ARCHIVE" -C "$BENCH_DIR/tests"
echo "[benchmark] $(find "$TESTS_DIR" -type f -name '*.json' | wc -l | tr -d ' ') JSON files in $TESTS_DIR"
