#!/bin/bash
# E2: small programs. RQ1 small-program column of Table 3 and the program figure; RQ2 Table 6.
# Usage: bash run.sh            (env: OUT=results dir, CPUS=0-7, MEM=12000 MiB = sum of concurrent jobs' memory caps)
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
source "$HERE/../common/env.sh"
OUT=${OUT:-$HERE/results}; CPUS=${CPUS:-0-7}; MEM=${MEM:-12000}
mkdir -p "$OUT"
"${MATRIX[@]}" --out "$OUT/r1" --cpus "$CPUS" --memory-budget "$MEM" --only prog/
# Rounds 2 and 3 repeat only the jobs whose round-1 wall time was below 300 s (the paper's repetition rule).
"$PY" "$ARTIFACT/experiments/common/repeat_names.py" "$OUT/r1" > "$OUT/repeat-names.txt"
for round in r2 r3; do
  "${MATRIX[@]}" --out "$OUT/$round" --cpus "$CPUS" --memory-budget "$MEM" --only prog/ --names "$OUT/repeat-names.txt"
done
"$PY" "$ARTIFACT/experiments/common/summarize.py" "$OUT"
