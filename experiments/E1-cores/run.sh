#!/bin/bash
# E1: instruction cores. RQ1 Table 1 (microbenchmarks); RQ2 Table 2 (microbenchmarks) and Fig. 6.
# Usage: bash run.sh            (env: OUT=results dir, CPUS=0-3, MEM=8000 MiB = sum of concurrent jobs' memory caps)
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
source "$HERE/../common/env.sh"
OUT=${OUT:-$HERE/results}; CPUS=${CPUS:-0-3}; MEM=${MEM:-8000}
mkdir -p "$OUT"
"${MATRIX[@]}" --out "$OUT/r1" --cpus "$CPUS" --memory-budget "$MEM" --only single/
# Rounds 2 and 3 repeat only the jobs whose round-1 wall time was below 300 s (the paper's repetition rule).
"$PY" "$ARTIFACT/experiments/common/repeat_names.py" "$OUT/r1" > "$OUT/repeat-names.txt"
for round in r2 r3; do
  "${MATRIX[@]}" --out "$OUT/$round" --cpus "$CPUS" --memory-budget "$MEM" --only single/ --names "$OUT/repeat-names.txt"
done
"$PY" "$ARTIFACT/experiments/common/summarize.py" "$OUT"
