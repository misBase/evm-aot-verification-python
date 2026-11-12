#!/bin/bash
# E4: complete contracts, V1/V2/V3 under the 3600 s budget. RQ1 Table 4 and the whole-contract figure.
# Usage: bash run.sh            (env: OUT=results dir, CPUS=0-14, MEM=24000 MiB = sum of concurrent jobs' memory caps)
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
source "$HERE/../common/env.sh"
OUT=${OUT:-$HERE/results}; CPUS=${CPUS:-0-14}; MEM=${MEM:-24000}
mkdir -p "$OUT"
"${MATRIX[@]}" --out "$OUT/r1" --cpus "$CPUS" --memory-budget "$MEM" --only whole/
"${MATRIX[@]}" --out "$OUT/r2" --cpus "$CPUS" --memory-budget "$MEM" --only whole/
"$PY" "$ARTIFACT/experiments/common/summarize.py" "$OUT"
