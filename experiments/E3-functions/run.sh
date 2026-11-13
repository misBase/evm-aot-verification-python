#!/bin/bash
# E3: admitted ENSRegistry function slices. Supplementary O1/O2 ablation, not reported in the paper.
# Usage: bash run.sh            (env: OUT=results dir, CPUS=0-7, MEM=12000 MiB = sum of concurrent jobs' memory caps)
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
source "$HERE/../common/env.sh"
OUT=${OUT:-$HERE/results}; CPUS=${CPUS:-0-7}; MEM=${MEM:-12000}
mkdir -p "$OUT"
"${MATRIX[@]}" --out "$OUT/r1" --cpus "$CPUS" --memory-budget "$MEM" --only fnx/
"$PY" "$ARTIFACT/experiments/common/summarize.py" "$OUT"
