#!/bin/bash
# Kick-the-tires check (a few minutes): one core, one small program under every configuration including V3 with
# its trace, and one admitted function slice, through the same harness as the full experiments.
set -euo pipefail
source "$(cd "$(dirname "$0")" && pwd)/env.sh"
OUT=${OUT:-$ARTIFACT/experiments/smoke-results}
rm -rf "$OUT"
for only in single/ADD/ prog/two_block/ fnx/ENSRegistry.owner/V2; do
  "${MATRIX[@]}" --out "$OUT/r1" --cpus "${CPUS:-0-3}" --memory-budget "${MEM:-8000}" --only "$only"
done
"$PY" "$ARTIFACT/experiments/common/summarize.py" "$OUT"
verified=$(grep -l '"result": "VERIFIED"' "$OUT"/r1/*.json | grep -vc worker.json || true)
echo "smoke: $verified jobs VERIFIED (expected 10: ADD V1/V2; two_block V1/V2/V2-O1/V2-O2/V3; owner V2/V2-O1/V2-O2)"
