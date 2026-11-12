#!/bin/bash
# E5: V3 (mixed mode) on the complete contracts with an extended budget: complete program certificates.
# Usage: bash run.sh [CONTRACT ...]     (default: all six)
#   env: OUT=results dir, WORKERS=node workers (13), NODE_MB=per-node memory cap (6000; Pool uses POOL_NODE_MB=9000),
#        CPUS=taskset CPU list (0-14)
# Each contract runs once with a fresh proof cache. Expect hours per contract on a 16-core / 32 GB host (see README).
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
source "$HERE/../common/env.sh"
OUT=${OUT:-$HERE/results}; WORKERS=${WORKERS:-13}; NODE_MB=${NODE_MB:-6000}; POOL_NODE_MB=${POOL_NODE_MB:-9000}
CPUS=${CPUS:-0-14}
CONTRACTS=("$@")
[ ${#CONTRACTS[@]} -gt 0 ] || CONTRACTS=(ENSRegistry Permit2 Safe CErc20 PoolManager Pool)
TASKSET=()
command -v taskset > /dev/null && TASKSET=(taskset -c "$CPUS")
for c in "${CONTRACTS[@]}"; do
  run="$OUT/$c"
  if [ -e "$run" ]; then echo "skip $c: $run exists (results are never reused)"; continue; fi
  mkdir -p "$run"
  node_mb=$NODE_MB; [ "$c" = Pool ] && node_mb=$POOL_NODE_MB
  echo "$(date '+%F %T') start $c (workers=$WORKERS, node memory=${node_mb} MB)"
  ( cd "$VALIDATOR" && BLOCK_SUMMARY_LEMMAS=1 BLOCK_PROOF_CACHE="$run/cache.sqlite" PYTHONHASHSEED=0 PYTHONPATH=. \
    "${TASKSET[@]}" "$PY" -m tools.verify_block_lockstep "$FIXTURES/$c" \
      --gas-check full --timeout-ms 30000 --first-pass-node-seconds 300 --node-seconds 28800 \
      --max-depth 400 --max-instances 8192 --max-parameter-values 32 --wall-seconds 259200 --hard-wall-seconds 262000 \
      --summaries --discover-first --constant-insensitive --node-workers "$WORKERS" --pair-workers-per-node 1 \
      --node-memory-mb "$node_mb" --status-dir "$run/status" --results-dir "$run/results" --output "$run/report.json" \
      --instruction-hints "$PAPER_HINTS_DIR/trace-$c.json" > "$run/log.txt" 2>&1 ) || true
  echo "$(date '+%F %T') done $c"
done
"$PY" "$HERE/table.py" "$OUT"
