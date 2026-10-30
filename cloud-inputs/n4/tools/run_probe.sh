#!/bin/sh
# Whole-node probe on a frozen-hex fixture (30s per query, serial), as N3's run_probe.sh, detached;
# output in cloud-inputs/n4/runs/TAG.json (probe result) and TAG.log (traced _check log), pid in TAG.pid.
# Usage (repo root): cloud-inputs/n4/tools/run_probe.sh STEM NODES.json TAG NODE_SECONDS [extra probe args]
# (e.g. --node-memory-mb 6000: the node stops and is reported inconclusive above that RSS).
# PROBE=cloud-inputs/n4/tools/probe_stacks.py STACKS_FILE=...: also dump Python stacks every 600s.
stem=$1 nodes=$2 tag=$3 seconds=$4
shift 4
mkdir -p cloud-inputs/n4/runs
( BLOCK_SUMMARY_LEMMAS=1 PYTHONHASHSEED=0 PYTHONPATH=. .venv/bin/python ${PROBE:-cloud-inputs/n2/tools/probe_traced.py} \
    "$stem" "$nodes" --output "cloud-inputs/n4/runs/$tag.json" --timeout-ms 30000 \
    --node-seconds "$seconds" "$@" > "cloud-inputs/n4/runs/$tag.log" 2>&1
  echo "$tag exit $?" >> "cloud-inputs/n4/runs/$tag.log" ) &
echo $! > "cloud-inputs/n4/runs/$tag.pid"
