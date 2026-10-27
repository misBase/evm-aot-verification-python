#!/bin/sh
# Whole-node probe on a frozen-hex fixture, as the task prescribes (30s per query, serial).
# Usage (repo root): cloud-inputs/n2/tools/run_probe.sh STEM NODES.json TAG NODE_SECONDS [extra probe args]
# Writes cloud-inputs/n3/runs/TAG.json (probe output) and TAG.log (traced _check log).
stem=$1 nodes=$2 tag=$3 seconds=$4
shift 4
mkdir -p cloud-inputs/n3/runs
BLOCK_SUMMARY_LEMMAS=1 PYTHONHASHSEED=0 PYTHONPATH=. .venv/bin/python cloud-inputs/n2/tools/probe_traced.py \
    "$stem" "$nodes" --output "cloud-inputs/n3/runs/$tag.json" --timeout-ms 30000 \
    --node-seconds "$seconds" "$@" > "cloud-inputs/n3/runs/$tag.log" 2>&1
echo "$tag exit $?" >> cloud-inputs/n3/runs/$tag.log
