#!/bin/sh
# Whole-node memory probe (mem_probe.py) on a frozen fixture, detached; its pid goes to TAG.pid.
# Usage (repo root): cloud-inputs/n4/tools/run_mem.sh STEM NODES.json INDEX TAG [mem_probe args]
stem=$1 nodes=$2 index=$3 tag=$4
shift 4
mkdir -p cloud-inputs/n4/runs
BLOCK_SUMMARY_LEMMAS=1 PYTHONHASHSEED=0 PYTHONPATH=. nohup .venv/bin/python cloud-inputs/n4/tools/mem_probe.py \
    "$stem" "$nodes" "$index" "cloud-inputs/n4/runs/$tag.json" "$@" > "cloud-inputs/n4/runs/$tag.log" 2>&1 &
echo $! > "cloud-inputs/n4/runs/$tag.pid"
