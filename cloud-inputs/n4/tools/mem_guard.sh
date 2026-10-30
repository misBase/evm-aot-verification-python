#!/bin/sh
# Keep the container away from the (cgroup) OOM killer, which takes the biggest process, usually a
# long node run: every 15s, if the headroom of this shell's memory cgroup (limit - usage; host
# MemAvailable when cgroup v1 sets no limit) is below MIN_MB (default 1500), kill the largest
# diagnostic process (node_profile / dump_paths / row_group / regress / h2_triage, or a probe whose
# output tag starts with "tri-") and log it to cloud-inputs/n4/runs/mem_guard.log.
min=${1:-1500}
log=cloud-inputs/n4/runs/mem_guard.log
cg=/sys/fs/cgroup/memory$(awk -F: '$2 == "memory" {print $3}' /proc/self/cgroup)
while true; do
    if [ -r "$cg/memory.limit_in_bytes" ] && [ "$(cat "$cg/memory.limit_in_bytes")" -lt 1000000000000 ]; then
        avail=$(( ($(cat "$cg/memory.limit_in_bytes") - $(cat "$cg/memory.usage_in_bytes")) / 1048576 ))
    else
        avail=$(awk '/MemAvailable/ {print int($2 / 1024)}' /proc/meminfo)
    fi
    if [ "$avail" -lt "$min" ]; then
        victim=$(ps -eo pid,rss,args --sort=-rss | grep "venv/bin/python" | grep -v grep |
                 grep -E "node_profile|dump_paths|row_group|regress|h2_triage|runs/tri-" | head -1)
        if [ -n "$victim" ]; then
            kill $(echo "$victim" | awk '{print $1}')
            echo "$(date -u +%H:%M:%S) headroom ${avail} MB: killed $(echo "$victim" | cut -c1-200)" >> "$log"
        fi
    fi
    sleep 15
done
