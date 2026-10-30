#!/bin/sh
# Log the RSS of TAG's python process every SECONDS to cloud-inputs/n4/runs/TAG.rss until it exits.
# Usage (repo root): cloud-inputs/n4/tools/rss_log.sh TAG [SECONDS]
tag=$1 every=${2:-300}
out=cloud-inputs/n4/runs/$tag.rss
sleep 5
pid=$(pgrep -P "$(cat cloud-inputs/n4/runs/$tag.pid)" -f "probe_traced|probe_stacks|h2_triage|trace_coverage|save_reach" | head -1)
[ -z "$pid" ] && pid=$(cat cloud-inputs/n4/runs/$tag.pid)
while kill -0 "$pid" 2>/dev/null; do
    echo "$(date -u +%H:%M:%S) $(awk '/VmRSS|VmHWM/ {printf "%s %s ", $1, $2}' /proc/$pid/status)" >> "$out"
    sleep "$every"
done
echo "$(date -u +%H:%M:%S) exited" >> "$out"
