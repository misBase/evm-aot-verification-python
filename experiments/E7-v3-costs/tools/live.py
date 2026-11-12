"""Where is a running replay now? live.py RUN_DIR...  (open spans, checks so far by phase, slowest checks)"""
import json
import sys
import time
from collections import defaultdict
from pathlib import Path

for run in sys.argv[1:]:
    open_, done = {}, []
    for f in Path(run, "events").glob("pid-*.jsonl"):
        for line in f.open():
            try:
                d = json.loads(line)
            except json.JSONDecodeError:
                continue
            if d["event"] == "enter":
                open_[d["id"]] = d
            elif d["event"] in ("return", "exception"):
                e = open_.pop(d["id"], None)
                if d["label"] == "check" and e:
                    done.append((d["wall_inclusive_s"], e["metadata"].get("name"), e["metadata"].get("phase"),
                                 d["metadata"].get("answer"), d["metadata"].get("routes")))
    now = time.monotonic()
    stack = sorted(open_.values(), key=lambda d: d["monotonic"])
    print("==", Path(run).name)
    print("  open:", " > ".join(f"{d['label']}({now - d['monotonic']:.0f}s)" for d in stack
                                if d["label"] not in ("program.verify",))[-400:])
    by = defaultdict(lambda: [0, 0.0])
    for w, _, ph, _, _ in done:
        by[ph][0] += 1
        by[ph][1] += w
    print("  checks:", {k: (v[0], round(v[1])) for k, v in by.items()})
    for w, name, ph, ans, routes in sorted(done, reverse=True)[:4]:
        top = sorted((routes or {}).items(), key=lambda kv: -kv[1][1])[:3]
        print(f"  slow {w:6.1f}s {name} [{ph}] {ans} {top}")
