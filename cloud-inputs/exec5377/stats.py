"""Summarize calls.jsonl of an xseg run. usage: stats.py DIR"""
import json
import sys
from collections import Counter, defaultdict

rows = [json.loads(l) for l in open(sys.argv[1] + "/calls.jsonl")]
tot = sum(r["t"] for r in rows)
print("calls", len(rows), "wall", round(tot, 1))
by = defaultdict(lambda: [0, 0.0])
for r in rows:
    key = ("apply" if r["apply"] else "main", "w" if r.get("w") else "",
           r.get("probe", ["-"])[0], r.get("exact", ["-"])[0], r["r"])
    by[key][0] += 1
    by[key][1] += r["t"]
for k, (n, s) in sorted(by.items(), key=lambda kv: -kv[1][1]):
    print(f"{n:6d} {s:8.1f}s", k)
parts = Counter()
for r in rows:
    for tag in ("probe", "exact"):
        if tag in r:
            parts[tag] += r[tag][1]
    parts["abs"] += r.get("abs", 0)
    parts["overhead"] += r["t"] - sum(r[t][1] for t in ("probe", "exact") if t in r) - r.get("abs", 0)
print({k: round(v, 1) for k, v in parts.items()})
# rlimit distribution of unknowns / decided
for tag in ("probe", "exact"):
    for res in ("sat", "unsat", "unknown"):
        xs = sorted(r[tag][2] for r in rows if tag in r and r[tag][0] == res)
        ts = sorted(r[tag][1] for r in rows if tag in r and r[tag][0] == res)
        if xs:
            q = lambda a, p: a[min(len(a) - 1, int(p * len(a)))]
            print(tag, res, len(xs), "rlimit p50/p90/max", q(xs, .5), q(xs, .9), xs[-1],
                  "sec p50/p90/max/sum", q(ts, .5), q(ts, .9), ts[-1], round(sum(ts), 1))
