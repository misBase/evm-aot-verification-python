"""Summarize solves.jsonl: solves.py DIR"""
import json
import sys
from collections import defaultdict

agg = defaultdict(lambda: [0, 0.0])
for line in open(sys.argv[1] + "/solves.jsonl"):
    r = json.loads(line)
    key = ("apply", r["apply"], r["res"]) if "apply" in r else ("solve", r["name"], r["exp"], r["ans"])
    agg[key][0] += 1
    agg[key][1] += r["t"]
for k, (n, t) in sorted(agg.items(), key=lambda kv: -kv[1][1]):
    print(f"{n:5d} {t:8.1f}s", k)
