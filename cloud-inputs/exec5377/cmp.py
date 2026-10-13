"""Compare replay files against the record: cmp.py DIR FILE [FILE...]"""
import json
import sys
from collections import Counter

d = sys.argv[1]
rows = [json.loads(l) for l in open(d + "/calls.jsonl")]
for f in sys.argv[2:]:
    rep = [json.loads(l) for l in open(d + "/" + f)]
    rec_t = sum(rows[x["i"]]["t"] for x in rep)
    t = sum(x["t"] for x in rep)
    flips = Counter((x["rec"], x["dec"]) for x in rep if x["rec"] != x["dec"])
    detail = Counter(tuple((k, v) for k, v in x.items() if k in ("probe", "pin", "exact", "sres", "pool")) for x in rep)
    print(f, "n", len(rep), "replay", round(t, 1), "record", round(rec_t, 1), "flips(rec,dec)", dict(flips))
    for k, v in detail.most_common(8):
        print("   ", v, k, round(sum(x["t"] for x in rep if tuple((a, b) for a, b in x.items() if a in ("probe", "pin", "exact", "sres", "pool")) == k), 1))
