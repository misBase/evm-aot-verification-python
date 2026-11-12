"""Scheduling what-if on measured instance durations (no solving): sim.py final1/*.json

Durations are the production final records; hidden (overwritten) attempt time
is added as evenly spread work. Policies, same worker count as production:
  production : measured proof-phase span
  LPT-oracle : longest-processing-time-first with the true durations
  LPT-block  : longest-first by the block's median duration among its other
               instances (a cost model available after a block's first proof)
  lower bound: max(longest instance, total work / workers)
Shortcut: assumes durations independent of order (no cache effects between siblings).
"""
import heapq
import json
import statistics
import sys
from collections import defaultdict
from pathlib import Path


def makespan(durations, workers):
    loads = [0.0] * workers
    heapq.heapify(loads)
    for d in durations:
        heapq.heappush(loads, heapq.heappop(loads) + d)
    return max(loads)


def main():
    rows = []
    for path in sys.argv[1:]:
        d = json.loads(Path(path).read_text())
        cfg = d["configuration"]
        workers = cfg.get("node_workers") or cfg.get("workers")
        inst = [i for v in d["diagnostics"].values() for i in v["instances"] if i.get("started_at")]
        t0, t1 = min(i["started_at"] for i in inst), max(i["finished_at"] for i in inst)
        span = t1 - t0
        busy = defaultdict(list)
        for i in inst:
            busy[i["pid"]].append((i["started_at"], i["finished_at"]))
        hidden = sum(max(0.0, b[0] - a[1]) for s in busy.values() for a, b in zip(sorted(s), sorted(s)[1:]))
        dur = [i["seconds"] for i in inst]
        extra = hidden / workers
        by_block = defaultdict(list)
        for i in inst:
            by_block[i["spec"].split(",")[0]].append(i["seconds"])
        guess = [statistics.median(by_block[i["spec"].split(",")[0]]) for i in inst]
        order_block = [x for _, x in sorted(zip(guess, dur), key=lambda t: -t[0])]
        row = dict(contract=Path(d["stem"]).name + ("" if d["status"] == "verified" else f" ({d['status']})"),
                   workers=workers, production=round(span),
                   lpt_oracle=round(makespan(sorted(dur, reverse=True), workers) + extra),
                   lpt_block=round(makespan(order_block, workers) + extra),
                   lower_bound=round(max(max(dur), (sum(dur) + hidden) / workers)),
                   longest=round(max(dur)), hidden=round(hidden))
        row["loss_vs_lpt_oracle"] = round(1 - row["lpt_oracle"] / span, 3)
        rows.append(row)
        print(json.dumps(row))
    return rows


if __name__ == "__main__":
    main()
