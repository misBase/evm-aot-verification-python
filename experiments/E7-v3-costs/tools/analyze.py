"""Aggregate one observed run: analyze.py RUN_DIR [--json OUT]

Buckets partition worker task time: each span's same-thread exclusive wall goes
to its label (a `check` goes to check@<enclosing phase>), so buckets add up to
the summed task wall. Counters (z3.check, isolated child, ...) are a separate
cross-cut: time inside the solver vs everything else.
"""
import argparse
import json
from collections import defaultdict
from pathlib import Path


def load(run):
    spans = []
    for f in sorted((Path(run) / "events").glob("pid-*.jsonl")):
        enter = {}
        for line in f.open():
            try:
                d = json.loads(line)
            except json.JSONDecodeError:
                continue  # a killed worker's last line
            if d["event"] == "enter":
                enter[d["id"]] = d
            elif d["event"] in ("return", "exception"):
                e = enter.pop(d["id"], None)
                spans.append(dict(pid=d["pid"], id=d["id"], parent=d["parent_id"], label=d["label"],
                                  wall=d["wall_inclusive_s"], excl=d["wall_same_thread_exclusive_s"],
                                  cpu=d["thread_cpu_inclusive_s"], exc=d["original_exception"],
                                  start=e["monotonic"] if e else None,
                                  meta=dict(e["metadata"] if e else {}, **(d.get("metadata") or {}))))
        for e in enter.values():  # still open when the process ended (killed / wall)
            spans.append(dict(pid=e["pid"], id=e["id"], parent=e["parent_id"], label=e["label"], wall=None,
                              excl=None, cpu=None, exc="UNFINISHED", start=e["monotonic"], meta=e["metadata"]))
    return spans


def bucket(s):
    return f"check@{s['meta'].get('phase', '?')}" if s["label"] == "check" else s["label"]


def summarize(run):
    spans = load(run)
    tasks = [s for s in spans if s["label"] == "task"]
    by_id = {(s["pid"], s["id"]): s for s in spans}

    def under_task(s):
        while s is not None:
            if s["label"] == "task":
                return True
            s = by_id.get((s["pid"], s["parent"]))
        return False
    buckets = defaultdict(lambda: [0, 0.0])
    for s in spans:
        if s["excl"] is not None and under_task(s):
            b = buckets[bucket(s)]
            b[0] += 1
            b[1] += s["excl"]
    task_wall = sum(s["wall"] for s in tasks if s["wall"] is not None)
    counts = defaultdict(lambda: [0, 0.0])
    for s in tasks:
        for k, (n, sec) in (s["meta"].get("counts") or {}).items():
            counts[k][0] += n
            counts[k][1] += sec
    routes = defaultdict(lambda: defaultdict(lambda: [0, 0, 0.0, 0.0]))  # phase -> route -> runs, wins, s, lost s
    checks = [s for s in spans if s["label"] == "check" and s["wall"] is not None]
    for s in checks:
        r = s["meta"].get("routes") or {}
        won = any(w for w, _ in r.values())
        for name, (w, sec) in r.items():
            row = routes[s["meta"].get("phase", "?")][name]
            row[0] += 1
            row[1] += w
            row[2] += sec
            if not w:
                row[3] += sec  # spent on a route that did not refute it
    slow = sorted(checks, key=lambda s: -s["wall"])[:15]
    program = {s["label"]: round(s["wall"], 1) for s in spans if s["label"].startswith("program.") and s["wall"]}
    unfinished = [dict(label=s["label"], meta={k: v for k, v in s["meta"].items() if k in ("spec", "name", "phase")})
                  for s in spans if s["exc"] == "UNFINISHED" and s["label"] in ("task", "check", "h2.close_edge")]
    return dict(
        run=str(run), program=program, tasks=len(tasks), task_wall=round(task_wall, 1),
        buckets={k: dict(n=v[0], s=round(v[1], 1), share=round(v[1] / task_wall, 4) if task_wall else None)
                 for k, v in sorted(buckets.items(), key=lambda kv: -kv[1][1])},
        counters={k: dict(n=v[0], s=round(v[1], 1), share=round(v[1] / task_wall, 4) if task_wall else None)
                  for k, v in sorted(counts.items(), key=lambda kv: -kv[1][1])},
        routes={ph: {k: dict(runs=v[0], wins=v[1], s=round(v[2], 1), lost_s=round(v[3], 1))
                     for k, v in sorted(t.items(), key=lambda kv: -kv[1][2])} for ph, t in routes.items()},
        slow_checks=[dict(wall=round(s["wall"], 1), name=s["meta"].get("name"), phase=s["meta"].get("phase"),
                          proved=s["meta"].get("proved"), answer=s["meta"].get("answer"),
                          routes=s["meta"].get("routes"), exported=s["meta"].get("exported")) for s in slow],
        task_rows=[dict(spec=s["meta"].get("spec"), chain=s["meta"].get("chain"), contexts=s["meta"].get("contexts"),
                        wall=None if s["wall"] is None else round(s["wall"], 1), closed=s["meta"].get("closed"),
                        kind=s["meta"].get("proof_kind"), lemma_s=s["meta"].get("lemma_seconds"),
                        z3=(s["meta"].get("counts") or {}).get("z3.check"), rss=s["meta"].get("maxrss_mb"))
                   for s in tasks],
        unfinished=unfinished)


def main():
    p = argparse.ArgumentParser()
    p.add_argument("run")
    p.add_argument("--json")
    a = p.parse_args()
    r = summarize(a.run)
    if a.json:
        Path(a.json).write_text(json.dumps(r, indent=1))
    print("program", r["program"], "tasks", r["tasks"], "task_wall", r["task_wall"])
    print("buckets (exclusive, partition of task wall):")
    for k, v in list(r["buckets"].items())[:14]:
        print(f"  {k:28s} {v['s']:>9} s  {100 * (v['share'] or 0):5.1f}%  n={v['n']}")
    print("counters (cross-cut):")
    for k, v in r["counters"].items():
        print(f"  {k:28s} {v['s']:>9} s  {100 * (v['share'] or 0):5.1f}%  n={v['n']}")
    for ph, t in r["routes"].items():
        print("routes @", ph, {k: (v["wins"], v["runs"], v["s"], v["lost_s"]) for k, v in list(t.items())[:8]})
    for s in r["slow_checks"][:6]:
        print("  slow", s)
    print("unfinished", r["unfinished"][:5])


if __name__ == "__main__":
    main()
