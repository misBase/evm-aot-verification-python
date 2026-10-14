"""One line per route_trace JSON: answer, seconds, goal-part winners, light probes at _retry_with_uf_unification.
Usage: summ.py FILE.json..."""
import json
import sys

for path in sys.argv[1:]:
    d = json.load(open(path))
    parts = []
    for f in d["frames"]:
        if "_goal_" not in f["name"]:
            continue
        k = f["name"].split("_goal_")[1]
        marks = [m for m in f["marks"] if m[0] not in ("gap", "pre-normalize")]
        win = [m for m in marks if m[1] == "unsat"]
        before = sum(m[2] for m in marks[:marks.index(win[0])]) if win else sum(m[2] for m in marks)
        parts.append(f"{k}:{win[0][0] + ' ' + str(win[0][2]) + 's' if win else 'none'} (before {before:.0f}s)")
    probes = {k: v for k, v in d["probes"].items() if k.startswith("light<_retry") and any(v.values())}
    print(path.rsplit("/", 2)[-2] + "/" + path.rsplit("/", 1)[-1], d["answer"], d["seconds"])
    for p in parts:
        if "unsat 0.0" not in p:
            print("   ", p)
    for k, v in probes.items():
        print("    ", k, v)
