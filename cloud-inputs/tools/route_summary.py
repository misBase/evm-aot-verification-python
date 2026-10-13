"""Summarise route_trace.py JSON files: route_summary.py OUT_DIR [--per-obligation]

Per goal-split part (or unsplit obligation): which stage proved it and the
time spent before it (failed stages). Totals per stage: tries, wins, seconds
on wins, seconds on misses.
"""
import glob
import json
import sys
from collections import defaultdict


def leaf_frames(data):
    names = [f["name"] for f in data["frames"]]
    for frame in data["frames"]:
        if not any(n.startswith(frame["name"] + "_goal_") for n in names):
            yield frame


def main():
    files = sorted(glob.glob(sys.argv[1] + "/*.json"))
    per = "--per-obligation" in sys.argv
    stats = defaultdict(lambda: [0, 0, 0.0, 0.0])  # tries, wins, win_s, miss_s
    total = 0.0
    for path in files:
        data = json.load(open(path))
        total += data["seconds"]
        print(f"{data['name']}: {data['answer']} {data['seconds']}s")
        for frame in data["frames"]:
            if any(f["name"].startswith(frame["name"] + "_goal_") for f in data["frames"]) and per:
                spent = sum(m[2] for m in frame["marks"])
                print(f"   [{frame['name'].rsplit('_goal_', 1)[-1] if '_goal_' in frame['name'] else 'top'}] own {spent:.1f}s")
        for frame in data["frames"]:
            winner, before = None, 0.0
            for label, answer, seconds in frame["marks"]:
                if label in ("gap", "pre-normalize", "split"):
                    continue
                s = stats[label]
                s[0] += 1
                if answer == "unsat" and winner is None:
                    s[1] += 1
                    s[2] += seconds
                    winner = (label, seconds)
                else:
                    s[3] += seconds
                    if winner is None:
                        before += seconds
            if per:
                part = frame["name"].rsplit("_goal_", 1)[-1] if "_goal_" in frame["name"] else "-"
                print(f"   part {part}: won by {winner and winner[0]} ({winner and winner[1]}s) after {before:.1f}s"
                      f" of failed stages; marks: " + " ".join(f"{l}={a and a[:3]}:{s}" for l, a, s in frame["marks"]
                                                            if l not in ("gap", "pre-normalize")))
        if per and data.get("probes"):
            print("   probes:", json.dumps(data["probes"]))
    print(f"\nTOTAL {total:.1f}s over {len(files)} obligations")
    print(f"{'stage':14} {'tries':>5} {'wins':>5} {'win_s':>9} {'miss_s':>9}")
    for label, (tries, wins, win_s, miss_s) in sorted(stats.items(), key=lambda kv: -kv[1][3]):
        print(f"{label:14} {tries:5d} {wins:5d} {win_s:9.1f} {miss_s:9.1f}")
    probes = defaultdict(lambda: defaultdict(float))
    for path in files:
        for k, v in json.load(open(path)).get("probes", {}).items():
            for kk, vv in v.items():
                probes[k][kk] += vv
    for k, v in probes.items():
        print(f"probe {k}: " + ", ".join(f"{kk}={vv:.1f}" for kk, vv in v.items()))


if __name__ == "__main__":
    main()
