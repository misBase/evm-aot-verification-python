"""Summarize one experiment's result rounds as Markdown tables.

Usage: python summarize.py ROOT
ROOT holds one directory per round (r1, r2, ...), each written by harness/matrix.py; `results/` (a fresh run) and
`expected/` (the paper's runs) have the same layout. Prints
  1. outcome counts per configuration, from the first round;
  2. per input: the outcome of every round ("r1/r2/...") and the median / min-max wall time of VERIFIED runs.
Outcome classes: VERIFIED, BOUNDED, BOUND, TO, OOM, UNK, ERR, N/A (see the paper's experimental setup).
"""
import json
import statistics
import sys
from collections import Counter, defaultdict
from pathlib import Path

CLASSES = ("VERIFIED", "BOUNDED", "BOUND", "TO", "OOM", "UNK", "ERR", "N/A")


def outcome(record):
    # run_one.py writes the final class at top level, also when its guard killed the job (TO, OOM) and there is
    # no worker payload; dependency-skipped jobs carry it at top level too.
    return record.get("result") or (record.get("worker_payload") or {}).get("result") or "ERR"


def load_round(directory):
    rows = {}
    for path in sorted(Path(directory).glob("*.json")):
        if path.name.endswith(".worker.json") or path.name == "matrix.process.json":
            continue
        record = json.loads(path.read_text())
        name = path.stem.replace("__", "/")
        kind, _, rest = name.partition("/")
        target, _, config = rest.rpartition("/")
        rows[(kind, target, config)] = (outcome(record), record.get("wall_seconds"))
    return rows


def main(root):
    rounds = sorted(p for p in Path(root).iterdir() if p.is_dir() and not p.name.startswith("."))
    if not rounds:
        sys.exit(f"no round directories under {root}")
    data = [(r.name, load_round(r)) for r in rounds]
    first = data[0][1]
    configs = sorted({c for _, rows in data for (_, _, c) in rows}, key=lambda c: (len(c), c))
    print(f"## {Path(root).resolve().parent.name}: outcome counts ({data[0][0]})\n")
    print("| Configuration | " + " | ".join(CLASSES) + " |")
    print("|---|" + "---:|" * len(CLASSES))
    for config in configs:
        counts = Counter(o for (_, _, c), (o, _) in first.items() if c == config)
        print(f"| {config} | " + " | ".join(str(counts.get(k, 0)) for k in CLASSES) + " |")
    print(f"\n## Per input ({', '.join(name for name, _ in data)}; wall time of VERIFIED runs, s)\n")
    cells = defaultdict(dict)
    for (kind, target, config) in sorted({key for _, rows in data for key in rows}):
        outcomes = [rows.get((kind, target, config), ("-", None))[0] for _, rows in data]
        walls = [w for _, rows in data for (o, w) in [rows.get((kind, target, config), ("-", None))]
                 if o == "VERIFIED" and isinstance(w, (int, float))]
        text = "/".join(o if o != "VERIFIED" else "P" for o in outcomes)
        if walls:
            text += f" {statistics.median(walls):.1f}" + (f" [{min(walls):.1f}-{max(walls):.1f}]" if len(walls) > 1 else "")
        cells[(kind, target)][config] = text
    print("| Input | " + " | ".join(configs) + " |")
    print("|---|" + "---|" * len(configs))
    for (kind, target), row in sorted(cells.items()):
        print(f"| {kind}/{target} | " + " | ".join(row.get(c, "") for c in configs) + " |")


if __name__ == "__main__":
    main(sys.argv[1])
