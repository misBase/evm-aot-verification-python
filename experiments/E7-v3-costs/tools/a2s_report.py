"""A2-S: PPS-weighted share of each cost category per contract.  a2s_report.py SAMPLE.json A2S_DIR [OUT.json]

Category share of a contract's node time = sum_i w_i x_ic / sum_i w_i (w_i = s_i / pi_i,
x_ic = category c's share of replay i's task wall).
"""
import json
import sys
from collections import defaultdict
from pathlib import Path

CATEGORIES = [
    ("局部:义务求解", lambda b: b == "check@local.prove"),
    ("局部:符号执行与summary", lambda b: b in ("local.x86_segment", "local.evm_segment", "summary.apply_div",
                                          "summary.apply_lemma")),
    ("局部:建项/配对/摘要", lambda b: b in ("local.prove", "local.pair_phase", "local.correspondence", "local.digest",
                                        "local.manifest", "local.observables", "local.axioms", "local.check_paths",
                                        "rel.havoc")),
    ("共享引理", lambda b: b.startswith("lemma.")),
    ("H2", lambda b: b.startswith(("h2.", "check@h2", "rel.goals")) or b == "check@other"),
    ("指令链", lambda b: b.startswith(("chain.", "check@chain"))),
    ("其他(任务框架)", lambda b: True),
]


def category(bucket):
    return next(name for name, test in CATEGORIES if test(bucket))


def main():
    sample = json.loads(Path(sys.argv[1]).read_text())
    root = Path(sys.argv[2])
    per = defaultdict(lambda: defaultdict(float))
    weight = defaultdict(float)
    counters = defaultdict(lambda: defaultdict(float))
    rows = []
    for i, job in enumerate(sample):
        name = f"{job['contract']}-{i:02d}-{job['pick'].replace(':', '_')}"
        path = root / name / "analysis.json"
        if not path.exists():
            continue
        a = json.loads(path.read_text())
        wall = a["task_wall"] or 1e-9
        shares = defaultdict(float)
        for b, v in a["buckets"].items():
            shares[category(b)] += v["s"] / wall
        c, w = job["contract"], job["w"]
        weight[c] += w
        for k, x in shares.items():
            per[c][k] += w * x
        for k, v in a["counters"].items():
            counters[c][k] += w * v["s"] / wall
        rows.append(dict(contract=c, pick=job["pick"], production_s=round(job["s"]), replay_s=round(wall),
                         kind=job["kind"], w=round(w), top=sorted(((k, round(100 * x)) for k, x in shares.items()),
                                                                   key=lambda t: -t[1])[:3]))
    out = {c: dict(categories={k: round(v / weight[c], 3) for k, v in sorted(per[c].items(), key=lambda t: -t[1])},
                   counters={k: round(v / weight[c], 3) for k, v in counters[c].items()})
           for c in per}
    if len(sys.argv) > 3:
        Path(sys.argv[3]).write_text(json.dumps(dict(weighted=out, rows=rows), ensure_ascii=False, indent=1))
    for c, v in out.items():
        print(c, {k: f"{100 * x:.0f}%" for k, x in v["categories"].items()})
        print("   z3.check %.0f%%  forward_selects %.0f%%  query_key %.0f%%  normalize %.0f%%" % tuple(
            100 * v["counters"].get(k, 0) for k in ("z3.check", "expr.forward_selects", "cache.query_key",
                                                    "expr.normalize")))
    for r in rows:
        print("  ", r)


if __name__ == "__main__":
    main()
