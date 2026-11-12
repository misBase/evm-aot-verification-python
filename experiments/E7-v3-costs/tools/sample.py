"""A2-S: probability-proportional-to-size sample of proof instances (systematic PPS, fixed seed).

  sample.py OUT_JOBS.json N CONTRACT=final.json ...

Each instance i (final record, production seconds s_i) is included with
probability pi_i = min(1, N s_i / S); certainty units (pi=1) are taken first.
The time-weighted share of a bucket over the whole contract is then estimated
by sum_i w_i x_i / sum_i w_i with w_i = s_i / pi_i (x_i: the bucket's share of
replay i). Weights are written with each job.
"""
import json
import random
import re
import sys
from pathlib import Path

PAT = re.compile(r"pc=(\d+), stack_depth=(\d+), memory_size=([^,]+), free_memory_pointer=([^,]+), stack_constants=(.*)\)$")


def pps(units, n, seed):
    total = sum(u["s"] for u in units)
    certain, rest = [], list(units)
    while True:  # peel certainty units until every remaining pi < 1
        left = n - len(certain)
        mass = sum(u["s"] for u in rest)
        big = [u for u in rest if left > 0 and u["s"] * left >= mass]
        if not big:
            break
        certain += big
        rest = [u for u in rest if u not in big]
    for u in certain:
        u["pi"] = 1.0
    left = n - len(certain)
    picked = list(certain)
    if left > 0 and rest:
        mass = sum(u["s"] for u in rest)
        rng = random.Random(seed)
        rng.shuffle(rest)
        step = mass / left
        point, acc = rng.uniform(0, step), 0.0
        for u in rest:
            acc += u["s"]
            u["pi"] = left * u["s"] / mass
            while point < acc and len(picked) < n:
                picked.append(u)
                point += step
    for u in picked:
        u["w"] = u["s"] / u["pi"]
    return picked, total


def main():
    out, n = sys.argv[1], int(sys.argv[2])
    jobs = []
    for arg in sys.argv[3:]:
        contract, path = arg.split("=", 1)
        d = json.loads(Path(path).read_text())
        units = []
        for v in d["diagnostics"].values():
            for i in v["instances"]:
                if i["status"] == "split" or not i.get("seconds"):
                    continue
                m = PAT.search(i["spec"])
                units.append(dict(contract=contract, spec=i["spec"], s=i["seconds"], contexts=i.get("contexts", 1),
                                  kind=i.get("proof_kind", "legacy"), status=i["status"],
                                  pick=":".join(m.group(k) for k in (1, 2, 3, 4)), constants=m.group(5)))
        picked, total = pps(units, n, seed=20261112)
        for u in picked:
            u.update(total=total, chain=u["kind"] == "instruction-chain/1")
        jobs += picked
        print(contract, "units", len(units), "total_s", round(total), "picked",
              [(u["pick"], round(u["s"]), u["kind"][:5], round(u["pi"], 2)) for u in picked])
    Path(out).write_text(json.dumps(jobs, indent=1))


if __name__ == "__main__":
    main()
