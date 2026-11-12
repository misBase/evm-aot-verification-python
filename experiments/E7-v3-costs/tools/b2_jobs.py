"""B2 jobs from exported slow obligations: b2_jobs.py RUNS_ROOT FIXTURES OUT_JOBS.json [MAX_OBLIGATIONS]

Each exported check (events with metadata.exported) gets one job per arm:
"all" (the production cascade) and every single route.
"""
import json
import sys
from pathlib import Path

ROUTES = ("conditional_ites", "divrem", "lia", "stores", "quick", "shift", "blast", "alias", "potential", "bvabs",
          "exact", "mul", "guards", "unify")
HERE = Path(__file__).resolve().parent


def exported(root):
    for run in sorted(Path(root).resolve().iterdir()):  # absolute: oracle runs with the snapshot as cwd
        enter = {}
        for f in (run / "events").glob("pid-*.jsonl") if (run / "events").is_dir() else ():
            for line in f.open():
                try:
                    d = json.loads(line)
                except json.JSONDecodeError:
                    continue
                if d["event"] == "enter":
                    enter[d["id"]] = d
                elif d.get("label") == "check" and (d.get("metadata") or {}).get("exported"):
                    e = enter.get(d["id"], {}).get("metadata", {})
                    yield dict(run=run.name, contract=run.name.split("-")[0], smt2=str(run / "obligations" /
                               d["metadata"]["exported"]), name=e.get("name"), phase=e.get("phase"),
                               production_wall=d["metadata"].get("wall_before_export"),
                               production_answer=d["metadata"].get("answer"), production_routes=d["metadata"].get("routes"))


def main():
    root, fixtures, out = sys.argv[1:4]
    cap = int(sys.argv[4]) if len(sys.argv) > 4 else 12
    found = sorted(exported(root), key=lambda o: -(o["production_wall"] or 0))[:cap]
    jobs = []
    for n, o in enumerate(found):
        for arm in ("all",) + ROUTES:
            jobs.append(dict(name=f"b2-{n:02d}-{arm}", contract=o["contract"], s=0, obligation=o, arm=arm,
                             argv=[str(HERE / "oracle.py"), f"{fixtures}/{o['contract']}", o["smt2"], o["name"], arm,
                                   "600", "{OUT}/out.json"]))
    Path(out).write_text(json.dumps(jobs, indent=1))
    for o in found:
        print(o["run"], o["name"], o["phase"], o["production_wall"], o["production_answer"])


if __name__ == "__main__":
    main()
