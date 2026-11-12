"""Fixed E22 timing+diagnostic plan; default plan-only, fresh sequential --run."""
import argparse
from datetime import datetime, timezone
from hashlib import sha256
import json
import os
from pathlib import Path
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
SNAP = HERE / "e25_snapshot_d213_baea"


def guard_wall_seconds(first):
    if "exit_observed_wall_seconds" in first and "cleanup_wall_seconds" in first:
        return first["exit_observed_wall_seconds"] + first["cleanup_wall_seconds"]
    return first["wall_seconds"]


def skip_repeat(point, first):
    return point["phase"] == "timing" and point["rep"] > 1 and guard_wall_seconds(first) > 300


def load_snapshot():
    ps = subprocess.run(["ps", "-A", "-o", "pid=,ppid=,pgid=,pcpu=,rss=,command="], capture_output=True, text=True, check=True)
    rows = [s for s in ps.stdout.splitlines() if "validator" in s or "measurement-work" in s]
    busy = [s for s in rows if any(token.endswith(("/single_cfg_merge_formal.py", "/e21_worker.py")) for token in s.split())]
    return dict(observed_utc=datetime.now(timezone.utc).isoformat(), load=list(os.getloadavg()), project_rows=rows,
        known_other_math_rows=busy, pcpu_scope="lifetime average, not interval usage")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run", action="store_true")
    parser.add_argument("--wait-local-idle", action="store_true")
    parser.add_argument("--out", type=Path, default=ROOT / "tests/paper/results/2026-11-05-v2/micro/E2.2/formal-v1")
    parser.add_argument("--phase", choices=("timing", "diagnostic", "all"), default="all")
    args = parser.parse_args()
    args.out = args.out.resolve()
    prepared = json.loads((HERE / "e22_formal_PREPARED.json").read_bytes())
    assert sys.executable == str(ROOT / ".venv/bin/python")
    assert all(sha256(Path(p).read_bytes()).hexdigest() == h for p, h in prepared["pins"].items())
    points = [p for p in prepared["points"] if args.phase == "all" or p["phase"] == args.phase]
    if not args.run:
        print(json.dumps(dict(status="PLAN_ONLY", cells=len(points), out=str(args.out), protocol=prepared["protocol"]), indent=2))
        return
    args.out.mkdir(parents=True, exist_ok=False)
    summary = dict(status="STARTING", protocol=prepared["protocol"], planned_cells=len(points), maximum_timing_cells=48, diagnostic_cells=16, rows=[])
    def save():
        (args.out / "SUMMARY.json").write_text(json.dumps(summary, indent=2) + "\n")
    save()
    try:
        for point in points:
            if point["phase"] == "timing" and point["rep"] > 1:
                first_path = args.out / (point["r1_name"] + ".json")
                first = json.loads(first_path.read_bytes())
                if skip_repeat(point, first):
                    summary["rows"].append(dict(name=point["name"], executed=False, result="SKIPPED_PROTOCOL",
                        reason="R1_GUARD_WALL_GT300", r1_wall_seconds=first["wall_seconds"],
                        r1_wall_exact_seconds=guard_wall_seconds(first),
                        r1_wall_basis="exit_observed_wall_seconds+cleanup_wall_seconds" if "exit_observed_wall_seconds" in first and "cleanup_wall_seconds" in first else "legacy wall_seconds fallback",
                        r1_path=str(first_path), r1_sha256=sha256(first_path.read_bytes()).hexdigest()))
                    save()
                    continue
            assert all(sha256(Path(p).read_bytes()).hexdigest() == h for p, h in prepared["pins"].items())
            load = load_snapshot()
            while load["known_other_math_rows"]:
                summary.update(status="WAITING_LOCAL_MATH", load=load)
                save()
                assert args.wait_local_idle, "other mathematical job active; --wait-local-idle keeps this fixed plan queued"
                time.sleep(5)
                load = load_snapshot()
            path = args.out / (point["name"] + ".json")
            env = {k: v for k, v in os.environ.items() if not k.startswith(("PAPER_", "BLOCK_", "E25_"))}
            env.update(PYTHONPATH=str(SNAP), PYTHONDONTWRITEBYTECODE="1", PYTHONHASHSEED="0", PYTHONNOUSERSITE="1")
            command = [sys.executable, str(ROOT / "tests/paper/harness/run_one.py"), str(path), "600", "6000", "--",
                       sys.executable, str(HERE / "e22_formal_worker.py"), point["name"]]
            (args.out / (point["name"] + ".launch.json")).write_text(json.dumps(dict(command=command, load=load), indent=2) + "\n")
            summary.update(status="RUNNING", current=point["name"])
            save()
            completed = subprocess.run(command, cwd=SNAP, env=env, capture_output=True, text=True)
            row = json.loads(path.read_bytes()) if path.exists() else {}
            summary["rows"].append(dict(name=point["name"], executed=True, result=row.get("result"), pgid=row.get("pgid"),
                supervisor_returncode=completed.returncode, stdout=completed.stdout, stderr=completed.stderr))
            save()
            assert completed.returncode == 0 and row.get("process_group_gone") is True and not row.get("monitor_error")
            assert row.get("result") in ("VERIFIED", "TO", "OOM", "BOUND", "UNK", "N/A"), "unexpected ERR/CEX stops fixed matrix"
            assert all(sha256(Path(p).read_bytes()).hexdigest() == h for p, h in prepared["pins"].items())
            print(point["name"], row["result"], row["pgid"], flush=True)
        summary.update(status="COMPLETED_FIXED_PROTOCOL", executed_cells=sum(r.get("executed", False) for r in summary["rows"]),
            skipped_cells=sum(not r.get("executed", False) for r in summary["rows"]), completed_utc=datetime.now(timezone.utc).isoformat())
        save()
    except BaseException as error:
        summary.update(status="STOPPED", error_type=type(error).__name__, error=str(error))
        save()
        raise



if __name__ == "__main__":
    main()
