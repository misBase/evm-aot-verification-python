"""Slot queue for replay jobs: queue.py JOBS.json CONF.json

CONF: {"out": dir, "snap": cwd, "python": exe, "fixtures": dir, "traces": {contract: file},
       "ordered": dir, "cpus": [6,7,...], "min_avail_mb": 5000, "rss_mb": 6000, "export_min_s": 120}
Discovery caches are built first (one job per contract, in parallel), then the
replays run longest-expected first, one per CPU slot, each under run.py's guard.
Writes OUT/QUEUE_DONE at the end.
"""
import json
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent


def avail_mb():
    try:
        for line in Path("/proc/meminfo").read_text().splitlines():
            if line.startswith("MemAvailable:"):
                return int(line.split()[1]) / 1024
    except OSError:
        pass
    return 1e9  # not Linux: no admission by memory


def command(c, job, name):
    wall = int(max(1800, 1.5 * job.get("s", 1200) + 1800))
    run = [c["python"], str(HERE / "run.py"), f"{c['out']}/{name}", "--observe", "--cwd", c["snap"],
           "--wall", str(wall), "--rss-mb", str(c["rss_mb"]), "--env", f"V3_EXPORT_MIN_S={c['export_min_s']}",
           "--env", "V3_EXPORT_CAP=10"]
    for kv in c.get("env", []):
        run += ["--env", kv]
    if job.get("cpu") is not None:
        run += ["--cpus", str(job["cpu"])]
    if job.get("argv"):  # a generic job (e.g. oracle.py): same guard, given command
        return run + ["--", c["python"], "-B"] + [a.replace("{OUT}", f"{c['out']}/{name}") for a in job["argv"]]
    rep = [c["python"], "-B", str(HERE / "replay.py"), f"{c['fixtures']}/{job['contract']}",
           f"{c['out']}/{name}/out.json", "--node-seconds", "28800",
           "--ordered", f"{c['ordered']}/{job['contract']}.pkl", "--trace", c["traces"][job["contract"]]]
    for p in job.get("picks", [job.get("spec")] if job.get("spec") else []):
        rep += ["--pick", p]
    if job.get("chain"):
        rep.append("--chain")
    return run + ["--"] + rep


def main():
    jobs = json.loads(Path(sys.argv[1]).read_text())
    c = json.loads(Path(sys.argv[2]).read_text())
    Path(c["out"]).mkdir(parents=True, exist_ok=True)
    Path(c["ordered"]).mkdir(parents=True, exist_ok=True)
    log = open(Path(c["out"]) / "queue.log", "a")
    say = lambda *a: (log.write(time.strftime("%H:%M:%S ") + " ".join(map(str, a)) + "\n"), log.flush())
    # 1) discovery caches
    need = sorted({j["contract"] for j in jobs if not Path(f"{c['ordered']}/{j['contract']}.pkl").exists()})
    disc = [subprocess.Popen(command(c, dict(contract=n, s=0, cpu=c["cpus"][i % len(c["cpus"])]), f"discovery-{n}"),
                             stdout=subprocess.DEVNULL, stderr=subprocess.STDOUT) for i, n in enumerate(need)]
    for p in disc:
        p.wait()
    say("discovery done", need)
    # 2) replays, longest first
    todo = sorted(enumerate(jobs), key=lambda ij: -ij[1].get("s", 0))
    running = {}  # cpu -> (Popen, name)
    while todo or running:
        for cpu, (p, name) in list(running.items()):
            if p.poll() is not None:
                say("end", name, p.returncode)
                del running[cpu]
        free = [x for x in c["cpus"] if x not in running]
        if todo and free and avail_mb() >= c["min_avail_mb"]:
            i, job = todo.pop(0)
            name = job.get("name") or f"{job['contract']}-{i:02d}-{job.get('pick', 'x').replace(':', '_')}"
            if not (Path(c["out"]) / name / "receipt.json").exists():
                running[free[0]] = (subprocess.Popen(command(c, dict(job, cpu=free[0]), name),
                                                     stdout=subprocess.DEVNULL, stderr=subprocess.STDOUT), name)
                say("start", name, "cpu", free[0], "avail_mb", round(avail_mb()))
                time.sleep(20)  # let it load before the next admission check
            continue
        time.sleep(15)
    (Path(c["out"]) / "QUEUE_DONE").write_text(time.strftime("%Y-%m-%d %H:%M:%S"))
    say("all done")


if __name__ == "__main__":
    main()
