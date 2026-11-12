"""Run one command under a wall/tree-RSS guard and write a receipt.

  run.py OUT [--wall S] [--rss-mb MB] [--observe] [--cpus 0-3] [--env K=V ...] -- cmd ...
  run.py OUT --contract NAME --fixtures DIR [--trace FILE] [--workers 4] [--program-wall 3600] ... (CLI shortcut)

The command runs in its own session (process group); on wall or RSS overrun the
whole group gets SIGTERM, then SIGKILL. --observe sets V3_COST_DIR=OUT and puts
this directory first on PYTHONPATH (sitecustomize installs hooks.py).
"""
import argparse
import json
import os
import platform
import signal
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent


def group_sample(pgid):
    """(tree RSS MiB, process count, live CPU seconds) of a process group."""
    if sys.platform.startswith("linux"):
        rss, n, cpu, tick = 0, 0, 0.0, os.sysconf("SC_CLK_TCK")
        for pid in os.listdir("/proc"):
            if not pid.isdigit():
                continue
            try:
                stat = Path(f"/proc/{pid}/stat").read_text()
                fields = stat[stat.rindex(")") + 2:].split()
                if int(fields[2]) != pgid:
                    continue
                n += 1
                cpu += (int(fields[11]) + int(fields[12])) / tick
                for line in Path(f"/proc/{pid}/status").read_text().splitlines():
                    if line.startswith("VmRSS:"):
                        rss += int(line.split()[1])
            except (OSError, ValueError, IndexError):
                continue
        return rss / 1024, n, cpu
    pids = subprocess.run(["pgrep", "-g", str(pgid)], capture_output=True, text=True).stdout.split()
    if not pids:
        return 0.0, 0, 0.0
    out = subprocess.run(["ps", "-o", "rss=,time=", "-p", ",".join(pids)], capture_output=True, text=True).stdout
    rss, n, cpu = 0, 0, 0.0
    for line in out.split("\n"):
        parts = line.split()
        if len(parts) == 2:
            n += 1
            rss += int(parts[0])
            t = parts[1].replace("-", ":").split(":")
            cpu += sum(float(x) * m for x, m in zip(reversed(t), (1, 60, 3600, 86400)))
    return rss / 1024, n, cpu


def whole_cmd(a):
    cmd = [sys.executable, "-B", "-m", "tools.verify_block_lockstep", str(Path(a.fixtures) / a.contract),
           "--gas-check", "full", "--num-inputs", "0", "--timeout-ms", "30000",
           "--first-pass-node-seconds", "300", "--node-seconds", str(a.node_seconds),
           "--max-depth", "400", "--max-instances", "8192", "--max-parameter-values", "32",
           "--wall-seconds", str(a.program_wall), "--hard-wall-seconds", str(a.program_wall + 300),
           "--summaries", "--discover-first", "--constant-insensitive",
           "--node-workers", str(a.workers), "--pair-workers-per-node", "1", "--node-memory-mb", str(a.node_mb),
           "--status-dir", str(Path(a.out).resolve() / "status"), "--results-dir", str(Path(a.out).resolve() / "results"),
           "--output", str(Path(a.out).resolve() / f"{a.contract}.json")]
    if a.trace:
        cmd += ["--instruction-hints", a.trace]
    return cmd


def main():
    p = argparse.ArgumentParser()
    p.add_argument("out")
    p.add_argument("--wall", type=float, default=None)
    p.add_argument("--rss-mb", type=float, default=None)
    p.add_argument("--observe", action="store_true")
    p.add_argument("--cpus")
    p.add_argument("--cwd", default=".")
    p.add_argument("--env", action="append", default=[])
    p.add_argument("--contract")
    p.add_argument("--fixtures")
    p.add_argument("--trace")
    p.add_argument("--workers", type=int, default=4)
    p.add_argument("--node-mb", type=int, default=3000)
    p.add_argument("--node-seconds", type=int, default=28800)
    p.add_argument("--program-wall", type=int, default=3600)
    argv = sys.argv[1:]
    cut = argv.index("--") if "--" in argv else len(argv)
    a = p.parse_args(argv[:cut])
    a.cmd = argv[cut + 1:]
    out = Path(a.out).resolve()
    out.mkdir(parents=True, exist_ok=False)  # never reuse a run directory
    cmd = a.cmd
    if a.contract:
        cmd = whole_cmd(a)
        if a.wall is None:
            a.wall = a.program_wall + 600
    if a.cpus and sys.platform.startswith("linux"):
        cmd = ["taskset", "-c", a.cpus] + cmd
    env = dict(os.environ, PYTHONHASHSEED="0", BLOCK_SUMMARY_LEMMAS="1",
               BLOCK_PROOF_CACHE=str(out / "cache.sqlite"), PYTHONDONTWRITEBYTECODE="1")
    cwd = Path(a.cwd).resolve()
    env["PYTHONPATH"] = os.pathsep.join(([str(HERE)] if a.observe else []) + [str(cwd)])
    if a.observe:
        env["V3_COST_DIR"] = str(out)
    for kv in a.env:
        k, v = kv.split("=", 1)
        env[k] = v
    receipt = dict(cmd=cmd, cwd=str(cwd), host=platform.node(), platform=platform.platform(),
                   observe=a.observe, wall_limit=a.wall, rss_limit_mb=a.rss_mb, cpus=a.cpus,
                   env={k: env[k] for k in env if k.startswith(("V3_", "BLOCK_", "PYTHON"))},
                   revision=subprocess.run(["git", "rev-parse", "HEAD"], cwd=cwd, capture_output=True,
                                           text=True).stdout.strip())
    started, peak, reason = time.time(), 0.0, None
    with open(out / "log.txt", "w") as log, open(out / "resources.csv", "w") as res:
        res.write("t,rss_mb,procs,cpu_live_s\n")
        proc = subprocess.Popen(cmd, cwd=cwd, env=env, stdout=log, stderr=subprocess.STDOUT,
                                stdin=subprocess.DEVNULL, start_new_session=True)
        (out / "pid").write_text(str(proc.pid))
        last_cpu = 0.0
        while proc.poll() is None:
            rss, n, cpu = group_sample(proc.pid)
            last_cpu = max(last_cpu, cpu)
            peak = max(peak, rss)
            res.write(f"{time.time() - started:.1f},{rss:.1f},{n},{cpu:.1f}\n")
            res.flush()
            if a.wall and time.time() - started > a.wall:
                reason = "wall"
            elif a.rss_mb and rss > a.rss_mb:
                reason = "rss"
            if reason:
                os.killpg(proc.pid, signal.SIGTERM)
                for _ in range(20):
                    if proc.poll() is not None:
                        break
                    time.sleep(0.5)
                break
            time.sleep(5)
        try:
            os.killpg(proc.pid, signal.SIGKILL)  # stragglers of the group
        except ProcessLookupError:
            pass
        code = proc.wait()
    rusage = resource_usage()  # this guard's only child (plus what it reaped): the run's CPU
    receipt.update(started=started, wall_s=round(time.time() - started, 1), exit=code, killed=reason,
                   peak_tree_rss_mb=round(peak, 1), live_cpu_peak_s=round(last_cpu, 1),
                   children_cpu_s=round(rusage.ru_utime + rusage.ru_stime, 1))
    (out / "receipt.json").write_text(json.dumps(receipt, indent=1))
    print(json.dumps({k: receipt[k] for k in ("wall_s", "exit", "killed", "peak_tree_rss_mb", "children_cpu_s")}))


def resource_usage():
    import resource
    return resource.getrusage(resource.RUSAGE_CHILDREN)


if __name__ == "__main__":
    main()
