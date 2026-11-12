"""Supervise a fresh job; retain wall/CPU, sampled tree RSS and raw status.

  python run_one.py RESULT.json TIMEOUT_S MEMORY_MB [--allow-exit-only] -- CMD...

CPU is wait4(job), excluding sampler children; unreaped descendants make it a
lower bound. RSS is a sampled sum. An exit-only diagnostic never proves a theorem.
"""
import json
import os
import platform
import signal
import subprocess
import sys
import time
from pathlib import Path


def _process_table(timeout=1.0):
    """pid -> (ppid, pgrp, rss KiB). Linux uses no sampler child."""
    table = {}
    if os.path.isdir("/proc/self"):
        page_kb = os.sysconf("SC_PAGE_SIZE") // 1024
        for entry in os.listdir("/proc"):
            if entry.isdigit():
                try:
                    fields = Path(f"/proc/{entry}/stat").read_text().rsplit(")", 1)[1].split()
                    table[int(entry)] = (int(fields[1]), int(fields[2]), int(fields[21]) * page_kb)
                except (OSError, ValueError, IndexError):
                    continue
        return table
    rows = subprocess.run(["ps", "-A", "-o", "pid=,ppid=,pgid=,rss="], capture_output=True,
                          text=True, check=True, timeout=timeout).stdout
    for line in rows.splitlines():
        pid, ppid, pgid, kb = map(int, line.split())
        table[pid] = (ppid, pgid, kb)
    return table


def _members(table, root):
    # The owned group survives root exit/reparenting; add its descendants too.
    selected = {pid for pid, (_, pgid, _) in table.items() if pgid == root}
    selected.add(root)
    changed = True
    while changed:
        old = len(selected)
        selected.update(pid for pid, (ppid, _, _) in table.items() if ppid in selected)
        changed = len(selected) != old
    return selected & table.keys()


def tree_rss_mb(root):
    table = _process_table()
    return sum(table[pid][2] for pid in _members(table, root)) / 1024


def _kill_group(pgid):
    try:
        os.killpg(pgid, signal.SIGKILL)
    except ProcessLookupError:
        pass


def main():
    out, timeout_s, memory_mb = Path(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3])
    split = sys.argv.index("--")
    command = sys.argv[split + 1:]
    allow_exit_only = "--allow-exit-only" in sys.argv[4:split]
    if not command or not (0 < timeout_s < float("inf") and 0 < memory_mb < float("inf")):
        raise ValueError("positive budgets and a command are required")
    out.parent.mkdir(parents=True, exist_ok=True)
    worker_out = out.with_suffix(".worker.json")
    if out.exists() or worker_out.exists() or out.with_suffix(".log").exists():
        raise FileExistsError(f"fresh result path required: {out}")
    started = time.monotonic()
    deadline = started + timeout_s
    env = dict(os.environ, PAPER_WORKER_OUT=str(worker_out.resolve()), PYTHONHASHSEED="0",
               PAPER_DEADLINE_MONOTONIC=str(deadline), PAPER_TIMEOUT_S=str(timeout_s),
               PYTHONDONTWRITEBYTECODE="1")
    peak, stopped, monitor_error, sampler_deadline_error = 0.0, None, None, None
    usage = status = exit_observed = None
    forced_cleanup = False
    with out.with_suffix(".log").open("w") as log:
        process = subprocess.Popen(command, stdout=log, stderr=subprocess.STDOUT, env=env,
                                   start_new_session=True)
        try:
            while status is None:
                pid, found, measured = os.wait4(process.pid, os.WNOHANG)
                if pid:
                    exit_observed = time.monotonic()
                    status, usage = found, measured
                    if exit_observed >= deadline:
                        stopped = "TO"
                    break
                remaining = deadline - time.monotonic()
                if remaining <= 0:
                    stopped = "TO"
                else:
                    try:
                        table = _process_table(max(0.001, min(1.0, remaining)))
                        peak = max(peak, sum(table[pid][2] for pid in _members(table, process.pid)) / 1024)
                    except Exception as exc:
                        detail = f"{type(exc).__name__}: {exc}"
                        if isinstance(exc, subprocess.TimeoutExpired) and time.monotonic() >= deadline:
                            sampler_deadline_error, stopped = detail, "TO"
                        else:
                            monitor_error, stopped = detail, "ERR"
                    if peak > memory_mb:
                        stopped = "OOM"
                if stopped:
                    _kill_group(process.pid)
                    _, status, usage = os.wait4(process.pid, 0)
                    exit_observed = time.monotonic()
                    break
                time.sleep(min(0.1, max(0, deadline - time.monotonic())))
        finally:
            if status is None:
                _kill_group(process.pid)
                _, status, usage = os.wait4(process.pid, 0)
                exit_observed = time.monotonic()
            process.returncode = os.waitstatus_to_exitcode(status)
        try:
            remaining_members = sorted(_members(_process_table(), process.pid))
            if remaining_members:
                forced_cleanup = True
                _kill_group(process.pid)
            until = time.monotonic() + 0.5
            while remaining_members and time.monotonic() < until:
                time.sleep(0.02)
                remaining_members = sorted(_members(_process_table(), process.pid))
        except Exception as exc:
            remaining_members = None
            monitor_error = f"{type(exc).__name__}: {exc}"
    finished = time.monotonic()
    wall = finished - started
    record = dict(command=command, cwd=os.getcwd(), host=platform.node(),
                  machine=platform.processor() or platform.machine(),
                  timeout_s=timeout_s, memory_mb=memory_mb, returncode=process.returncode,
                  wall_seconds=round(wall, 3), cpu_seconds=round(usage.ru_utime + usage.ru_stime, 3),
                  exit_observed_monotonic=exit_observed,
                  exit_observed_wall_seconds=exit_observed - started,
                  cleanup_wall_seconds=finished - exit_observed,
                  wall_scope="includes cleanup; deadline is tested at exit observation before cleanup",
                  cpu_user_seconds=usage.ru_utime, cpu_sys_seconds=usage.ru_stime,
                  peak_rss_mb=round(peak, 1), peak_rss_scope="sampled sum of owned group and descendants",
                  ru_maxrss_bytes=usage.ru_maxrss if sys.platform == "darwin" else usage.ru_maxrss * 1024,
                  ended_at=time.strftime("%Y-%m-%dT%H:%M:%S"),
                  sampler="proc" if os.path.isdir("/proc/self") else "ps",
                  cpu_scope="wait4 job + descendants it reaped; excludes sampler children",
                  cpu_lower_bound=bool(stopped or forced_cleanup), pgid=process.pid,
                  cleanup_forced=forced_cleanup, process_group_gone=remaining_members == [],
                  remaining_group_members=remaining_members, monitor_error=monitor_error)
    record["sampler_deadline_error"] = sampler_deadline_error
    worker = None
    try:
        if worker_out.exists():
            worker = json.loads(worker_out.read_text())
            if not isinstance(worker, dict):
                raise ValueError("worker result is not an object")
            if "result" in worker and not isinstance(worker["result"], str):
                raise ValueError("worker result class is not a string")
            record["worker_payload"] = worker
            record.update({key: value for key, value in worker.items() if key not in record})
    except (ValueError, OSError) as exc:
        record["worker_json_error"] = f"{type(exc).__name__}: {exc}"
        stopped = stopped or "ERR"
    if stopped:
        record["result"] = stopped
        record["legacy_result"] = "TIMEOUT" if stopped == "TO" else stopped
    elif monitor_error or forced_cleanup or remaining_members:
        record["result"] = "ERR"
    elif process.returncode != 0:
        record["worker_result"] = (worker or {}).get("result")
        record["result"] = "ERR"
        record["legacy_result"] = "CRASH_AFTER_RESULT" if worker else "CRASH"
    elif worker is None or "result" not in worker:
        record["result"] = "COMPLETED" if allow_exit_only else "ERR"
        record["result_scope"] = "exit-status-only diagnostic; not a proof"
    else:
        record["result"] = {"UNKNOWN": "UNK", "TIMEOUT": "TO", "ERROR": "ERR"}.get(worker["result"], worker["result"])
        if record["result"] == "VERIFIED" and worker.get("verified") is not True:
            record["result"] = "ERR"
    if record["result"] in ("ERR", "TO", "OOM", "UNK", "N/A", "UNSUPPORTED"):
        record["verified"] = False
    temporary = out.with_suffix(out.suffix + ".tmp")
    temporary.write_text(json.dumps(record, ensure_ascii=False, indent=1))
    temporary.replace(out)
    print(record["result"], record["cpu_seconds"], record["wall_seconds"], record["peak_rss_mb"])


if __name__ == "__main__":
    main()
