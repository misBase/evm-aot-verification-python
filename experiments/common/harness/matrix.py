"""Run the experiment matrix on one machine, highest priority first.

  python matrix.py --snap SNAPSHOT --fixtures FROZEN_FIXTURES --out RESULTS --cpus 0-7 [--max-priority N]

Each job is `run_one.py` around `worker.py` (cwd = the frozen snapshot), pinned with
taskset to its own CPUs. Finished jobs (result JSON present) are skipped, so the
matrix can be restarted. Writes OUT/matrix.process.json for the remote waiter.
"""
import argparse
import json
import os
import platform
import subprocess
import sys
import time
from dataclasses import dataclass, field
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from slices import SLICES  # noqa: E402

ALL_SINGLE = ("ADD SUB MUL DIV MOD SDIV SMOD ADDMOD MULMOD EXP SIGNEXTEND LT GT SLT SGT EQ ISZERO AND OR XOR "
              "NOT BYTE SHL SHR SAR SHA3 ADDRESS BALANCE ORIGIN CALLER CALLVALUE CALLDATALOAD CALLDATASIZE "
              "CALLDATACOPY CODESIZE CODECOPY GASPRICE EXTCODESIZE EXTCODECOPY RETURNDATASIZE RETURNDATACOPY "
              "EXTCODEHASH BLOCKHASH COINBASE TIMESTAMP NUMBER DIFFICULTY GASLIMIT CHAINID SELFBALANCE BASEFEE "
              "BLOBHASH BLOBBASEFEE POP MLOAD MSTORE MSTORE8 SLOAD SSTORE MSIZE GAS TLOAD TSTORE MCOPY "
              "MCOPY_OVERLAP PUSH0 PUSH1 PUSH32 DUP1 DUP2 DUP16 SWAP1 SWAP2 SWAP16 LOG0 LOG1 LOG2 LOG3 LOG4 "
              "CREATE CREATE2 CALL CALLCODE DELEGATECALL STATICCALL SELFDESTRUCT STOP RETURN REVERT INVALID "
              "JUMP JUMPI JUMPDEST").split()
A_ARITH = "MUL DIV MOD SDIV SMOD ADDMOD MULMOD EXP SIGNEXTEND BYTE SHL SHR SAR".split()
A_MEM = "MLOAD MSTORE MSTORE8 CALLDATALOAD CALLDATACOPY CODECOPY RETURNDATACOPY MCOPY MCOPY_OVERLAP SHA3 LOG0 LOG4".split()
A_PROGRAMS = ("two_block three_block jumpi_2block jumpi_2block_ok jumpi_2block_err mstore_return sstore_load "
              "perf_erc20_lite muti_block muti_block_08 static_bounded dynamic_bounded unbounded "
              "lockstep_counter_loop lockstep_calldata_loop lockstep_fmp_loop lockstep_return_loop "
              "lockstep_storage_loop").split()
BASELINES = ("V1", "V2")  # v3 round: the main matrix excludes V0
ABLATIONS = ("V2-O1", "V2-O2")  # O1 = B1+B2, O2 = B3+B4
B4_ABLATIONS = ()
PARALLEL = {"V2", "V2-O2"}  # paths mode's four path-pair threads
WHOLE_CONTRACTS = ("ENSRegistry", "Permit2", "Safe", "CErc20", "PoolManager", "Pool")
# Function slices admitted by the 2026-11-05 sample-admission gate (non-empty domain, complete slice coverage,
# reduced exploration); the v3 round reuses this admission instead of re-running the gate.
ADMITTED_FUNCTIONS = ("ENSRegistry.owner", "ENSRegistry.resolver", "ENSRegistry.setOwner",
                      "ENSRegistry.setSubnodeOwner")
V0_DEPTH = 1_000_000_000  # practical unbounded baseline, still subject to the outer limit
SMALL_DEPTH = 400
# Real contracts: loop-free paths run deeper than 400 x86 blocks, so slices use the
# repository's whole-contract depth (tests/integration/test_ext_contract_verification.py).
CONTRACT_DEPTH = ["--max-depth", "100000"]


@dataclass
class Job:
    name: str
    priority: int
    argv: list
    timeout: float
    memory_mb: float
    cpus: int = 1
    requires: tuple = ()  # (result name, accepted classes): run only if that result is in them
    extra: dict = field(default_factory=dict)


def jobs(fixtures, out_dir="."):
    """One V2-design repetition; the caller supplies a fresh output directory."""
    out = []
    for case in ALL_SINGLE:
        for config in BASELINES:
            depth = V0_DEPTH if config == "V0" else SMALL_DEPTH
            out.append(Job(f"single/{case}/{config}", 1,
                           ["single", case, config, "--max-depth", str(depth), "--gas", "off"], 600, 2000))
    for case in A_ARITH + A_MEM:
        for config in ABLATIONS:
            out.append(Job(f"single/{case}/{config}", 2,
                           ["single", case, config, "--max-depth", str(SMALL_DEPTH), "--gas", "off"], 600, 2000))
    for case in A_ARITH:
        for config in B4_ABLATIONS:
            out.append(Job(f"single/{case}/{config}", 2,
                           ["single", case, config, "--max-depth", str(SMALL_DEPTH), "--gas", "off"], 600, 2000))
    for stem in A_PROGRAMS:
        path = f"tests/data/{stem}"
        for config in BASELINES + ABLATIONS:
            depth = V0_DEPTH if config == "V0" else SMALL_DEPTH
            out.append(Job(f"prog/{stem}/{config}", 1 if config in BASELINES else 2,
                           ["program", path, config, "--max-depth", str(depth), "--gas", "off"], 600, 3000,
                           cpus=4 if config in PARALLEL else 1))
        out.append(Job(f"prog/{stem}/V3", 1,
                       ["lockstep", path, "V3", "--wall", "600", "--max-depth", str(SMALL_DEPTH),
                        "--gas", "full"], 600, 4000, cpus=4))
    for contract, function, selector, size in SLICES:
        stem = str(Path(fixtures) / contract)
        tag = f"fn/{contract}.{function.split('(')[0]}"
        pin = ["--selector", f"{selector:08x}", "--calldata-size", str(size), *CONTRACT_DEPTH, "--gas", "off"]
        whole_report = str(Path(out_dir) / "whole-metrics" / f"{contract}.json")
        out.append(Job(f"{tag}/reach", 2,
                       ["reach", stem, f"{selector:08x}", str(size), "--include-x86", "--whole-report",
                        whole_report, *CONTRACT_DEPTH, "--gas", "off"], 1800, 2000))
        for config in ("V2",) + ABLATIONS:
            out.append(Job(f"{tag}/{config}", 2 if config == "V2" else 3,
                           ["program", stem, config, *pin], 1800, 4000,
                           cpus=4 if config in PARALLEL else 1,
                           requires=(f"{tag}/reach", ("SLICE-VALID",))))
            if f"{contract}.{function.split('(')[0]}" in ADMITTED_FUNCTIONS:
                # v3 round: the four functions admitted by the 2026-11-05 gate, without re-running the gate
                out.append(Job(f"fnx/{contract}.{function.split('(')[0]}/{config}", 2 if config == "V2" else 3,
                               ["program", stem, config, *pin], 1800, 4000,
                               cpus=4 if config in PARALLEL else 1))
    for contract in WHOLE_CONTRACTS:
        stem = str(Path(fixtures) / contract)
        for config in BASELINES:
            depth = V0_DEPTH if config == "V0" else 100_000
            out.append(Job(f"whole/{contract}/{config}", 2,
                           ["program", stem, config, "--whole", "--max-depth", str(depth), "--gas", "off"],
                           3600, 6000, cpus=4 if config in PARALLEL else 1))
        out.append(Job(f"whole/{contract}/V3", 2,
                       ["lockstep", stem, "V3", "--wall", "3600", "--max-depth",
                        "800" if contract == "Pool" else "400", "--gas", "full"], 3600, 6000, cpus=4))
    return out


def inflight_cpus(out):
    """CPU affinity of run_one.py processes already writing into the results directory (Linux /proc)."""
    held = {}
    if not os.path.isdir("/proc/self"):
        return held
    for entry in os.listdir("/proc"):
        if not entry.isdigit() or int(entry) == os.getpid():
            continue
        try:
            argv = Path(f"/proc/{entry}/cmdline").read_bytes().split(b"\0")
            if any(a.endswith(b"run_one.py") for a in argv) and any(a.startswith(str(out).encode()) for a in argv):
                held[int(entry)] = sorted(os.sched_getaffinity(int(entry)))
        except OSError:
            continue
    return held


def load_extra(fixtures, out_dir):
    """Jobs from extra_jobs.py, re-read while the matrix runs (additions need no restart)."""
    path = HERE / "extra_jobs.py"
    if not path.exists():
        return []
    namespace = dict(Job=Job, Path=Path, SLICES=SLICES, CONTRACT_DEPTH=CONTRACT_DEPTH, result_path=result_path)
    try:
        exec(compile(path.read_text(), str(path), "exec"), namespace)
        return namespace["extra"](fixtures, out_dir)
    except Exception as error:  # a bad edit must not kill the running matrix
        print(time.strftime("%H:%M:%S"), "extra_jobs.py ignored:", error, flush=True)
        return []


def parse_cpus(text):
    cpus = []
    for part in text.split(","):
        lo, _, hi = part.partition("-")
        cpus.extend(range(int(lo), int(hi or lo) + 1))
    return cpus


def result_path(out, job):
    return Path(out) / (job.name.replace("/", "__") + ".json")


def dependency_failure(job, record):
    if not isinstance(record, dict) or record.get("result") not in job.requires[1]:
        return "dependency has no accepted result"
    if job.name.startswith("fn/"):
        from slices import receipt_failure
        argv = job.argv
        selector = int(argv[argv.index("--selector") + 1], 16)
        size = argv[argv.index("--calldata-size") + 1]
        return receipt_failure(record, argv[1], selector, None if size == "None" else int(size))
    return None


def record_unvalidated(out, job, reason):
    result_path(out, job).write_text(json.dumps(dict(
        kind=job.argv[0], target=job.argv[1], config=job.argv[2],
        result="N/A", verified=False, dependency=job.requires[0],
        message=f"Missing/unvalidated slice dependency: {reason}; no verification was run"), indent=1))


def check_fixture_inputs(candidates):
    from slices import fixture_receipt
    for stem in sorted({job.argv[1] for job in candidates if job.name.startswith(("whole/", "fn/"))}):
        fixture_receipt(stem)  # canonical bytes may live under any configured fixture root


def record_incomplete_previous(out, job, inherited):
    path = result_path(out, job)
    log = path.with_suffix(".log")
    if inherited or path.exists() or not log.exists():
        return False
    path.write_text(json.dumps(dict(
        kind=job.argv[0], target=job.argv[1], config=job.name.rsplit("/", 1)[1],
        result="ERR", raw_status="incomplete_previous_attempt", verified=False,
        previous_log=str(log), message="Previous log has no result; raw preserved, no automatic retry"), indent=1))
    return True


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--snap", required=True)
    p.add_argument("--fixtures", required=True, help="directory containing the canonical r4 fixture bytes")
    p.add_argument("--out", required=True)
    p.add_argument("--cpus", default="0-7")
    p.add_argument("--python", default=sys.executable)
    p.add_argument("--max-priority", type=int, default=9)
    p.add_argument("--memory-budget", type=float, default=14000, help="sum of running jobs' memory caps (MB)")
    p.add_argument("--only", default="", help="run only jobs whose name starts with this")
    p.add_argument("--names", default="", help="file of job names (one per line): run only those (repetition rounds)")
    args = p.parse_args()
    names = set(Path(args.names).read_text().split()) if args.names else None
    args.fixtures = str(Path(args.fixtures).resolve())
    out = Path(args.out).resolve()  # children run with cwd=the immutable snapshot
    out.mkdir(parents=True, exist_ok=True)
    status = out / "matrix.process.json"
    def runnable(candidates):
        return [j for j in candidates
                if j.priority <= args.max_priority and j.name.startswith(args.only)
                and (names is None or j.name in names) and not result_path(out, j).exists()]

    pending = sorted(runnable(jobs(args.fixtures, out) + load_extra(args.fixtures, out)), key=lambda j: j.priority)
    check_fixture_inputs(pending)
    status.write_text(json.dumps(dict(pid=os.getpid(), state="running", started=time.time(), argv=sys.argv)))
    known, reloaded = {j.name for j in pending}, time.monotonic()
    free = parse_cpus(args.cpus)
    inherited = inflight_cpus(out)  # pid -> CPUs still held by a previous matrix's jobs
    free = [c for c in free if not any(c in cpus for cpus in inherited.values())]
    running = {}  # Popen -> (job, cpus)
    taskset = ["taskset", "-c"] if platform.system() == "Linux" else None
    reserved = lambda: sum(job.memory_mb for job, _ in running.values())  # caps are enforced by run_one
    try:
        while pending or running or inherited:
            if time.monotonic() - reloaded > 60:
                reloaded = time.monotonic()
                fresh = [j for j in runnable(load_extra(args.fixtures, out)) if j.name not in known]
                known.update(j.name for j in fresh)
                pending = sorted(pending + fresh, key=lambda j: j.priority)
            for pid in [pid for pid in inherited if not os.path.exists(f"/proc/{pid}")]:
                free.extend(c for c in inherited.pop(pid) if c in parse_cpus(args.cpus) and c not in free)
            for process in [p for p in running if p.poll() is not None]:
                job, cpus = running.pop(process)
                free.extend(cpus)
                print(time.strftime("%H:%M:%S"), "done", job.name, flush=True)
            if inherited:
                time.sleep(2)  # old jobs' memory is unknown: wait before reserving new memory
                continue
            for job in list(pending):
                if result_path(out, job).exists():
                    pending.remove(job)  # an inherited worker completed while this matrix waited
                    continue
                if record_incomplete_previous(out, job, inherited):
                    pending.remove(job)
                    continue
                if job.cpus > len(free) or reserved() + job.memory_mb > args.memory_budget:
                    break  # strict priority order: wide jobs are not starved by narrow ones
                if job.requires:
                    name, _ = job.requires
                    dependency = Path(out) / (name.replace("/", "__") + ".json")
                    if not dependency.exists():
                        if any(j.name == name for j in pending) or any(j.name == name for j, _ in running.values()):
                            continue  # not decided yet
                        pending.remove(job)
                        record_unvalidated(out, job, "missing receipt")
                        continue
                    try:
                        failure = dependency_failure(job, json.loads(dependency.read_text()))
                    except (OSError, ValueError, TypeError, KeyError) as error:
                        failure = f"receipt rejected: {type(error).__name__}: {error}"
                    if failure:
                        pending.remove(job)
                        record_unvalidated(out, job, failure)
                        continue
                pending.remove(job)
                cpus, free = free[:job.cpus], free[job.cpus:]
                worker = str(HERE / {"reach": "reach.py", "slice_v3": "slice_v3.py"}.get(job.argv[0], "worker.py"))
                argv = (job.argv[1:4] + [str(result_path(out, job).with_suffix(".reach.json"))] + job.argv[4:] if job.argv[0] == "reach"
                        else job.argv[1:] if job.argv[0] == "slice_v3" else job.argv)
                command = [args.python, str(HERE / "run_one.py"), str(result_path(out, job)), str(job.timeout),
                           str(job.memory_mb), "--", args.python, worker, *argv]
                if taskset:
                    command = taskset + [",".join(map(str, cpus))] + command
                running[subprocess.Popen(command, cwd=args.snap, stdout=subprocess.DEVNULL)] = (job, cpus)
                print(time.strftime("%H:%M:%S"), "start", job.name, cpus, flush=True)
            time.sleep(2)
    finally:
        status.write_text(json.dumps(dict(pid=os.getpid(), state="finished", ended=time.time(), argv=sys.argv)))


if __name__ == "__main__":
    main()
