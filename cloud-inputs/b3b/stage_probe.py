"""capture_probe.py plus per-phase timing of BlockEquivalenceProver.prove.

usage (cwd = snapshot, PYTHONPATH=.):  stage_probe.py <capture_probe args...>
env: STAGE_DIR   trace.log, evm_paths.json, x86_paths.json go here
     STAGE_STOP=<phase>  stop when that phase (check_paths/_correspondence/_pair_phase) is entered
     SCRIPTS     directory of capture_probe.py (default ~/evm-verif/scripts)
Pure observation: wraps phases, never changes arguments or results.
"""
import json
import os
import sys
from pathlib import Path
from time import monotonic, process_time

sys.path.insert(0, os.environ.get("SCRIPTS", os.path.expanduser("~/evm-verif/scripts")))
sys.path.insert(0, str(Path(__file__).parent))
import capture_probe  # noqa: E402  (installs the SMT2 capture on _check)
import verification.block_equivalence as be  # noqa: E402
from x86_64.cfg_executor import X86SymbolicExecutor  # noqa: E402
from canon_hash import canon_hash  # noqa: E402

OUT = Path(os.environ["STAGE_DIR"])
OUT.mkdir(parents=True, exist_ok=True)
LOG = open(OUT / "trace.log", "a")
T0 = monotonic()
P = be.BlockEquivalenceProver
REACH = {"executors": 0, "calls": 0, "wall": 0.0, "pruned": 0}


class Stop(BaseException):
    pass


def log(*parts):
    LOG.write(f"{monotonic() - T0:8.1f} " + " ".join(str(p) for p in parts) + "\n")
    LOG.flush()


def dump(name, paths):
    (OUT / name).write_text(json.dumps([[p.kind, str(p.location), canon_hash(p.condition)] for p in paths]))


_execute = X86SymbolicExecutor.execute


def execute(self, *a, **k):
    try:
        return _execute(self, *a, **k)
    finally:
        REACH["executors"] += 1
        REACH["calls"] += self.reachability_call_count
        REACH["wall"] += self.reachability_total_wall
        REACH["pruned"] += self.reachability_pruned_count


X86SymbolicExecutor.execute = execute


def segment(fn, label):
    def run(*a, **k):
        t, cpu = monotonic(), process_time()
        before = dict(REACH)
        result = fn(*a, **k)
        reach = {key: round(REACH[key] - before[key], 1) for key in REACH}
        log("PHASE", label, f"{monotonic() - t:.1f}s", f"cpu {process_time() - cpu:.1f}s", "paths", len(result[0]),
            "defects", result[1], "reach(all executors incl. summary replays)", reach)
        dump(f"{label}_paths.json", result[0])
        return result
    return run


be.run_evm_segment = segment(be.run_evm_segment, "evm")
be.run_x86_segment = segment(be.run_x86_segment, "x86")


def phase(attr, show):
    fn = getattr(P, attr)

    def timed(self, *a, **k):
        if os.environ.get("STAGE_STOP") == attr:
            log("STOP at", attr)
            raise Stop()
        t, cpu = monotonic(), process_time()
        log("BEGIN", attr)
        result = "exception"
        try:
            result = fn(self, *a, **k)
            return result
        finally:
            log("PHASE", attr, f"{monotonic() - t:.1f}s", f"cpu {process_time() - cpu:.1f}s", show(a, result))
    setattr(P, attr, timed)


def counts(correspondence):
    if not isinstance(correspondence, tuple):
        return correspondence
    return {"rows": len(correspondence), "all": sum(c == "all" for c in correspondence),
            "empty": sum(c is None for c in correspondence),
            "mapped": sum(type(c) is int for c in correspondence),
            "all_rows": [j for j, c in enumerate(correspondence) if c == "all"]}


def coverage_records(a, _):
    return {r.name: (r.answer, round(r.elapsed_seconds, 1)) for r in a[-1] if r.name.endswith("_coverage")}


phase("check_paths", coverage_records)
phase("_correspondence", lambda a, r: counts(r))
phase("_pair_phase", lambda a, r: counts(r))

if __name__ == "__main__":
    log("START", sys.argv[1:])
    try:
        code = capture_probe.main()
    except Stop:
        log("STOPPED")
        code = 0
    log("END", f"{monotonic() - T0:.1f}s")
    sys.exit(code)
