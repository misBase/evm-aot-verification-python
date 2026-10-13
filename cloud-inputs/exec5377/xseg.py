"""Time the x86 segment (+ check_paths + _correspondence) of one block context.

usage: xseg.py STEM 'BlockSpecialization(...)' NODE_SECONDS OUTDIR   (cwd = snapshot)
env:
  REACH_MODE   base (re-implementation of X86Constraints.is_possible, instrumented)
               | any mode defined in reach_modes.py
  RECORD=1     dump every reachability query (unique conjunct table + per-call index lists)
  STOP=x86     stop right after run_x86_segment (default: stop at _pair_phase entry)
Writes OUTDIR/trace.log, OUTDIR/calls.jsonl, OUTDIR/paths.json.
"""
import json
import os
import sys
from pathlib import Path
from time import monotonic, process_time

sys.path.insert(0, ".")
sys.path.insert(0, str(Path(__file__).parent))
os.environ.setdefault("BLOCK_PAIR_WORKERS", "1")
from z3 import Solver  # noqa: E402
from verification import block_parallel as bp  # noqa: E402
import verification.block_equivalence as be  # noqa: E402
from verification.block_specialization import BlockSpecialization  # noqa: E402,F401
from x86_64 import cfg_state  # noqa: E402
from x86_64.cfg_executor import X86SymbolicExecutor  # noqa: E402
from verification.block_summaries import VerifiedSummaryRuntime  # noqa: E402
import reach_modes  # noqa: E402

stem, text, seconds, out = sys.argv[1], sys.argv[2], float(sys.argv[3]), Path(sys.argv[4])
out.mkdir(parents=True, exist_ok=True)
LOG = open(out / "trace.log", "a")
CALLS = open(out / "calls.jsonl", "w")
T0 = monotonic()
MODE = os.environ.get("REACH_MODE", "base")
RECORD = os.environ.get("RECORD") == "1"


def log(*parts):
    LOG.write(f"{monotonic() - T0:8.1f} " + " ".join(str(p) for p in parts) + "\n")
    LOG.flush()


class Stop(BaseException):
    pass


# ---------------- reachability instrumentation ----------------
TABLE, ORDER = {}, []   # z3 ast id -> index; keeps the ASTs alive (ids never reused)
IN_APPLY = [0]
STATS = {"calls": 0, "wall": 0.0}


def index_of(e):
    k = e.get_id()
    if k not in TABLE:
        TABLE[k] = len(ORDER)
        ORDER.append(e)
    return TABLE[k]


def instrumented(self, solver_timeout=None):
    started = monotonic()
    info = {"n": len(self._constraints) + len(self.flag_constraints), "apply": IN_APPLY[0]}
    if RECORD:
        info["c"] = [index_of(c) for c in self._constraints]
        info["f"] = [index_of(c) for c in self.flag_constraints.values()]
    try:
        result = reach_modes.MODES[MODE](self, solver_timeout, info)
    finally:
        dt = monotonic() - started
        info["t"] = round(dt, 4)
        STATS["calls"] += 1
        STATS["wall"] += dt
    info["r"] = result
    CALLS.write(json.dumps(info) + "\n")
    return result


cfg_state.X86Constraints.is_possible = instrumented
reach_modes.install_executor_hook()
ENTRY_HITS = reach_modes.install_entry_witness(None) if MODE.endswith("_entry") else None
if os.environ.get("OPT_CORR") == "1":
    import opt_corr
    opt_corr.install(log)
APPLY_STATS = None
if os.environ.get("OPT_APPLY") == "1":
    import opt_apply
    APPLY_STATS = opt_apply.install()

ACC = {}


def accumulate(owner, attr, flag=None):
    fn = getattr(owner, attr)

    def timed(*a, **k):
        t = monotonic()
        if flag:
            IN_APPLY[0] += 1
        try:
            return fn(*a, **k)
        finally:
            if flag:
                IN_APPLY[0] -= 1
            n, s = ACC.get(attr, (0, 0.0))
            ACC[attr] = (n + 1, s + monotonic() - t)
    setattr(owner, attr, timed)


for owner, attr, flag in ((X86SymbolicExecutor, "_handle_jcc", False), (VerifiedSummaryRuntime, "apply", True),
                          (VerifiedSummaryRuntime, "_solve", False)):
    accumulate(owner, attr, flag)
SOLVES = open(out / "solves.jsonl", "w")
_solve_inner = VerifiedSummaryRuntime._solve


CAPS = {}


def solve_logged(self, name, formula, expected="unsat"):
    if os.environ.get("CAPTURE_SOLVES") and CAPS.get(name, 0) < 3 and name in ("entry", "memgas_exit_guard_excluded"):
        CAPS[name] = CAPS.get(name, 0) + 1
        cs = Solver()
        cs.add(formula)
        (out / f"solve_{name}_{CAPS[name]}.smt2").write_text(cs.to_smt2())
    t = monotonic()
    rec = _solve_inner(self, name, formula, expected)
    SOLVES.write(json.dumps({"name": name, "exp": expected, "ans": rec.answer, "t": round(monotonic() - t, 3)}) + "\n")
    SOLVES.flush()
    return rec


VerifiedSummaryRuntime._solve = solve_logged
_apply_inner = VerifiedSummaryRuntime.apply


PROF = None
if os.environ.get("PROFILE_APPLY"):
    import cProfile
    PROF = cProfile.Profile()


def apply_logged(self, summary, state, path_condition=None):
    t = monotonic()
    ok = "exc"
    try:
        if PROF is not None:
            PROF.enable()
        try:
            r = _apply_inner(self, summary, state, path_condition)
        finally:
            if PROF is not None:
                PROF.disable()
        ok = "ok"
        return r
    finally:
        SOLVES.write(json.dumps({"apply": summary.kind, "res": ok, "t": round(monotonic() - t, 3)}) + "\n")


VerifiedSummaryRuntime.apply = apply_logged

P = be.BlockEquivalenceProver
_seg = be.run_x86_segment


def path_key(p):
    # Fresh summary symbols embed id(runtime) (a per-process address): mask long digit runs.
    from canon_hash import canon_hash
    return [p.kind, str(p.location), canon_hash(p.condition)]


def x86_segment(*a, **k):
    t, cpu = monotonic(), process_time()
    log("BEGIN run_x86_segment mode", MODE)
    r = _seg(*a, **k)
    SEG_DONE.append(1)
    if PROF is not None:
        PROF.dump_stats(str(out / "apply.prof"))
    log("PHASE run_x86_segment", f"{monotonic() - t:.1f}s", f"cpu {process_time() - cpu:.1f}s", "paths", len(r[0]), "defects", r[1],
        "reach", STATS, "entry_hits", ENTRY_HITS, "complement", APPLY_STATS, {k: (n, round(s, 1)) for k, (n, s) in ACC.items()})
    (out / "paths.json").write_text(json.dumps({"x86": [path_key(p) for p in r[0]]}))
    if RECORD:
        t = monotonic()
        s = Solver()
        for e in ORDER:
            s.add(e)
        (out / "table.smt2").write_text(s.to_smt2())
        log("dumped", len(ORDER), "conjuncts", f"{monotonic() - t:.1f}s")
    if os.environ.get("STOP") == "x86":
        raise Stop()
    return r


be.run_x86_segment = x86_segment
SEG_DONE = []
_evm = be.run_evm_segment


def evm_segment(*a, **k):
    r = _evm(*a, **k)
    (out / "evm_paths.json").write_text(json.dumps([path_key(p) for p in r[0]]))
    return r


be.run_evm_segment = evm_segment


def phase(owner, attr):
    fn = getattr(owner, attr)

    def timed(*a, **k):
        t, cpu = monotonic(), process_time()
        log("BEGIN", attr)
        r = "exc"
        try:
            r = fn(*a, **k)
            return r
        finally:
            log("PHASE", attr, f"{monotonic() - t:.1f}s", f"cpu {process_time() - cpu:.1f}s", r if attr == "_correspondence" else "")
    setattr(owner, attr, timed)


if os.environ.get("DUMP_PATHS") == "1":
    _cp = P.check_paths

    def check_paths_dump(self, evm, x86, premise, initial, records):
        if not SEG_DONE:
            return _cp(self, evm, x86, premise, initial, records)
        s = Solver()
        s.add(premise)
        for p in (*evm, *x86):
            s.add(p.condition)
        (out / "paths.smt2").write_text(s.to_smt2())
        (out / "paths_meta.json").write_text(json.dumps({"evm": len(evm), "x86": len(x86)}))
        log("dumped paths.smt2")
        if os.environ.get("STOP") == "dump":
            raise Stop()
        return _cp(self, evm, x86, premise, initial, records)
    P.check_paths = check_paths_dump

phase(P, "check_paths")
phase(P, "_correspondence")
_orig_check = P._check
CHK = {}


def _check(self, name, formula, records, **kw):
    t = monotonic()
    ok = _orig_check(self, name, formula, records, **kw)
    CHK[name[:12]] = CHK.get(name[:12], 0) + monotonic() - t
    if not name.startswith("evm_disjoint") or monotonic() - t > 1:
        log("check", name, records[-1].answer if records else ok, f"{monotonic() - t:.1f}s")
    return ok


P._check = _check


def pair_phase(self, *a, **k):
    raise Stop()


if os.environ.get("FULL") != "1":
    P._pair_phase = pair_phase
else:
    phase(P, "_pair_phase")

OPTIONS = dict(gas_check="full", gas_budget=1_000_000_000, num_inputs=0, timeout_ms=30000, node_seconds=seconds,
               first_pass_node_seconds=None, max_parameter_values=32, max_depth=400, max_instances=8192,
               wall_seconds=6 * 3600, summaries=True)
spec = eval(text)
bp.load_worker(stem, OPTIONS, [spec])
prover = bp._WORKER["setup"].prover
prover.node_timeout_seconds = seconds
prover.deadline = None
log("START", spec, "mode", MODE)
t = monotonic()
try:
    result = prover.prove(spec)
    log("DONE", result.status, result.reasons, f"{result.elapsed_seconds:.1f}s")
    th = result.theorem
    (out / "outcome.json").write_text(json.dumps({
        "status": result.status, "reasons": list(result.reasons),
        "evm_paths": result.evm_paths, "x86_paths": result.x86_paths,
        "correspondence": [str(c) for c in (th.correspondence if th is not None else ())],
        "records": sorted((r.name, r.answer) for r in result.obligations)}))
except Stop:
    log("STOPPED")
log("TOTAL", f"{monotonic() - t:.1f}s", "check seconds by prefix", {k: round(v, 1) for k, v in CHK.items()})
