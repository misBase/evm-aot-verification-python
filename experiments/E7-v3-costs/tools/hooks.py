"""V3 cost observer: spans on fixed c68c4df function boundaries + cheap counters.

Never changes arguments, results or exceptions; adds no solving. Spans reuse
the e2_time_v1 span engine (owner thread only). Counters (outermost call per
thread) cover hot primitives such as Solver.check, where one event per call
would be too heavy.
"""
import json
import os
import resource
import sys
import threading
import time
from functools import wraps
from pathlib import Path

HERE = Path(__file__).resolve().parent
OBS = None
COUNTS = {}           # label -> [calls, seconds]
_LOCK = threading.Lock()
_DEPTH = threading.local()
EXPORTED = [0]


def _engine():
    import importlib.util
    spec = importlib.util.spec_from_file_location("v3_span_engine", HERE.parent / "e2_time_v1/observer.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def counter(owner, name, label):
    """Accumulate calls/seconds of the outermost call per thread."""
    original = getattr(owner, name)
    if getattr(original, "_v3_counter", False):
        return

    @wraps(original)
    def wrapper(*args, **kwargs):
        depth = getattr(_DEPTH, label, 0)
        if depth:
            return original(*args, **kwargs)
        setattr(_DEPTH, label, 1)
        started = time.monotonic()
        try:
            return original(*args, **kwargs)
        finally:
            spent = time.monotonic() - started
            setattr(_DEPTH, label, 0)
            with _LOCK:
                row = COUNTS.setdefault(label, [0, 0.0])
                row[0] += 1
                row[1] += spent
    wrapper._v3_counter = True
    setattr(owner, name, wrapper)


def counter_everywhere(module_name, name, label):
    """Patch the defining module and every already-imported binding of it."""
    module = sys.modules[module_name]
    original = getattr(module, name)
    for mod in list(sys.modules.values()):
        if getattr(mod, "__name__", "").split(".")[0] in ("verification", "common", "x86_64", "state", "evm_ir"):
            if getattr(mod, name, None) is original:
                counter(mod, name, label)


def snapshot_counts():
    with _LOCK:
        return {k: [v[0], round(v[1], 4)] for k, v in COUNTS.items()}


def delta_counts(before):
    now = snapshot_counts()
    out = {}
    for k, (n, s) in now.items():
        n0, s0 = before.get(k, (0, 0.0))
        if n - n0:
            out[k] = [n - n0, round(s - s0, 4)]
    return out


def spec_data(s):
    return dict(pc=s.pc, d=s.stack_depth, m=s.memory_size, f=s.free_memory_pointer,
                k=[list(p) for p in s.stack_constants])


def maxrss_mb():
    r = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    return round(r / (1024 * 1024) if sys.platform == "darwin" else r / 1024, 1)


def op_name(chain, k):
    ops = getattr(chain.block, "operations", None) or ()
    return getattr(getattr(ops[k], "kind", None), "name", str(getattr(ops[k], "kind", ""))) if 0 <= k < len(ops) else None


def phase():
    for frame in reversed(OBS.stack):
        if frame["label"] in ("lemma.prove", "chain.node", "h2.close_edge", "h2.quick", "h0.close_edge",
                              "local.prove", "program.discovery"):
            return frame["label"]
    return "other"


def install():
    global OBS
    out = Path(os.environ["V3_COST_DIR"])
    events = out / "events"
    events.mkdir(parents=True, exist_ok=True)
    OBS = _engine().Observer(events)
    import z3
    import verification.block_parallel as bp
    import verification.block_equivalence as be
    import verification.block_program as bprog
    import verification.block_summaries as bs
    import verification.instruction_chain as ic
    import verification.proof_cache as pc
    import common.isolated_sat as iso
    import common.store_forwarding as sf
    OBS.emit("v3_install", argv=sys.argv[:3], snapshot=str(Path(bp.__file__).resolve().parents[1]))

    def hook(owner, name, label, **kw):
        OBS.hook([(owner, name)], label, **kw)

    # ---- counters (no events)
    counter(z3.Solver, "check", "z3.check")
    counter_everywhere("common.isolated_sat", "isolated_sat", "z3.isolated_child")
    counter(pc, "query_key", "cache.query_key")
    counter(pc, "statement_key", "cache.statement_key")
    counter_everywhere("common.store_forwarding", "forward_selects", "expr.forward_selects")
    if hasattr(be, "normalize_word_arith"):
        counter_everywhere("verification.block_equivalence", "normalize_word_arith", "expr.normalize")
    counter_everywhere("verification.block_parallel", "reset_node_caches", "worker.reset_caches")

    # ---- parent: phases and dispatch ledger
    hook(bp, "verify_parallel", "program.verify")
    hook(bprog.BlockProgramVerifier, "_setup", "program.setup")
    hook(bp, "discover", "program.discovery")
    hook(bp, "proof_groups", "program.groups",
         after=lambda r, a, k, b: dict(groups=len(r), contexts=sum(len(c) for c in r.values())))
    hook(bp, "_prove_all", "program.proofs_H2")
    hook(bp.ParallelProgramCertificate, "valid", "program.consumer",
         after=lambda r, a, k, b: dict(accepted=bool(r)))
    hook(bp, "_attempt", "sched.attempt",
         before=lambda a, k, c: dict(spec=spec_data(a[0]), offered=a[1]),
         after=lambda r, a, k, b: dict(budget=r[0], chain=bool(r[1])))
    hook(bp, "_record", "sched.record",
         before=lambda a, k, c: dict(spec=spec_data(a[1]["spec"]), status=a[2], seconds=a[1]["seconds"],
                                     contexts=len(a[1].get("contexts", ())) or 1, proved=bool(a[1]["proved"]),
                                     proof_kind=a[1].get("proof_kind"),
                                     chain_attempt=a[1].get("chain_attempt"),
                                     memory=bool(a[1].get("memory_exceeded")),
                                     reasons=[str(x)[:160] for x in list(a[1]["reasons"])[:2]]))

    # ---- worker: task and its parts
    task_before = {}

    def t_before(a, k, c):
        task_before["counts"] = snapshot_counts()
        task_before["lemma"] = bs.lemma_seconds()
        contexts = a[3] if len(a) > 3 else k.get("contexts")
        chain = a[4] if len(a) > 4 else k.get("chain", False)
        return dict(spec=spec_data(a[0]), node_seconds=a[1], contexts=len(contexts or (a[0],)), chain=bool(chain))

    def t_after(r, a, k, b):
        return dict(proved=bool(r["proved"]), closed=bool(r["proved"] and not r["reasons"]), status=r["status"],
                    proof_kind=r.get("proof_kind"), chain_attempt=r.get("chain_attempt"),
                    seconds=r["seconds"], queries=r["queries"], failed=len(r.get("failed", ())),
                    reasons=[str(x)[:160] for x in list(r["reasons"])[:3]],
                    counts=delta_counts(task_before["counts"]),
                    lemma_seconds=round(bs.lemma_seconds() - task_before["lemma"], 3), maxrss_mb=maxrss_mb())
    hook(bp, "prove_instance", "task", before=t_before, after=t_after)
    hook(be.BlockEquivalenceProver, "prove", "local.prove",
         after=lambda r, a, k, b: dict(proved=r.status == "proved", evm_paths=r.evm_paths, x86_paths=r.x86_paths,
                                       queries=r.queries))
    hook(be, "run_evm_segment", "local.evm_segment")
    hook(be, "run_x86_segment", "local.x86_segment",
         after=lambda r, a, k, b: dict(outcomes=len(r[0]), incomplete=len(r[1])))
    hook(bp, "close_edge", "h2.close_edge", before=lambda a, k, c: dict(name=str(a[1])[:40]),
         after=lambda r, a, k, b: dict(proved=bool(r.proved)))
    hook(bp, "_quick_whole_h2", "h2.quick", before=lambda a, k, c: dict(edges=len(a[1])),
         after=lambda r, a, k, b: dict(closed=sum(x is not None for x in a[4])))
    hook(bp, "prepare_shared", "h2.prepare_shared")
    hook(ic, "prove_node", "chain.node")
    hook(ic, "semantic_plan", "chain.plan")
    hook(ic.ChainProver, "prove_op", "chain.op",
         before=lambda a, k, c: dict(k=a[1], op=op_name(a[0], a[1])),
         after=lambda r, a, k, b: dict(ok=r is not None and r is not False))
    hook(ic.ChainProver, "prove_exit", "chain.exit")
    hook(bs.VerifiedSummaryRuntime, "_prove_lemma", "lemma.prove",
         before=lambda a, k, c: dict(hit=a[2] in a[1], kind=getattr(a[3], "kind", None)),
         after=lambda r, a, k, b: dict(ok=r[1] is not None))
    hook(bs.VerifiedSummaryRuntime, "_discharge", "lemma.discharge")
    hook(bs.VerifiedSummaryRuntime, "_apply_lemma", "summary.apply_lemma",
         before=lambda a, k, c: dict(kind=getattr(a[1], "kind", None)))
    hook(bs.VerifiedSummaryRuntime, "_apply_div", "summary.apply_div",
         before=lambda a, k, c: dict(kind=getattr(a[1], "kind", None)))
    hook(pc, "lemma_proved", "lemma.cache_lookup",
         before=lambda a, k, c: dict(key=str(a[0])[:24]), after=lambda r, a, k, b: dict(hit=bool(r)))

    if os.environ.get("V3_FINE"):  # finer split of local.prove's own time (opt-in: keeps older runs comparable)
        import verification.block_relation as br
        hook(be, "paths_digest", "local.digest")
        hook(be, "obligation_manifest", "local.manifest")
        hook(be, "terminal_observable_conditions", "local.observables")
        hook(be, "host_model_axioms", "local.axioms")
        hook(be.BlockEquivalenceProver, "check_paths", "local.check_paths")
        hook(be.BlockEquivalenceProver, "_correspondence", "local.correspondence")
        hook(be.BlockEquivalenceProver, "_pair_phase", "local.pair_phase")
        hook(br.BlockRelationSchema, "build_havoc", "rel.havoc")
        hook(br.BlockRelationSchema, "relation_goals", "rel.goals")

    export_min = float(os.environ.get("V3_EXPORT_MIN_S", "0") or 0)
    export_cap = int(os.environ.get("V3_EXPORT_CAP", "20"))
    check_before = {}

    def c_scope(a, k, c):
        return not OBS.has("check")

    def c_before(a, k, c):
        stats = getattr(a[0], "_route_stats", {}) or {}
        check_before["routes"] = {cls: dict(v) for cls, v in stats.items()}
        check_before["counts"] = snapshot_counts()
        check_before["t"] = time.monotonic()
        return dict(name=str(a[1])[:60], phase=phase(), expected=k.get("expected", "unsat"))

    def c_after(r, a, k, b):
        stats = getattr(a[0], "_route_stats", {}) or {}
        old = check_before.get("routes", {})
        routes = {}
        for cls, table in stats.items():
            for (route, norm), (wins, secs) in table.items():
                w0, s0 = old.get(cls, {}).get((route, norm), (0, 0.0))
                if secs - s0 > 0.0005 or wins - w0:
                    key = f"{route}{'+n' if norm else ''}"
                    w, s = routes.get(key, (0, 0.0))
                    routes[key] = (w + wins - w0, round(s + secs - s0, 3))
        out = dict(proved=bool(r), answer=getattr(a[3][-1], "answer", None) if a[3] else None,
                   routes={k2: list(v) for k2, v in routes.items()}, counts=delta_counts(check_before["counts"]))
        wall = time.monotonic() - check_before["t"]
        if export_min and wall >= export_min and EXPORTED[0] < export_cap:
            EXPORTED[0] += 1
            started = time.monotonic()
            try:
                solver = z3.Solver()
                solver.add(a[2])
                path = out_dir_obl / f"{os.getpid()}-{EXPORTED[0]}.smt2"
                path.write_text(solver.to_smt2())
                out.update(exported=path.name)
            except Exception as exc:  # noqa: BLE001 - diagnostics only
                out.update(export_error=type(exc).__name__)
            out.update(export_seconds=round(time.monotonic() - started, 3), wall_before_export=round(wall, 3))
        return out
    out_dir_obl = out / "obligations"
    if export_min:
        out_dir_obl.mkdir(exist_ok=True)
    hook(be.BlockEquivalenceProver, "_check", "check", scope=c_scope, before=c_before, after=c_after)

    import atexit

    def finish():
        try:
            OBS.emit("v3_counts", counts=snapshot_counts(), maxrss_mb=maxrss_mb())
            status = OBS.snapshot()
            (events / f"status-{os.getpid()}.json").write_text(json.dumps(status))
        except Exception:  # noqa: BLE001
            pass
    atexit.register(finish)
