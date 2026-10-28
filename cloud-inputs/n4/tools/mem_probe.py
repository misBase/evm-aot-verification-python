"""Whole-node prove() with a memory sampler (diagnostics only: nothing here is a proof).

Usage (repo root, PYTHONPATH=.): mem_probe.py STEM NODES.json INDEX OUT.json
    [--seconds N] [--every S] [--cap-gb G] [--types-every K] [--x86-only]

Every --every seconds prints one line: RSS / peak RSS, Z3's own allocation estimate, the
process-level term caches (store_forwarding _MEMO with the characters of its string values,
_SHARED_FORWARD and its keep-alive list), the prover's lemma cache, the summary runtime's
certificates (count and total characters of every obligation text inside, lemmas included),
the executor's live / final / cut states. Every --types-every samples also the most common
gc-tracked object types. Above --cap-gb of RSS the process exits (code 3) so the container
is never OOM-killed. --x86-only stops right after the x86 segment.
"""
import collections
import gc
import json
import os
import sys
import threading
import time

import z3

import common.store_forwarding as sf
import verification.block_equivalence as be
import verification.loop_induction as li
import x86_64.cfg_executor as cx
from tools.probe_block_obligations import build_prover, parse_nodes

argv = sys.argv[1:]
stem, node_json, index, out = argv[0], argv[1], int(argv[2]), argv[3]


def opt(name, default, cast=float):
    return cast(argv[argv.index(name) + 1]) if name in argv else default


seconds, every, cap = opt("--seconds", 43200), opt("--every", 60), opt("--cap-gb", 10.0)
types_every = opt("--types-every", 10, int)
x86_only = "--x86-only" in argv
T0 = time.monotonic()
seen = dict(executor=None, runtime=None, prover=None, phase="setup")


def status_kb(field):
    with open("/proc/self/status") as f:
        for line in f:
            if line.startswith(field + ":"):
                return int(line.split()[1])
    return 0


def text_chars(value, memo):
    """Characters of every obligation formula text reachable from `value`."""
    if id(value) in memo:
        return 0
    memo.add(id(value))
    if isinstance(value, be.Obligation):
        return len(value.formula) + sum(text_chars(lemma, memo) for lemma in value.lemmas)
    if isinstance(value, (list, tuple)):
        return sum(text_chars(v, memo) for v in value)
    if hasattr(value, "__dataclass_fields__"):
        return sum(text_chars(getattr(value, f), memo) for f in value.__dataclass_fields__)
    return 0


def sample(n):
    rss, hwm = status_kb("VmRSS") / 1e6, status_kb("VmHWM") / 1e6
    try:
        z3_alloc = z3.Z3_get_estimated_alloc_size() / 1e9
    except Exception:
        z3_alloc = -1
    memo = list(sf._MEMO.values())
    memo_chars = sum(len(v[1]) for v in memo if isinstance(v[1], str))
    memo_obl = sum(text_chars(v[1], set()) for v in memo if isinstance(v[1], be.Obligation))
    shared = len(sf._SHARED_FORWARD)
    alive = len(sf._SHARED_FORWARD.get(sf._ALIVE, ()))
    runtime, ex, prover = seen["runtime"], seen["executor"], seen["prover"]
    certs = list(runtime.certificates) if runtime is not None else []
    cert_chars = text_chars(certs, set())
    statement = len(runtime._statement or ()) if runtime is not None else 0
    lemma_cache = len(prover._lemma_cache) if prover is not None else 0
    states = ((len(ex.work_list), len(ex.final_states), len(ex.cut_states),
               sum(len(v) for v in getattr(ex, "merge_buffers", {}).values()))
              if ex is not None else None)
    print(f"[{time.monotonic() - T0:8.1f}s] MEM {seen['phase']} rss {rss:.2f}G peak {hwm:.2f}G z3 {z3_alloc:.2f}G "
          f"memo {len(memo)} ({memo_chars / 1e6:.0f}M chars str, {memo_obl / 1e6:.0f}M chars obl) "
          f"shared_fwd {shared} alive {alive} lemma_cache {lemma_cache} "
          f"certs {len(certs)} ({cert_chars / 1e6:.0f}M chars) statement {statement} "
          f"states(live,final,cut,buffered) {states}", flush=True)
    print("   z3 net alloc by step kind (GB, calls):", {k: (round(v / 1e9, 2) if not k.endswith("#") else v)
                                                       for k, v in sorted(delta.items())}, flush=True)
    if n % types_every == 0:
        counts = collections.Counter(type(o).__name__ for o in gc.get_objects())
        print("   types:", counts.most_common(12), flush=True)
    if rss > cap:
        print(f"[{time.monotonic() - T0:8.1f}s] RSS {rss:.2f}G above cap {cap}G: exit 3", flush=True)
        os._exit(3)


def sampler():
    n = 0
    while True:
        time.sleep(every)
        n += 1
        try:
            sample(n)
        except Exception as exc:  # a dict resized under us: try again next time
            print("sampler:", type(exc).__name__, exc, flush=True)


# Net Z3 allocation (Z3_get_estimated_alloc_size) left behind by each kind of step.
delta = collections.Counter()


def z3_alloc():
    return z3.Z3_get_estimated_alloc_size()


def attributed(kind, fn):
    def run(*a, **k):
        before = z3_alloc()
        try:
            return fn(*a, **k)
        finally:
            delta[kind] += z3_alloc() - before
            delta[kind + "#"] += 1
    return run


cx.X86SymbolicExecutor._is_state_reachable = attributed("reach", cx.X86SymbolicExecutor._is_state_reachable)
cx.X86SymbolicExecutor.execute_state = attributed("step", cx.X86SymbolicExecutor.execute_state)
orig_execute = cx.X86SymbolicExecutor.execute


def execute(self, *a, **k):
    seen["executor"] = self
    return orig_execute(self, *a, **k)


cx.X86SymbolicExecutor.execute = execute
orig_segment = be.run_x86_segment


class Stop(BaseException):  # past prove()'s `except Exception`
    pass


def segment(*a, **k):
    seen["runtime"], seen["phase"] = k.get("summary_runtime"), "x86"
    if k.get("summary_runtime") is not None:
        k["summary_runtime"].apply = attributed("apply", k["summary_runtime"].apply)
    started = time.monotonic()
    try:
        return orig_segment(*a, **k)
    finally:
        seen["phase"] = "pairs"
        print(f"[{time.monotonic() - T0:8.1f}s] x86 segment end after {time.monotonic() - started:.1f}s", flush=True)
        sample(0)
        if x86_only:
            raise Stop()


be.run_x86_segment = segment
spec = parse_nodes(json.loads(open(node_json).read()))[index]
prover = build_prover(stem, base_addr=0x1000, timeout_ms=30000, node_seconds=seconds, max_depth=400, summaries=True)
seen["prover"] = prover
threading.Thread(target=sampler, daemon=True).start()
try:
    result = prover.prove(spec)
    summary = dict(status="proved" if result.proved else "inconclusive", seconds=result.elapsed_seconds,
                   queries=result.queries, evm_paths=result.evm_paths, x86_paths=result.x86_paths,
                   reasons=list(result.reasons))
except Stop:
    summary = dict(status="x86-only", seconds=time.monotonic() - T0)
sample(0)
print(summary, flush=True)
with open(out, "w") as f:
    json.dump(summary, f, indent=2)
