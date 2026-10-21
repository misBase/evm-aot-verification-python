"""Profile one node's x86 segment execution (where paths fork, how long reachability takes).

Usage (repo root, PYTHONPATH=.): x86_profile.py STEM NODES.json INDEX [--seconds N] [--every S]

Runs prove() up to and including run_x86_segment with a node budget of --seconds, then stops.
Every --every seconds (and at the end) prints: executed blocks, live work list, finished paths,
the blocks executed most often, the jcc blocks that forked most often (both branches kept),
summary hits / precondition failures, and reachability-check time.
Diagnostics only: nothing here is a proof.
"""
import collections
import json
import sys
import threading
import time
from pathlib import Path

import verification.block_equivalence as be
import x86_64.cfg_executor as cx
from tools.probe_block_obligations import build_prover, parse_nodes

argv = sys.argv[1:]
stem, node_json, index = argv[0], argv[1], int(argv[2])
seconds = float(argv[argv.index("--seconds") + 1]) if "--seconds" in argv else 1200
every = float(argv[argv.index("--every") + 1]) if "--every" in argv else 60
T0 = time.monotonic()
executed, forks, reach = collections.Counter(), collections.Counter(), [0, 0.0, 0]
summaries = collections.Counter()  # also "seconds": time inside summary application
last = [T0]
ex_ref = []


def report(tag):
    ex = ex_ref[-1] if ex_ref else None
    live = len(ex.work_list) if ex is not None else -1
    done = (len(ex.final_states), len(ex.cut_states)) if ex is not None else (-1, -1)
    print(f"[{time.monotonic() - T0:8.1f}s] {tag}: executed {sum(executed.values())} live {live} "
          f"final/cut {done} reach {reach[0]} checks {reach[1]:.1f}s pruned {reach[2]}", flush=True)
    print("   top blocks:", [(hex(a), n) for a, n in executed.most_common(12)], flush=True)
    print("   top forks:", [(hex(a), n) for a, n in forks.most_common(12)], flush=True)
    print("   summaries:", dict(summaries), flush=True)


orig_execute = cx.X86SymbolicExecutor.execute
orig_state = cx.X86SymbolicExecutor.execute_state
orig_reach = cx.X86SymbolicExecutor._is_state_reachable


def execute(self, *a, **k):
    ex_ref.append(self)
    return orig_execute(self, *a, **k)


def execute_state(self, gs, *a, **k):
    addr = gs.node.address if gs.node else None
    executed[addr] += 1
    out = orig_state(self, gs, *a, **k)
    if out and len(out) > 1:
        forks[addr] += 1
    if time.monotonic() - last[0] > every:
        last[0] = time.monotonic()
        report("progress")
    return out


SLOW = float(argv[argv.index("--dump-slow") + 1]) if "--dump-slow" in argv else None


def reachable(self, state):
    t = time.monotonic()
    timer = None
    if SLOW is not None:
        # A check still running after SLOW seconds: write its path condition (diagnostics).
        text = be._to_smt2(state.get_constraints().as_bool())
        addr = state.node.address if state.node else 0

        def dump():
            path = Path(f"slow_reach_{addr:x}_{reach[0]}.smt2")
            path.write_text(text)
            print(f"[{time.monotonic() - T0:8.1f}s] slow reachability check at {addr:#x} -> {path}", flush=True)
        timer = threading.Timer(SLOW, dump)
        timer.start()
    ok = orig_reach(self, state)
    if timer is not None:
        timer.cancel()
    reach[0] += 1
    reach[1] += time.monotonic() - t
    reach[2] += not ok
    if time.monotonic() - t > 5:
        print(f"[{time.monotonic() - T0:8.1f}s] reachability check {time.monotonic() - t:.1f}s "
              f"at {state.node.address if state.node else 0:#x} -> {ok}", flush=True)
    return ok


cx.X86SymbolicExecutor.execute = execute
cx.X86SymbolicExecutor.execute_state = execute_state
cx.X86SymbolicExecutor._is_state_reachable = reachable


class Stop(Exception):
    pass


orig_segment = be.run_x86_segment


def segment(*a, **k):
    runtime = k.get("summary_runtime")
    if runtime is not None:
        orig_apply = runtime.apply

        def apply(summary, *aa, **kk):
            started = time.monotonic()
            try:
                result = orig_apply(summary, *aa, **kk)
                summaries["seconds"] += time.monotonic() - started
                summaries[f"{summary.kind}@{hex(summary.entry_addr)}"] += 1
                return result
            except Exception as exc:
                summaries["seconds"] += time.monotonic() - started
                summaries[f"REJECT {summary.kind}@{hex(summary.entry_addr)}: {type(exc).__name__}"] += 1
                raise
        runtime.apply = apply
    try:
        paths, defects, notes = orig_segment(*a, **k)
    finally:
        report("x86 segment end")
    print("paths", len(paths), collections.Counter(f"{p.kind}@{p.location}" for p in paths), defects, flush=True)
    raise Stop()


be.run_x86_segment = segment
spec = parse_nodes(json.loads(Path(node_json).read_text()))[index]
print("spec", spec, flush=True)
prover = build_prover(stem, base_addr=0x1000, timeout_ms=30000, node_seconds=seconds, max_depth=400,
                      summaries=True)
result = prover.prove(spec)
print("result", result.reasons, flush=True)
