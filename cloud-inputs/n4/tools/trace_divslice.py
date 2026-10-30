"""cloud-inputs/n4/tools/probe_stacks.py plus a log line before and after every DIV slice lemma proof
(prove_div_slice): entry address, paths, seconds, RSS (diagnostics only). Arguments as probe_traced.py."""
import time

import x86_64.summaries.div_proof as dp
from common.node_monitor import rss_bytes

T0 = time.monotonic()
real = dp.prove_div_slice


def traced(summary, blocks, **k):
    entry, started = summary.payload.entry_addr, time.monotonic()
    print(f"[{started - T0:8.1f}s] DIVSLICE {entry:#x} start rss {rss_bytes() >> 20} MB", flush=True)
    try:
        lemma = real(summary, blocks, **k)
        print(f"[{time.monotonic() - T0:8.1f}s] DIVSLICE {entry:#x} proved {time.monotonic() - started:.1f}s rss {rss_bytes() >> 20} MB", flush=True)
        return lemma
    except BaseException as exc:
        print(f"[{time.monotonic() - T0:8.1f}s] DIVSLICE {entry:#x} {type(exc).__name__} {time.monotonic() - started:.1f}s", flush=True)
        raise


dp.prove_div_slice = traced
import runpy
runpy.run_path("cloud-inputs/n4/tools/probe_stacks.py", run_name="__main__")
