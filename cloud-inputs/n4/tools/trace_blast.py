"""cloud-inputs/n4/tools/probe_stacks.py, but every blasted summary-entry SAT check (VerifiedSummaryRuntime._blasted_sat)
is measured and dumped instead of solved (diagnostics only): DAG size of the formula before and after
simplify(blast_select_store=True), Z3 MB, seconds; formulas go to $TRACE_DIR/blast_<n>.smt2. With
TRACE_SOLVE=1 the check is also solved (as production). Arguments as probe_traced.py."""
import os
import time
from pathlib import Path

import z3

import verification.block_summaries as bs

out = Path(os.environ.get("TRACE_DIR", "blast-trace"))
out.mkdir(parents=True, exist_ok=True)
T0, N = time.monotonic(), [0]


def dag(term):
    seen, work = set(), [term]
    while work:
        t = work.pop()
        if t.get_id() in seen:
            continue
        seen.add(t.get_id())
        if z3.is_app(t):
            work.extend(t.children())
    return len(seen)


real = bs.VerifiedSummaryRuntime._blasted_sat


def traced(formula, budget):
    N[0] += 1
    started, mb = time.monotonic(), z3.Z3_get_estimated_alloc_size() >> 20
    blasted = z3.simplify(formula, blast_select_store=True)
    s = z3.Solver()
    s.add(formula)
    (out / f"blast_{N[0]}.smt2").write_text(s.to_smt2())
    print(f"[{time.monotonic() - T0:8.1f}s] BLAST {N[0]} dag {dag(formula)} -> {dag(blasted)}"
          f" z3 {mb}->{z3.Z3_get_estimated_alloc_size() >> 20} MB {time.monotonic() - started:.1f}s", flush=True)
    if os.environ.get("TRACE_SOLVE"):
        return real(formula, budget)
    return "unknown", None


bs.VerifiedSummaryRuntime._blasted_sat = staticmethod(traced)
import runpy
runpy.run_path("cloud-inputs/n4/tools/probe_stacks.py", run_name="__main__")
