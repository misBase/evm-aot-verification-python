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


def cost(term):
    """Bit-blast estimate: width^2 per bvmul, 4 width^2 per division/remainder, with 2 symbolic operands."""
    seen, work, total = set(), [term], 0
    while work:
        t = work.pop()
        if t.get_id() in seen or not z3.is_app(t):
            continue
        seen.add(t.get_id())
        name = t.decl().name()
        if sum(not z3.is_bv_value(c) for c in t.children()) >= 2:
            if name == "bvmul":
                total += t.size() ** 2
            elif name.startswith(("bvudiv", "bvurem", "bvsdiv", "bvsrem", "bvsmod")):
                total += 4 * t.size() ** 2
        work.extend(t.children())
    return total


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
    print(f"[{time.monotonic() - T0:8.1f}s] BLAST {N[0]} dag {dag(formula)} -> {dag(blasted)} cost {cost(blasted)}"
          f" z3 {mb}->{z3.Z3_get_estimated_alloc_size() >> 20} MB {time.monotonic() - started:.1f}s", flush=True)
    if os.environ.get("TRACE_SOLVE"):
        started = time.monotonic()
        result = real(formula, budget)
        print(f"[{time.monotonic() - T0:8.1f}s] BLAST {N[0]} solved {result[0]} {time.monotonic() - started:.1f}s"
              f" z3 {z3.Z3_get_estimated_alloc_size() >> 20} MB", flush=True)
        return result
    return "unknown", None


bs.VerifiedSummaryRuntime._blasted_sat = staticmethod(traced)
sat_model = bs._sat_model
M = [0]


def traced_sat_model(query, timeout_ms):
    """Every summary-entry SAT check (also the blasted retry's): cost before, answer / seconds / Z3 MB after."""
    M[0] += 1
    k, c, started, mb = M[0], cost(query), time.monotonic(), z3.Z3_get_estimated_alloc_size() >> 20
    print(f"[{time.monotonic() - T0:8.1f}s] ENTRY {k} cost {c} budget {timeout_ms}ms z3 {mb} MB", flush=True)
    result = sat_model(query, timeout_ms)
    print(f"[{time.monotonic() - T0:8.1f}s] ENTRY {k} {result[0]} {time.monotonic() - started:.1f}s"
          f" z3 {z3.Z3_get_estimated_alloc_size() >> 20} MB", flush=True)
    return result


bs._sat_model = traced_sat_model
import runpy
runpy.run_path("cloud-inputs/n4/tools/probe_stacks.py", run_name="__main__")
