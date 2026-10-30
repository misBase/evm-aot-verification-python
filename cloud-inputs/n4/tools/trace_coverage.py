"""cloud-inputs/n4/tools/probe_stacks.py plus a trace of the coverage step (diagnostics only): every
coverage_by_prefix_tree call (paths, result, seconds), _retry_over_nonlinear_mul on a coverage formula,
and solve_query / solve_pure_bv calls over 2s (answer, seconds, Z3 MB before/after); each coverage
formula is written to $TRACE_DIR/<label>_coverage.smt2. Arguments as probe_traced.py."""
import os
import time
from pathlib import Path

import z3

import verification.block_equivalence as be

out = Path(os.environ.get("TRACE_DIR", "coverage-trace"))
out.mkdir(parents=True, exist_ok=True)
T0 = time.monotonic()


def log(*a):
    print(f"[{time.monotonic() - T0:8.1f}s] TRACE", *a, flush=True)


def z3_mb():
    return z3.Z3_get_estimated_alloc_size() >> 20


def timed(name, fn, slow=2.0):
    def run(*a, **k):
        started, before = time.monotonic(), z3_mb()
        result = fn(*a, **k)
        if time.monotonic() - started > slow:
            log(name, str(result)[:40], f"{time.monotonic() - started:.1f}s", f"z3 {before}->{z3_mb()} MB")
        return result
    return run


be.solve_query = timed("solve_query", be.solve_query)
be.solve_pure_bv = timed("solve_pure_bv", be.solve_pure_bv)
tree = be.coverage_by_prefix_tree


def traced_tree(premise, conditions, *a, **k):
    n = len(list(out.glob("*_coverage.smt2")))
    s = z3.Solver()
    s.add(z3.And(premise, z3.Not(z3.Or(*conditions))))
    (out / f"cov{n}_{len(conditions)}paths_coverage.smt2").write_text(s.to_smt2())
    started = time.monotonic()
    result = tree(premise, conditions, *a, **k)
    log("prefix tree", len(conditions), "paths ->", result, f"{time.monotonic() - started:.1f}s z3 {z3_mb()} MB")
    return result


be.coverage_by_prefix_tree = traced_tree
retry = be.BlockEquivalenceProver._retry_over_nonlinear_mul
be.BlockEquivalenceProver._retry_over_nonlinear_mul = lambda self, *a, **k: timed("mul->UF", lambda: retry(self, *a, **k), 0.0)()
import runpy
runpy.run_path("cloud-inputs/n4/tools/probe_stacks.py", run_name="__main__")
