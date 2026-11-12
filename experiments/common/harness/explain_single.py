"""Why B1 (terminal-path comparison) matters for SHL/SHR/SAR/SIGNEXTEND: per query
size and time in both comparison modes. Run from the frozen snapshot directory:

  python explain_single.py OUT.json [SOLVER_MS]
"""
import dataclasses
import json
import os
import sys
import time

sys.path.insert(0, os.getcwd())

import tests.integration.test_single_ins_equivalence as suite  # noqa: E402
import tests.support.instruction_equivalence as harness  # noqa: E402
from z3 import Z3_get_ast_id, is_app  # noqa: E402

CASES = ["SHL", "SHR", "SAR", "SIGNEXTEND", "BYTE", "DIV", "MOD"]


def dag_nodes(expr):
    seen, stack = set(), [expr]
    while stack:
        node = stack.pop()
        key = Z3_get_ast_id(node.ctx_ref(), node.as_ast())
        if key in seen:
            continue
        seen.add(key)
        if is_app(node):
            stack.extend(node.children())
    return len(seen)


def run(case, terminal_paths, solver_ms):
    queries = []
    original = harness._make_equivalence_solver

    def make(c):
        solver = original(c)
        check = solver.check

        def timed():
            mismatch = solver.assertions()[-1]
            started = time.process_time()
            answer = check()
            queries.append(dict(nodes=dag_nodes(mismatch), cpu_s=round(time.process_time() - started, 3),
                                answer=str(answer)))
            return answer
        solver.check = timed
        return solver

    harness._make_equivalence_solver = make
    try:
        changed = dataclasses.replace(case, x86_compare_terminal_paths=terminal_paths, solver_timeout_ms=solver_ms)
        started = time.process_time()
        try:
            harness.assert_instruction_equivalent(changed)
            outcome = "VERIFIED"
        except AssertionError as error:
            outcome = "unknown" if "solver_result=unknown" in str(error) else "FAILED"
        return dict(case=case.name, terminal_paths=terminal_paths, outcome=outcome,
                    total_cpu_s=round(time.process_time() - started, 2), queries=queries)
    finally:
        harness._make_equivalence_solver = original


def main():
    out, solver_ms = sys.argv[1], int(sys.argv[2]) if len(sys.argv) > 2 else 120_000
    cases = {c.name: c for c in suite.INSTRUCTION_REFINEMENT_CASES}
    rows = []
    for name in CASES:
        for terminal_paths in (True, False):
            row = run(cases[name], terminal_paths, solver_ms)
            rows.append(row)
            q = row["queries"]
            print(name, "terminal" if terminal_paths else "merged", row["outcome"], row["total_cpu_s"],
                  "queries", len(q), "max_nodes", max((x["nodes"] for x in q), default=0),
                  "max_query_cpu", max((x["cpu_s"] for x in q), default=0), flush=True)
            with open(out, "w") as f:
                json.dump(rows, f, indent=1)


if __name__ == "__main__":
    main()
