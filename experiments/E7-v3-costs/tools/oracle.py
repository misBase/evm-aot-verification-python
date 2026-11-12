"""B2 oracle routing: one exported obligation through the production `_check`,
with all routes (arm "all") or only one route (every other arm).

  oracle.py STEM FILE.smt2 NAME ROUTE BUDGET_S OUT.json

The preamble of `_check` (skolemization, quick exact solve, goal split,
pin_split) is the production one; only the route list is filtered, through the
`_winners_first` hook `_check` already calls. Fresh process, fresh proof cache.
"""
import json
import sys
import time
from pathlib import Path


def main():
    stem, smt2, name, route, budget, out = sys.argv[1:7]
    budget = float(budget)
    from z3 import And, parse_smt2_file
    from verification import block_parallel as bp
    from verification import block_equivalence as be
    from verification.block_program import BlockProgramResult
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from replay import options  # the same production options as the replays
    opts = options(type("A", (), dict(node_seconds=budget, trace=None))())
    evm, x86, initial, verifier = bp.build_inputs(stem, opts)
    prover = verifier._setup(evm, x86, initial, BlockProgramResult(), time.monotonic(), []).prover
    formula = And(*parse_smt2_file(smt2))
    if route != "all":
        be._ROUTE_ORDER_STATIC = False
        be._winners_first = lambda routes, stats: [r for r in routes if r[0] == route]
    prover._route_stats, prover._node_needed_unification, prover._potential_pending = {}, False, None
    prover._kept_failures = []
    prover.deadline = time.monotonic() + budget
    records, started, answer = [], time.monotonic(), None
    try:
        proved = prover._check(name, formula, records)
        answer = records[-1].answer if records else None
    except be.ProofBudgetExceeded:
        proved, answer = False, "budget"
    Path(out).write_text(json.dumps(dict(smt2=Path(smt2).name, name=name, route=route, budget=budget,
                                         wall=round(time.monotonic() - started, 2), proved=bool(proved),
                                         answer=answer, routes={f"{k[0]}{'+n' if k[1] else ''}": v for t in
                                                                prover._route_stats.values() for k, v in t.items()})))


if __name__ == "__main__":
    main()
