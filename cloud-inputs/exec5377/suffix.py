"""Suffix-first refutation on captured `premise /\\ X` queries.  usage: suffix.py FILE..."""
import sys
from time import monotonic

from z3 import And, SolverFor, is_and, parse_smt2_file


def flat(e, out):
    if is_and(e):
        for c in e.children():
            flat(c, out)
    else:
        out.append(e)
    return out


for f in sys.argv[1:]:
    (q,) = list(parse_smt2_file(f))
    # q = And(premise, violated): goal part is the last top-level child
    top = q.children() if is_and(q) else [q]
    premise, goal = top[:-1], top[-1]
    cs = flat(And(*premise), [])
    row = [f.split("/")[-1], len(cs)]
    for k in (0, 4, 16, None):
        s = SolverFor("QF_AUFBV")
        s.set(timeout=30000)
        s.add(*(cs if k is None else cs[len(cs) - k:] if k else []), goal)
        t = monotonic()
        r = s.check()
        row.append((k, str(r), round(monotonic() - t, 3)))
    print(row, flush=True)
