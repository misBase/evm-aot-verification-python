"""Structure of a captured pair obligation: conjuncts, goal parts, sizes.
Usage (cwd=snapshot, PYTHONPATH=.): struct.py FILE.smt2"""
import sys
sys.setrecursionlimit(100000)
from z3 import And, parse_smt2_file, is_not, is_and, is_eq, Z3_ARRAY_SORT, is_app

import verification.block_equivalence as be


def dag_size(t, seen=None):
    seen = set() if seen is None else seen
    stack, n = [t], 0
    while stack:
        x = stack.pop()
        if x.get_id() in seen:
            continue
        seen.add(x.get_id())
        n += 1
        if is_app(x):
            stack.extend(x.children())
        elif hasattr(x, "body"):
            stack.append(x.body())
    return n


f = And(*parse_smt2_file(sys.argv[1]))
parts = be._conjuncts(f)
print(len(parts), "conjuncts")
for k, c in enumerate(parts):
    s = str(c).replace("\n", " ")
    print(f"[{k}] size={dag_size(c)} {s[:300]}")
gs = be._goal_split(f)
print("goal split:", None if gs is None else len(gs))
top = f
while is_and(top) and top.num_args() == 1:
    top = top.arg(0)
last = top.children()[-1]
if is_not(last) and is_and(last.arg(0)):
    for k, g in enumerate(last.arg(0).children()):
        kind = g.arg(0).sort() if is_eq(g) else g.sort()
        print(f"goal[{k}] sort={kind} size={dag_size(g)} {str(g)[:400]!r}")
