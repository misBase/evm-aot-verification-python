"""UF applications / lambdas in a goal part of a captured obligation.
Usage (cwd=snapshot, PYTHONPATH=.): ufs.py FILE.smt2 PART"""
import sys
sys.setrecursionlimit(100000)
from collections import Counter
from z3 import And, parse_smt2_file, is_app, is_quantifier, Z3_OP_UNINTERPRETED, Z3_OP_STORE

import verification.block_equivalence as be

f = And(*parse_smt2_file(sys.argv[1]))
part = be._goal_split(f)[int(sys.argv[2])]
goal = be._conjuncts(part)[0]  # ¬g (last child pushed last, popped first)
print("goal head:", goal.decl().name(), goal.arg(0).decl().name())
for side, t in zip(("LHS", "RHS"), goal.arg(0).children()):
    seen, work, ufs, lams, stores = set(), [t], Counter(), 0, 0
    while work:
        x = work.pop()
        if x.get_id() in seen:
            continue
        seen.add(x.get_id())
        if is_quantifier(x):
            lams += 1
            work.append(x.body())
            continue
        if not is_app(x):
            continue
        if x.decl().kind() == Z3_OP_UNINTERPRETED and x.num_args() > 0:
            ufs[x.decl().name()] += 1
        if x.decl().kind() == Z3_OP_STORE:
            stores += 1
        work.extend(x.children())
    print(side, "nodes", len(seen), "stores", stores, "lambdas", lams, "ufs", dict(ufs))
