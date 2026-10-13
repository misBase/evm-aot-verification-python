"""Walk the memory goal's sides down their Store spines; print each layer compactly.
Usage (cwd=snapshot, PYTHONPATH=.): chain.py FILE.smt2 PART [maxlen]"""
import sys
sys.setrecursionlimit(100000)
from z3 import And, parse_smt2_file, is_app, is_quantifier, Z3_OP_STORE, simplify

import verification.block_equivalence as be

N = int(sys.argv[3]) if len(sys.argv) > 3 else 200
f = And(*parse_smt2_file(sys.argv[1]))
part = be._goal_split(f)[int(sys.argv[2])]
goal = be._conjuncts(part)[0]


def short(t, n=N):
    return " ".join(str(t).replace("blk5377_30_None_None_", "").split())[:n]


def walk(t, depth=0, label=""):
    stores = []
    while is_app(t) and t.decl().kind() == Z3_OP_STORE:
        stores.append((t.arg(1), t.arg(2)))
        t = t.arg(0)
    pad = "  " * depth
    print(f"{pad}{label} {len(stores)} stores; top idx: {[short(i, 80) for i, _ in stores[:3]]} ... bottom idx: {[short(i, 80) for i, _ in stores[-3:]]}")
    if stores:
        print(f"{pad}  sample values: {[short(v, 120) for _, v in stores[:2]]}")
    if is_quantifier(t):
        print(f"{pad}  base LAMBDA var={t.var_name(0)} body: {short(t.body(), 600)}")
        # descend into arrays selected inside the lambda body
        seen, work = set(), [t.body()]
        while work:
            x = work.pop()
            if x.get_id() in seen or not is_app(x):
                continue
            seen.add(x.get_id())
            if x.decl().name() == "select" and (x.arg(0).decl().kind() == Z3_OP_STORE if is_app(x.arg(0)) else is_quantifier(x.arg(0))):
                if depth < 4:
                    walk(x.arg(0), depth + 1, "select-base")
                continue
            work.extend(x.children())
    else:
        print(f"{pad}  base: {short(t, 300)}")


for side, t in zip(("EVM?", "X86?"), goal.arg(0).children()):
    print("=====", side)
    walk(t)
