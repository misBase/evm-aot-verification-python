"""Count selects over the x86 stack chain (Store* over stack_rest) in a goal part,
raw / simplify / skolem+normalize_word_arith. Prints distinct read indices.
Usage (cwd=snapshot, PYTHONPATH=.): stackreads.py FILE.smt2 PART"""
import sys
from time import monotonic
sys.setrecursionlimit(100000)
from collections import Counter
from z3 import And, parse_smt2_file, is_app, is_quantifier, Z3_OP_STORE, Z3_OP_SELECT, simplify

import verification.block_equivalence as be


def base(a):
    while is_app(a) and a.decl().kind() == Z3_OP_STORE:
        a = a.arg(0)
    return a


def report(label, f):
    seen, work, idx, n = set(), [f], Counter(), 0
    while work:
        x = work.pop()
        if x.get_id() in seen:
            continue
        seen.add(x.get_id())
        if is_quantifier(x):
            work.append(x.body())
            continue
        if not is_app(x):
            continue
        if x.decl().kind() == Z3_OP_SELECT:
            b = base(x.arg(0))
            if is_app(b) and b.decl().name().endswith("stack_rest"):
                n += 1
                idx[" ".join(str(x.arg(1)).split())[:90]] += 1
        work.extend(x.children())
    print(f"{label}: {n} stack_rest-chain selects, {len(idx)} distinct idx", flush=True)
    for k, v in sorted(idx.items())[:12]:
        print("   ", v, k)


f = And(*parse_smt2_file(sys.argv[1]))
part = be._goal_split(f)[int(sys.argv[2])]
report("raw", part)
report("simplify", simplify(part))
sk, _ = be.skolemize_array_disequalities(part)
t = monotonic()
norm, rw = be.normalize_word_arith(sk)
print(f"normalize {monotonic()-t:.1f}s rewrites={len(rw)}")
report("normalized", norm)
