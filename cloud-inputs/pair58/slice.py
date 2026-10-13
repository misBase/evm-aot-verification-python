"""Refute goal part k with a weakened premise (conjuncts dropped by a filter): sound for UNSAT.
Usage (cwd=snapshot, PYTHONPATH=.): slice.py FILE.smt2 PART timeout_ms MODE
MODE: nogas (drop conjuncts mentioning gas_remaining) | nonlin (drop conjuncts with symbolic*symbolic bvmul)
      | goalonly (keep only conjuncts sharing a constant with the goal) | none"""
import sys
from time import monotonic
sys.setrecursionlimit(100000)
from z3 import And, parse_smt2_file, is_app, simplify, is_quantifier, Z3_OP_BMUL, is_bv_value, Z3_OP_UNINTERPRETED

import verification.block_equivalence as be


def walk(t):
    seen, work = set(), [t]
    while work:
        x = work.pop()
        if x.get_id() in seen:
            continue
        seen.add(x.get_id())
        yield x
        if is_quantifier(x):
            work.append(x.body())
        elif is_app(x):
            work.extend(x.children())


def mentions(t, name):
    return any(is_app(x) and x.num_args() == 0 and x.decl().name().endswith(name) for x in walk(t))


def nonlinear(t):
    return any(is_app(x) and x.decl().kind() == Z3_OP_BMUL and sum(not is_bv_value(c) for c in x.children()) > 1
               for x in walk(t))


def leaves(t):
    return {x.decl().name() for x in walk(t) if is_app(x) and x.num_args() == 0
            and x.decl().kind() == Z3_OP_UNINTERPRETED}


path, k, tmo, mode = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
f = And(*parse_smt2_file(path))
part = be._goal_split(f)[k]
sk, _ = be.skolemize_array_disequalities(part)
cs = be._conjuncts(sk)
goal = [c for c in cs if mentions(c, "ext_w!0")] or [cs[-1]]
rest = [c for c in cs if not any(c.eq(g) for g in goal)]
if mode == "nogas":
    keep = [c for c in rest if not mentions(c, "gas_remaining")]
elif mode == "nonlin":
    keep = [c for c in rest if not nonlinear(c)]
elif mode == "goalonly":
    gl = set().union(*(leaves(g) for g in goal))
    keep = [c for c in rest if leaves(c) & gl and not mentions(c, "gas_remaining")]
else:
    keep = rest
print(f"goal conjuncts {len(goal)}; premise {len(rest)} -> {len(keep)}", flush=True)
t = monotonic()
print(mode, be.solve_query(simplify(And(*keep, *goal)), tmo), f"{monotonic()-t:.1f}s", flush=True)
