"""Shape comparison of two captured pair obligations (repository root, PYTHONPATH=.):
shape.py A.smt2 B.smt2 [--goals] [--dump-only-a] [--dump-only-b]

Prints the goal-split part count, per-part goal size, premise conjunct counts, the
premise conjunct set difference (by sexpr), the sha3_slice applications and the
products in each formula.
"""
import sys

from z3 import And, Z3_OP_BMUL, Z3_OP_UNINTERPRETED, is_app, parse_smt2_file

import verification.block_equivalence as be


def load(path):
    f = And(*parse_smt2_file(path))
    while be.is_and(f) and f.num_args() == 1:
        f = f.arg(0)
    *rest, last = f.children()
    return f, rest, last


def walk(t, seen=None):
    seen = set() if seen is None else seen
    out, work = [], [t]
    while work:
        x = work.pop()
        if x.get_id() in seen:
            continue
        seen.add(x.get_id())
        out.append(x)
        if is_app(x):
            work.extend(x.children())
    return out


def products(t):
    return [x for x in walk(t) if is_app(x) and x.decl().kind() == Z3_OP_BMUL
            and sum(1 for c in x.children() if not be.is_bv_value(c)) >= 2]


def ufs(t, name):
    return [x for x in walk(t) if is_app(x) and x.decl().kind() == Z3_OP_UNINTERPRETED and x.decl().name() == name]


def main():
    pa, pb = sys.argv[1], sys.argv[2]
    fa, ra, ga = load(pa)
    fb, rb, gb = load(pb)
    for tag, f, r, g in (("A", fa, ra, ga), ("B", fb, rb, gb)):
        goals = g.arg(0).children() if be.is_not(g) and be.is_and(g.arg(0)) else [g]
        print(f"{tag}: premise conjuncts {len(r)} (flattened {len(be._conjuncts(And(*r)))}), goal parts {len(goals)}")
        for k, x in enumerate(goals):
            print(f"  part {k}: {len(walk(x))} nodes, sha3 {len(ufs(x, 'sha3_slice'))}, products {len(products(x))}:"
                  f" {x.sexpr()[:160]}")
        print(f"  sha3_slice in premise: {len(ufs(And(*r), 'sha3_slice'))}, products in premise: {len(products(And(*r)))}")
    sa = {c.sexpr(): c for c in be._conjuncts(And(*ra))}
    sb = {c.sexpr(): c for c in be._conjuncts(And(*rb))}
    only_a, only_b = [s for s in sa if s not in sb], [s for s in sb if s not in sa]
    print(f"common {len(set(sa) & set(sb))}, only A {len(only_a)}, only B {len(only_b)}")
    for tag, only, flag in (("A", only_a, "--dump-only-a"), ("B", only_b, "--dump-only-b")):
        for n, s in enumerate(only):
            print(f"--- only {tag} [{n}] ({len(s)} chars)")
            print(s if flag in sys.argv else s[:600])
    if "--goals" in sys.argv:
        goals_a = ga.arg(0).children()
        goals_b = gb.arg(0).children()
        for k, (x, y) in enumerate(zip(goals_a, goals_b)):
            print(f"=== part {k} same={x.eq(y)}")
            if not x.eq(y):
                print("A:", x.sexpr())
                print("B:", y.sexpr())


if __name__ == "__main__":
    main()
