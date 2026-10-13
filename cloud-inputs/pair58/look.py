"""Print goal2's array sides as a let-style DAG listing. Diagnostic.

Usage: tmp_g2_look.py GOAL.smt2 [MIN_SIZE]
"""
import sys
sys.setrecursionlimit(100000)

from z3 import is_and, Z3_ARRAY_SORT, And, is_eq, is_not, is_quantifier, is_app, is_var, parse_smt2_file, get_var_index

import verification.block_equivalence as be


def listing(roots, min_size):
    names, sizes, lines = {}, {}, []

    def size(t):
        k = t.get_id()
        if k not in sizes:
            if is_quantifier(t):
                sizes[k] = 1 + size(t.body())
            elif is_app(t):
                sizes[k] = 1 + sum(size(c) for c in t.children())
            else:
                sizes[k] = 1
        return sizes[k]

    def text(t):
        k = t.get_id()
        if k in names:
            return names[k]
        if is_var(t):
            return f"#{get_var_index(t)}"
        if is_quantifier(t):
            s = f"(lambda {t.var_name(0)} {text(t.body())})"
        elif is_app(t) and t.num_args() > 0:
            d = t.decl().name()
            p = t.params()
            if p:
                d = f"({d} {' '.join(map(str, p))})"
            s = f"({d} {' '.join(text(c) for c in t.children())})"
        else:
            s = str(t).replace("blk5377_30_None_None_", "")
        if size(t) >= min_size:
            names[k] = f"t{len(names)}"
            lines.append(f"{names[k]} [{size(t)}] = {s}")
            return names[k]
        return s

    for r in roots:
        print("ROOT", text(r))
    for line in lines:
        print(line[:1500])


def main():
    f = And(*parse_smt2_file(sys.argv[1]))
    min_size = int(sys.argv[2]) if len(sys.argv) > 2 else 40
    k = int(sys.argv[3])
    while is_and(f) and f.num_args() == 1:
        f = f.arg(0)
    g = f.children()[-1].arg(0).arg(k)
    listing(g.children(), min_size)


if __name__ == "__main__":
    main()
