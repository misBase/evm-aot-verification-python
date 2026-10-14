"""dag_conj.py FILE.smt2 SUBSTRING: print, as a DAG, every top-level conjunct whose
sexpr contains SUBSTRING (PYTHONPATH=.)."""
import sys

from z3 import And, is_app, is_quantifier, is_var, parse_smt2_file

import verification.block_equivalence as be


def show_dag(goal):
    counts = {}

    def count(t):
        counts[t.get_id()] = counts.get(t.get_id(), 0) + 1
        if counts[t.get_id()] > 1:
            return
        if is_quantifier(t):
            count(t.body())
        elif is_app(t):
            for c in t.children():
                count(c)
    count(goal)
    names, lines = {}, []

    def show(t):
        if t.get_id() in names:
            return names[t.get_id()]
        if is_var(t) or (is_app(t) and t.num_args() == 0):
            return t.sexpr()
        if is_quantifier(t):
            s = f"(lambda[{t.num_vars()}] {show(t.body())})"
        else:
            d = t.decl()
            params = d.params()
            head = d.name() + (("[" + ",".join(str(p) for p in params) + "]") if params else "")
            s = "(" + " ".join([head] + [show(c) for c in t.children()]) + ")"
        if counts[t.get_id()] > 1 or len(s) > 200:
            n = f"#{len(names)}"
            names[t.get_id()] = n
            lines.append(f"{n} = {s}")
            return n
        return s
    top = show(goal)
    return lines + [f"TOP = {top}"]


def main():
    sys.setrecursionlimit(100000)
    f = And(*parse_smt2_file(sys.argv[1]))
    for c in be._conjuncts(f):
        if sys.argv[2] in c.sexpr():
            print("\n".join(show_dag(c)))
            print("=" * 40)


if __name__ == "__main__":
    main()
