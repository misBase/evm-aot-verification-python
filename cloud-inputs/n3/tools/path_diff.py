"""Compare two dumped path conditions conjunct by conjunct (dump_paths.py output).

Usage (repo root, PYTHONPATH=.): path_diff.py DUMPDIR A B [--x86 J]
A, B: names like evm_63 / evm_93 / x86_2. Prints the conjuncts only in A, only in B (simplified,
truncated), and with --x86 J whether premise ∧ x86_J ∧ (each A-only conjunct) is decided quickly.
Diagnostics only.
"""
import sys

from z3 import And, Not, parse_smt2_file, simplify

import verification.block_equivalence as be

argv = sys.argv[1:]
d, a, b = argv[0], argv[1], argv[2]


def conj(name):
    return be._conjuncts(And(*parse_smt2_file(f"{d}/{name}.smt2")))


A, B = conj(a), conj(b)
ida, idb = {c.get_id() for c in A}, {c.get_id() for c in B}
print(f"{a}: {len(A)} conjuncts, {b}: {len(B)}, shared {len(ida & idb)}")
for name, cs, other in ((a, A, idb), (b, B, ida)):
    for k, c in enumerate(cs):
        if c.get_id() not in other:
            print(f"only {name}[{k}] ({len(c.sexpr())} chars):", " ".join(simplify(c).sexpr().split())[:400])
if "--x86" in argv:
    j = argv[argv.index("--x86") + 1]
    premise = And(*parse_smt2_file(f"{d}/premise.smt2"))
    x = And(*parse_smt2_file(f"{d}/x86_{j}.smt2"))
    for k, c in enumerate(A):
        if c.get_id() not in idb:
            print(f"premise ∧ x86_{j} ∧ {a}[{k}]:", be.solve_query(simplify(And(premise, x, c)), 10000),
                  "| with negation:", be.solve_query(simplify(And(premise, x, Not(c))), 10000), flush=True)
