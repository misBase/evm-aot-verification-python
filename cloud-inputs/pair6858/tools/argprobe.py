"""sha3 arg-0 equality of a pair obligation's memory part under light / full premise.
Usage (repo root, PYTHONPATH=.): argprobe.py FILE.smt2 PART timeout_ms"""
import sys
from time import monotonic
sys.setrecursionlimit(100000)
from z3 import And, parse_smt2_file, simplify, substitute

import verification.block_equivalence as be

path, k, tmo = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
f = And(*parse_smt2_file(path))
part = be._goal_split(f)[k]
sk, _ = be.skolemize_array_disequalities(part)
apps = [a for g in be._uf_applications(sk) for a in g if a.decl().name() == "sha3_slice"]
x, y = apps[0].arg(0), apps[1].arg(0)
parts = [c for c in be._conjuncts(sk) if be._no_binder(c)]
light = [c for c in parts if not be._heavy(c)]
print(len(be._conjuncts(sk)), "conjuncts,", len(parts), "binder-free,", len(light), "light", flush=True)
differ = be._differ(x, y)
opaque = be._uf_app_constants(And(*parts), differ)
hide = (lambda t: substitute(t, *opaque)) if opaque else (lambda t: t)
for label, ps in (("light", light), ("full", parts)):
    q = simplify(And(*(hide(c) for c in ps), hide(differ)))
    t = monotonic()
    print(label, be.solve_query(q, tmo), f"{monotonic() - t:.1f}s", flush=True)
