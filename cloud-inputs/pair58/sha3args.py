"""The two sha3_slice applications of a memory goal part: print args, try premise ⊨ args equal.
Usage (cwd=snapshot, PYTHONPATH=.): sha3args.py FILE.smt2 PART timeout_ms [dump]"""
import sys
from time import monotonic
sys.setrecursionlimit(100000)
from z3 import And, parse_smt2_file, simplify, substitute, Select, FreshConst

import verification.block_equivalence as be

path, k, tmo = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
f = And(*parse_smt2_file(path))
part = be._goal_split(f)[k]
sk, _ = be.skolemize_array_disequalities(part)
apps = [a for g in be._uf_applications(sk) for a in g if a.decl().name() == "sha3_slice"]
print(len(apps), "sha3_slice apps")
for a in apps:
    print("  args:", [" ".join(str(c).replace("blk5377_30_None_None_", "").split())[:300] for c in a.children()])
premise = And(*(c for c in be._conjuncts(sk) if be._no_binder(c)))
x, y = apps[0], apps[1]
for n, (u, v) in enumerate(zip(x.children(), y.children())):
    if u.eq(v):
        print(f"arg {n}: identical")
        continue
    t = monotonic()
    d = be._differ(u, v)
    q = simplify(And(premise, d))
    if len(sys.argv) > 4:
        open(f"sha3arg{n}.smt2", "w").write(be._to_smt2(q))
    t2 = monotonic()
    print(f"arg {n}: no premise", be.solve_query(simplify(d), tmo), f"{monotonic()-t2:.1f}s", flush=True)
    print("BODY0", simplify(u.body()).sexpr().replace("blk5377_30_None_None_", ""))
    print("BODY1", simplify(v.body()).sexpr().replace("blk5377_30_None_None_", ""))
    t = monotonic()
    print(f"arg {n}: direct", be.solve_query(q, tmo), f"{monotonic()-t:.1f}s", flush=True)
