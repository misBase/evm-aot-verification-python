"""joint_norm.py FILE.smt2 : one normalize_word_arith over And(m_k => x_k == y_k) for every differing argument
pair of same-decl UF applications; report which pairs became identities and the time."""
import sys
from time import monotonic
from z3 import *
import verification.block_equivalence as be

F = And(*parse_smt2_file(sys.argv[1]))
F, _ = be.skolemize_array_disequalities(F)
pairs = {}
for apps in be._uf_applications(F):
    for i, first in enumerate(apps):
        for other in apps[i + 1:]:
            for x, y in zip(first.children(), other.children()):
                if not x.eq(y):
                    pairs.setdefault((x.get_id(), y.get_id()), (x, y))
marks = [Bool(f"idm_{n}") for n in range(len(pairs))]
G = And(*(Implies(m, x == y) for m, (x, y) in zip(marks, pairs.values())))
t = monotonic()
N, lem = be.normalize_word_arith(G)
left = set(str(c) for c in be._conjuncts(N) for c in [c])
names = {d.name() for d in [] }
seen, work, live = set(), [N], set()
while work:
    u = work.pop()
    if u.get_id() in seen or not is_app(u):
        continue
    seen.add(u.get_id())
    if u.num_args() == 0 and u.decl().name().startswith("idm_"):
        live.add(u.decl().name())
    work.extend(u.children())
print("pairs", len(pairs), "normalize", f"{monotonic() - t:.1f}s", "lemmas", len(lem), flush=True)
for m, (x, y) in zip(marks, pairs.values()):
    print(" ", m, x.sort(), len(x.sexpr()), len(y.sexpr()), "residual" if str(m) in live else "IDENTITY")
