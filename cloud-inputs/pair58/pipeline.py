"""Manual pipeline on a memory goal part: merge sha3 memory args (lemma under the linear premise),
make sha3 applications opaque, then refute with full / linear-only premise.
Usage (cwd=snapshot, PYTHONPATH=.): pipeline.py FILE.smt2 PART timeout_ms"""
import sys
from time import monotonic
sys.setrecursionlimit(100000)
from z3 import And, parse_smt2_file, simplify, is_app, is_quantifier, Z3_OP_BMUL, is_bv_value, substitute

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


def nonlinear(t):
    return any(is_app(x) and x.decl().kind() == Z3_OP_BMUL and sum(not is_bv_value(c) for c in x.children()) > 1
               for x in walk(t))


path, k, tmo = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
f = And(*parse_smt2_file(path))
part = be._goal_split(f)[k]
sk, _ = be.skolemize_array_disequalities(part)
if len(sys.argv) > 4:
    t = monotonic()
    sk, _rw = be.normalize_word_arith(sk)
    print("normalized", len(_rw), f"{monotonic()-t:.1f}s", flush=True)
apps = [a for g in be._uf_applications(sk) for a in g if a.decl().name() == "sha3_slice"]
merges = []
for x, y in zip(apps[0].children(), apps[1].children()):
    if x.eq(y):
        continue
    lin = [c for c in be._conjuncts(sk) if be._no_binder(c) and not nonlinear(c)]
    t = monotonic()
    a = be.solve_query(simplify(And(*lin, be._differ(x, y))), tmo)
    print("arg lemma (linear premise)", a, f"{monotonic()-t:.1f}s", flush=True)
    if a != "unsat":
        sys.exit(1)
    small, big = sorted((x, y), key=lambda t: len(t.sexpr()))
    merges.append((big, small))
sk = substitute(sk, *merges)
opaque = [(t, c) for t, c in be._uf_app_constants(sk) if any(be._is_array_term(a) for a in t.children())]
print("opaque apps", len(opaque))
q = substitute(sk, *opaque)
from z3 import Const, ArraySort, BitVecSort, Concat, Select, BitVecVal, ULT, UGE
w = next(x for x in walk(q) if is_app(x) and x.num_args() == 0 and x.decl().name().startswith("ext_w"))
mem0 = Const("blk5377_30_None_None_evm_mem0", ArraySort(BitVecSort(64), BitVecSort(8)))
fmp = Concat(*[Select(mem0, BitVecVal(i, 64)) for i in range(88, 96)])
d = w - fmp
lq = And(*[c for c in be._conjuncts(q) if not nonlinear(c)])
for label, c in (("d<256", ULT(d, 256)), ("256<=d<288", And(UGE(d, 256), ULT(d, 288))), ("288<=d<2^63", And(UGE(d, 288), ULT(d, 1 << 63))), ("d>=2^63", UGE(d, 1 << 63))):
    t = monotonic()
    print("linear", label, be.solve_query(simplify(And(lq, c)), tmo), f"{monotonic()-t:.1f}s", flush=True)
for label, query in (("linear premise", And(*[c for c in be._conjuncts(q) if not nonlinear(c)])), ("full", q)):
    t = monotonic()
    print(label, be.solve_query(simplify(query), tmo), f"{monotonic()-t:.1f}s", flush=True)
