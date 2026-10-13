"""Split the skolemized memory part by the witness offset d = w - fmp and solve each case.
Usage (cwd=snapshot, PYTHONPATH=.): region.py FILE.smt2 PART timeout_ms [norm]"""
import sys
from time import monotonic
sys.setrecursionlimit(100000)
from z3 import (And, parse_smt2_file, is_app, Concat, Select, BitVecVal, ULT, UGE, simplify, Const, BitVecSort,
                ArraySort)

import verification.block_equivalence as be

path, k, tmo = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
norm = len(sys.argv) > 4
f = And(*parse_smt2_file(path))
part = be._goal_split(f)[k]
sk, _ = be.skolemize_array_disequalities(part)
if norm:
    sk, _ = be.normalize_word_arith(sk)


def consts(t):
    seen, work, out = set(), [t], {}
    while work:
        x = work.pop()
        if x.get_id() in seen:
            continue
        seen.add(x.get_id())
        if hasattr(x, "body") and not is_app(x):
            work.append(x.body())
            continue
        if is_app(x):
            if x.num_args() == 0 and x.decl().name().startswith("ext_w"):
                out[x.decl().name()] = x
            work.extend(x.children())
    return out


ws = consts(sk)
print("witnesses", list(ws))
w = list(ws.values())[0]
mem0 = Const("blk5377_30_None_None_evm_mem0", ArraySort(BitVecSort(64), BitVecSort(8)))
fmp = Concat(*[Select(mem0, BitVecVal(i, 64)) for i in range(88, 96)])
d = w - fmp
cases = [("d<256", ULT(d, 256)), ("256<=d<288", And(UGE(d, 256), ULT(d, 288))), ("288<=d<2^63", And(UGE(d, 288), ULT(d, 1 << 63))),
         ("d>=2^63", UGE(d, 1 << 63))]
only = sys.argv[5].split(",") if len(sys.argv) > 5 else None
for name, c in cases:
    if only and name not in only:
        continue
    t = monotonic()
    print(name, be.solve_query(simplify(And(sk, c)), tmo), f"{monotonic()-t:.1f}s", flush=True)
