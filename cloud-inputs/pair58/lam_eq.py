"""premise ⊨ L_evm = L_x86 (sha3 memory argument) under several premise reductions.
Usage (cwd=snapshot, PYTHONPATH=.): lam_eq.py FILE.smt2 PART timeout_ms MODES(comma)
MODES: full, mulabs (abstract_nonlinear_mul like the unify route), nogas, nononlin, core"""
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


def mentions(t, name):
    return any(is_app(x) and x.num_args() == 0 and x.decl().name().endswith(name) for x in walk(t))


def nonlinear(t):
    return any(is_app(x) and x.decl().kind() == Z3_OP_BMUL and sum(not is_bv_value(c) for c in x.children()) > 1
               for x in walk(t))


path, k, tmo, modes = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4].split(",")
f = And(*parse_smt2_file(path))
part = be._goal_split(f)[k]
sk, _ = be.skolemize_array_disequalities(part)
for mode in modes:
    base = be.abstract_nonlinear_mul(sk, functions={})[0] if mode == "mulabs" else sk
    apps = [a for g in be._uf_applications(base) for a in g if a.decl().name() == "sha3_slice"]
    x, y = apps[0].arg(0), apps[1].arg(0)
    parts = [c for c in be._conjuncts(base) if be._no_binder(c)]
    if mode == "nogas":
        parts = [c for c in parts if not mentions(c, "gas_remaining")]
    elif mode == "nononlin":
        parts = [c for c in parts if not nonlinear(c)]
    d = be._differ(x, y)
    opaque = be._uf_app_constants(And(*parts), d)
    hide = (lambda t: substitute(t, *opaque)) if opaque else (lambda t: t)
    t = monotonic()
    if mode == "core":
        core = be.unsat_core([hide(c) for c in parts], hide(d), tmo)
        print(mode, "core", None if core is None else len(core), f"{monotonic()-t:.1f}s", flush=True)
        if core:
            for i in core:
                print("   ", " ".join(str(parts[i]).replace("blk5377_30_None_None_", "").split())[:250])
        continue
    print(mode, len(parts), "premise conjuncts:", be.solve_query(simplify(And(hide(And(*parts)), hide(d))), tmo),
          f"{monotonic()-t:.1f}s", flush=True)
