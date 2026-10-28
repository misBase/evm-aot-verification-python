"""Experiment (diagnostics only): fix 9's guard route with guards also taken from ite conditions
inside the arguments of multiply-applied UFs (a merged diamond, fix 18, turns x86's sign-branch
tree of holiman_udiv applications into one application over ite(T, -a, a) arguments).

Usage (repo root, PYTHONPATH=.): arg_guards.py GOAL.smt2 [--seconds N] [--baseline]
--baseline: production uf_guards (no change). Prints the guards and the traced _check routes.
"""
import sys
import time

from z3 import And, Z3_OP_ITE, Z3_OP_UNINTERPRETED, is_app, is_false, is_true, parse_smt2_file, simplify

import verification.block_equivalence as be

argv = sys.argv[1:]
path = argv[0]
seconds = float(argv[argv.index("--seconds") + 1]) if "--seconds" in argv else 1800
original = be.uf_guards


def uf_guards(formula):
    out = original(formula)
    multi = {apps[0].decl().get_id() for apps in be._uf_applications(formula)}
    known = {raws[0].get_id() for raws in out}
    groups, seen, work = {}, set(), []
    for apps in be._uf_applications(formula):
        for app in apps:
            work.extend(app.children())
    while work:
        t = work.pop()
        if t.get_id() in seen or not is_app(t):
            continue
        seen.add(t.get_id())
        if t.decl().kind() == Z3_OP_ITE and be._no_binder(t.arg(0)):
            c = simplify(t.arg(0))
            if not (is_true(c) or is_false(c)):
                groups.setdefault(c.get_id(), (c, {}))[1].setdefault(t.arg(0).get_id(), t.arg(0))
        if not (t.decl().kind() == Z3_OP_UNINTERPRETED and t.decl().get_id() in multi):
            work.extend(t.children())
    extra = [list(raws.values()) for c, raws in sorted(groups.values(), key=lambda g: be._text_size(g[0]))
             if not any(r.get_id() in known for r in raws.values())]
    return sorted(out + extra, key=lambda raws: be._text_size(simplify(raws[0])))


if "--baseline" not in argv:
    be.uf_guards = uf_guards
formula = And(*parse_smt2_file(path))
print("guards:", [(len(g), be._text_size(simplify(g[0]))) for g in be.uf_guards(formula)][:12], flush=True)
T0 = time.monotonic()
for n in ("_retry_over_guard_cases", "_retry_with_uf_unification", "_retry_over_potential"):
    orig = getattr(be.BlockEquivalenceProver, n)

    def run(self, *a, _orig=orig, _n=n, **k):
        started = time.monotonic()
        out = _orig(self, *a, **k)
        print(f"[{time.monotonic() - T0:8.1f}s]   {_n} -> {out[1]} {time.monotonic() - started:.1f}s", flush=True)
        return out
    setattr(be.BlockEquivalenceProver, n, run)
prover = be.BlockEquivalenceProver([], [], {}, timeout_ms=30000)
prover.deadline = time.monotonic() + seconds
records = []
try:
    ok = prover._check("pair_goal_2_of_7", formula, records, split=False)
    answer = "proved" if ok else records[-1].answer
except be.ProofBudgetExceeded:
    answer = "budget"
print("result", answer, f"{time.monotonic() - T0:.1f}s",
      {f"{r}{'+n' if n else ''}": (w, round(t, 1)) for c in prover._route_stats.values() for (r, n), (w, t) in c.items()},
      flush=True)
