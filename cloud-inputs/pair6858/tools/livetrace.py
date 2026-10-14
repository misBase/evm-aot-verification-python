"""route_trace.py with live logging of every array-argument _prove_equal (route, cache use, result).
Usage (repo root, PYTHONPATH=.): livetrace.py OUT.json FILE.smt2 [--seconds N] [--sequence ...] (as route_trace)"""
import sys
from time import monotonic
sys.path.insert(0, "cloud-inputs/tools")
sys.setrecursionlimit(100000)

import route_trace as rt
import verification.block_equivalence as be

T0 = monotonic()
real_pe = be._prove_equal


def prove_equal(premise, x, y, budget_ms, deadline, cache=None):
    if not be._is_array_term(x):
        return real_pe(premise, x, y, budget_ms, deadline, cache)
    route = rt.STACK[-1].route if rt.STACK else "-"
    name = rt.STACK[-1].name if rt.STACK else "-"
    key = tuple(sorted((x.get_id(), y.get_id())))
    ids = frozenset(c.get_id() for c in be._conjuncts(premise))
    hits = [("proof" if p is not None else "fail", len(u), u <= ids if p is not None else ids <= u)
            for u, p, _ in (cache or {}).get(key, ())]
    t = monotonic()
    r = real_pe(premise, x, y, budget_ms, deadline, cache)
    print(f"[{monotonic() - T0:7.1f}] {name} @{route} array _prove_equal caller={sys._getframe(1).f_code.co_name} "
          f"conj={len(ids)} cached={hits} -> {'proved' if r is not None else None} {monotonic() - t:.2f}s",
          flush=True)
    return r


be._prove_equal = prove_equal
real_light = be._refute_over_light_premise


def light(parts, goal, budget_ms):
    t = monotonic()
    r = real_light(parts, goal, budget_ms)
    if budget_ms > 2000 or monotonic() - t > 1.5:
        caller = sys._getframe(2).f_code.co_name
        print(f"[{monotonic() - T0:7.1f}]   light caller={caller} budget={budget_ms} -> {r is not None} "
              f"{monotonic() - t:.2f}s", flush=True)
    return r


be._refute_over_light_premise = light
rt.main()
