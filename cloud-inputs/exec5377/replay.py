"""Replay recorded reachability queries under a strategy.

usage: replay.py DIR VARIANT [FILTER] [LIMIT]    (cwd = snapshot, PYTHONPATH=.)
  FILTER: all | solved (calls that reached a solver, default) | slow (t >= 0.2s in the record)
Writes DIR/replay_VARIANT.jsonl (index, decision, seconds, detail) and prints totals.
Decision: False = pruned (UNSAT proved), True = kept.
"""
import json
import sys
from pathlib import Path
from time import monotonic

from z3 import And, SolverFor, is_true, parse_smt2_file, sat, unsat

sys.path.insert(0, str(Path(__file__).parent))
from x86_64.cfg_state import _bounded_check
from verification.block_equivalence import abstract_nonlinear_mul

d, variant = Path(sys.argv[1]), sys.argv[2]
flt = sys.argv[3] if len(sys.argv) > 3 else "solved"
limit = int(sys.argv[4]) if len(sys.argv) > 4 else None
TMO = 1000

t = monotonic()
TABLE = list(parse_smt2_file(str(d / "table.smt2")))
print("table", len(TABLE), f"{monotonic() - t:.1f}s", flush=True)
rows = [json.loads(l) for l in open(d / "calls.jsonl")]
sel = []
for i, r in enumerate(rows):
    if "c" not in r:
        continue
    if flt == "solved" and r.get("w"):
        continue
    if flt == "slow" and (r.get("w") or r["t"] < 0.2):
        continue
    sel.append(i)
sel = sel[:limit] if limit else sel


def conjuncts(r):
    return [TABLE[k] for k in r["c"]] + [TABLE[k] for k in r["f"]]


def fresh_check(fs, tag):
    s = SolverFor("QF_AUFBV")
    s.add(*fs)
    return _bounded_check(s, TMO, tag), s


def v_base(r, info):
    fs = conjuncts(r)
    relaxed, changed = abstract_nonlinear_mul(And(*fs))
    if changed:
        res, _ = fresh_check([relaxed], "probe")
        info["probe"] = str(res)
        if res == unsat:
            return False
    res, _ = fresh_check(fs, "exact")
    info["exact"] = str(res)
    return res != unsat


def v_exact(r, info):
    res, _ = fresh_check(conjuncts(r), "exact")
    info["exact"] = str(res)
    return res != unsat


def v_probe(r, info):
    relaxed, changed = abstract_nonlinear_mul(And(*conjuncts(r)))
    if not changed:
        info["unchanged"] = 1
        return True
    res, _ = fresh_check([relaxed], "probe")
    info["probe"] = str(res)
    return res != unsat


# Incremental: one solver, push/pop along the longest common conjunct prefix.
INC = {"solver": None, "stack": []}


def v_incremental(r, info):
    keys = r["c"] + [("f", k) for k in r["f"]]
    if INC["solver"] is None:
        INC["solver"] = SolverFor("QF_AUFBV")
    s, stack = INC["solver"], INC["stack"]
    common = 0
    while common < min(len(stack), len(keys)) and stack[common] == keys[common]:
        common += 1
    while len(stack) > common:
        s.pop()
        stack.pop()
    for k in keys[common:]:
        s.push()
        s.add(TABLE[k] if not isinstance(k, tuple) else TABLE[k[1]])
        stack.append(k)
    info["reuse"] = common
    res = _bounded_check(s, TMO, "inc")
    info["exact"] = str(res)
    return res != unsat


# Model pool: try the last K sat models before solving (a model is a sat witness).
POOL = []


def v_pool(r, info):
    fs = And(*conjuncts(r))
    for m in reversed(POOL[-64:]):
        if is_true(m.eval(fs, model_completion=True)):
            info["pool"] = 1
            return True
    relaxed, changed = abstract_nonlinear_mul(fs)
    if changed:
        res, _ = fresh_check([relaxed], "probe")
        info["probe"] = str(res)
        if res == unsat:
            return False
    res, s = fresh_check(conjuncts(r), "exact")
    info["exact"] = str(res)
    if res == sat:
        POOL.append(s.model())
    return res != unsat


def _symbols(e, memo):
    """Uninterpreted constants under e (z3 ids), memoized per AST id."""
    from z3 import is_const, is_app, Z3_OP_UNINTERPRETED
    k = e.get_id()
    if k in memo:
        return memo[k]
    out, todo, seen = set(), [e], set()
    while todo:
        x = todo.pop()
        if x.get_id() in seen:
            continue
        seen.add(x.get_id())
        if is_app(x) and x.decl().kind() == Z3_OP_UNINTERPRETED:
            out.add(x.decl().name())
        todo.extend(x.children())
    memo[k] = frozenset(out)
    return memo[k]


SYM = {}


def v_slice(r, info):
    """Independence slicing (KLEE): the last conjunct's connected component only.
    UNSAT of a sub-conjunction is UNSAT of the whole; otherwise fall back to base."""
    fs = conjuncts(r)
    syms = [_symbols(f, SYM) for f in fs]
    comp = set(syms[-1])
    chosen = {len(fs) - 1}
    changed = True
    while changed:
        changed = False
        for n, s in enumerate(syms):
            if n not in chosen and s & comp:
                chosen.add(n)
                comp |= s
                changed = True
    info["slice"] = [len(chosen), len(fs)]
    if len(chosen) < len(fs):
        sub = [fs[n] for n in sorted(chosen)]
        res, _ = fresh_check(sub, "slice")
        info["sres"] = str(res)
        if res == unsat:
            return False
    return v_base(r, info)


ANC = {}


def _ancestor_model(keys):
    for L in range(len(keys) - 1, 0, -1):
        m = ANC.get(tuple(keys[:L]))
        if m is not None:
            return m
    return None


def v_pin(r, info):
    """probe (mul->UF) for UNSAT; then a SAT under-approximation: pin the constants under
    nonlinear products to the ancestor's model (any model of F /\\ pins is a model of F);
    then the exact query."""
    from verification.block_equivalence import _nonlinear_mul_terms
    from z3 import simplify as simp, is_const, Z3_OP_UNINTERPRETED
    keys = r["c"] + [("f", k) for k in r["f"]]
    fs = conjuncts(r)
    whole = And(*fs)
    relaxed, changed = abstract_nonlinear_mul(whole)
    if changed:
        res, _ = fresh_check([relaxed], "probe")
        info["probe"] = str(res)
        if res == unsat:
            return False
        m = _ancestor_model(keys)
        if m is not None:
            consts = {}
            for term in _nonlinear_mul_terms(simp(whole)):
                for a in term.children():
                    todo = [a]
                    while todo:
                        x = todo.pop()
                        if is_const(x) and x.decl().kind() == Z3_OP_UNINTERPRETED:
                            consts[x.get_id()] = x
                        todo.extend(x.children())
            pins = [c == m.eval(c, model_completion=True) for c in consts.values()]
            info["pins"] = len(pins)
            s = SolverFor("QF_AUFBV")
            s.add(*fs)
            s.add(*pins)
            pres = _bounded_check(s, TMO, "pin")
            info["pin"] = str(pres)
            if pres == sat:
                ANC[tuple(keys)] = s.model()
                return True
    res, s = fresh_check(fs, "exact")
    info["exact"] = str(res)
    if res == sat:
        ANC[tuple(keys)] = s.model()
    return res != unsat


def v_incprobe(r, info):
    """incremental exact first; only an unknown pays for the mul->UF probe (fresh solver)."""
    if not v_incremental(r, info):
        return False
    if info["exact"] == "unknown":
        relaxed, changed = abstract_nonlinear_mul(And(*conjuncts(r)))
        if changed:
            res, _ = fresh_check([relaxed], "probe")
            info["probe"] = str(res)
            return res != unsat
    return True


PROBE2 = {"ps": None}


def v_incprobe2(r, info):
    import reach_modes
    if not v_incremental(r, info):
        return False
    if info["exact"] != "unknown":
        return True
    if PROBE2["ps"] is None:
        PROBE2["ps"] = reach_modes.PrefixSolver()
    fs = conjuncts(r)
    relaxed = [reach_modes._abstract_conjunct(c) for c in fs]
    if any(not a.eq(b) for a, b in zip(relaxed, fs)):
        res = PROBE2["ps"].check(relaxed, TMO, {})
        info["probe"] = str(res)
        return res != unsat
    return True


def _mul_arg_consts(whole):
    from verification.block_equivalence import _nonlinear_mul_terms
    from z3 import simplify as simp, is_const, Z3_OP_UNINTERPRETED
    consts = {}
    for term in _nonlinear_mul_terms(simp(whole)):
        todo = list(term.children())
        while todo:
            x = todo.pop()
            if is_const(x) and x.decl().kind() == Z3_OP_UNINTERPRETED:
                consts[x.get_id()] = x
            todo.extend(x.children())
    return list(consts.values())


def v_pinprobe(r, info):
    """probe for UNSAT; on probe SAT pin the product operands' constants to the PROBE's model."""
    fs = conjuncts(r)
    whole = And(*fs)
    relaxed, changed = abstract_nonlinear_mul(whole)
    if changed:
        probe = SolverFor("QF_AUFBV")
        probe.add(relaxed)
        res = _bounded_check(probe, TMO, "probe")
        info["probe"] = str(res)
        if res == unsat:
            return False
        if res == sat:
            m = probe.model()
            consts = _mul_arg_consts(whole)
            s = SolverFor("QF_AUFBV")
            s.add(*fs)
            s.add(*[c == m.eval(c, model_completion=True) for c in consts])
            pres = _bounded_check(s, TMO, "pin")
            info["pin"] = str(pres)
            if pres == sat:
                return True
    res, s = fresh_check(fs, "exact")
    info["exact"] = str(res)
    return res != unsat


VARIANTS = {"incprobe2": v_incprobe2, "incprobe": v_incprobe, "pinprobe": v_pinprobe, "pin": v_pin, "slice": v_slice,"base": v_base, "exact": v_exact, "probe": v_probe, "incremental": v_incremental, "pool": v_pool}
fn = VARIANTS[variant]
out = open(d / f"replay_{variant}_{flt}.jsonl", "w")
total, flips = 0.0, 0
for i in sel:
    r = rows[i]
    info = {"i": i}
    t = monotonic()
    dec = fn(r, info)
    dt = monotonic() - t
    total += dt
    info.update(dec=dec, t=round(dt, 4), rec=r["r"])
    if dec != r["r"]:
        flips += 1
    out.write(json.dumps(info) + "\n")
    out.flush()
print(variant, flt, "n", len(sel), "total", round(total, 1), "flips", flips, flush=True)
