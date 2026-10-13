"""Route profile of the production `_check` on captured SMT2 obligations.

Usage (repository root, PYTHONPATH=.): route_trace.py OUT.json FILE.smt2 [--seconds N]

Like check_obligation.py (30s per query, 1800s per obligation) but `_check`
is re-compiled from its own source with timing marks inserted between its
stages, so the logic is the code under test. Every `_check` frame (the
obligation and each goal-split part) records
  [label, answer, seconds]
for: quick0 (first exact probe), pin (pin_split), lia, normalize, each route
("blast*" = route on the normalised formula), skip:<route> (nothing rewritten),
tail (pending potential resume + direct query). Light-premise probes
(_refute_over_light_premise), unsat_core probes and _refute_by_cases calls are
counted with their hit/miss time per caller.
"""
import inspect
import json
import sys
import textwrap
from time import monotonic

from z3 import And, parse_smt2_file

import verification.block_equivalence as be

FRAMES, STACK = [], []
PROBES = {}


class Frame:
    def __init__(self, name):
        self.name, self.marks, self.last, self.route = name, [], monotonic(), "pre"
        FRAMES.append(self)

    def mark(self, label, answer=None):
        now = monotonic()
        self.marks.append([label, answer, round(now - self.last, 2)])
        self.last = now


def _probe(kind, fn):
    def wrapped(*args, **kwargs):
        started = monotonic()
        result = fn(*args, **kwargs)
        caller = sys._getframe(1).f_code.co_name
        hit = result is not None
        route = STACK[-1].route if STACK else "-"
        entry = PROBES.setdefault(f"{kind}<{caller}@{route}", {"hit": 0, "miss": 0, "hit_s": 0.0, "miss_s": 0.0})
        entry["hit" if hit else "miss"] += 1
        entry["hit_s" if hit else "miss_s"] += monotonic() - started
        return result
    return wrapped


def _instrumented_check():
    src = textwrap.dedent(inspect.getsource(be.BlockEquivalenceProver._check))
    lines = src.split("\n")

    def insert(anchor, code, after=True, occurrence=0, up=0):
        hits = [i for i, l in enumerate(lines) if anchor in l]
        i = hits[occurrence] - up
        indent = lines[i][:len(lines[i]) - len(lines[i].lstrip())]
        if after and lines[i].rstrip().endswith(":"):
            indent += "    "
        lines.insert(i + 1 if after else i, indent + code)

    insert("started = monotonic()", "_tr = _Frame(name); _STACK.append(_tr)")
    insert("answer = solve_query(simplify(formula), min(timeout, _QUICK_EXACT_MS))", "_tr.mark('quick0', answer)")
    if any("proved, answer, lemmas = self._retry_over_lia(formula)" in l for l in lines):  # LIA before the route loop
        insert("proved, answer, lemmas = self._retry_over_lia(formula)", "_tr.mark('pin', answer)", after=False, up=1)
        insert("proved, answer, lemmas = self._retry_over_lia(formula)", "_tr.mark('lia', answer)")
    else:  # LIA is a route of the loop (marked there)
        insert("# Same routes either way", "_tr.mark('pin', answer)", after=False, up=1)
    insert("for index, (route, norm) in enumerate(routes):", "_tr.mark('gap'); _tr.route = route + ('*' if norm else '')")
    insert("continue  # nothing rewritten", "_tr.mark('skip:' + route)", after=False)
    insert("ours = self._potential_pending", "_tr.mark(route + ('*' if norm else ''), answer)", after=False)
    insert("record = Obligation(name, proved.sexpr(), answer, expected, monotonic() - started,",
           "_tr.mark('split' if parts is not None else 'tail', answer)", after=False, occurrence=0)
    insert("record = Obligation(name, proved.sexpr(), answer, expected, monotonic() - started,",
           "_tr.mark('tail', answer)", after=False, occurrence=1)
    src = "\n".join(lines)
    # Each mark is unconditional bookkeeping: no route, budget or answer changes.
    g = dict(be.__dict__)
    real_norm = be.normalize_word_arith

    def normalize(*args, **kwargs):
        STACK[-1].mark("pre-normalize")
        result = real_norm(*args, **kwargs)
        STACK[-1].mark("normalize")
        return result
    g.update(_Frame=Frame, _STACK=STACK, normalize_word_arith=normalize)
    exec(compile(src, "<_check traced>", "exec"), g)
    fn = g["_check"]

    def check(self, *args, **kwargs):
        depth = len(STACK)
        try:
            return fn(self, *args, **kwargs)
        finally:
            del STACK[depth:]
    return check


def main():
    out, path = sys.argv[1], sys.argv[2]
    seconds = float(sys.argv[sys.argv.index("--seconds") + 1]) if "--seconds" in sys.argv else 1800
    be.BlockEquivalenceProver._check = _instrumented_check()
    be._refute_over_light_premise = _probe("light", be._refute_over_light_premise)
    be.unsat_core = _probe("unsat_core", be.unsat_core)
    be._refute_by_cases = _probe("cases", be._refute_by_cases)
    prover = be.BlockEquivalenceProver([], [], {}, timeout_ms=30000)
    prover.deadline = monotonic() + seconds
    records, started = [], monotonic()
    name = path.rsplit("/", 1)[-1]
    try:
        ok = prover._check(name, And(*parse_smt2_file(path)), records)
        answer = "proved" if ok else records[-1].answer
    except be.ProofBudgetExceeded:
        answer = "budget"
    total = monotonic() - started
    print(name, answer, f"{total:.1f}s", flush=True)
    with open(out, "w") as handle:
        json.dump({"name": name, "answer": answer, "seconds": round(total, 1),
                   "frames": [{"name": f.name, "marks": f.marks} for f in FRAMES],
                   "probes": {k: {kk: round(vv, 2) for kk, vv in v.items()} for k, v in PROBES.items()}},
                  handle, indent=1)


if __name__ == "__main__":
    main()
