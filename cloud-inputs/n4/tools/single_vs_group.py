"""Why a conjunct alone is hard but its row group is easy (diagnostics only: nothing here is a proof).

Usage (repo root, PYTHONPATH=.): single_vs_group.py DUMP_DIR ROW K [--others N] [--seconds S]

Builds x86_maps_ROW_K (premise ∧ x_j ∧ ¬c_K) and the group with N other conjuncts of the row
(default: all), as _check_rows / _prove_row_groups build them; for each: normalize_word_arith
(rewrites, time), then the blasted normalised query with --seconds (default 300), and the
blasted plain query. --single: only the single conjunct; --norm-only: only blast+norm.
"""
import json
import sys
import time
from pathlib import Path

from z3 import And, Not, parse_smt2_file, simplify

import verification.block_equivalence as be

argv = sys.argv[1:]


def opt(flag, default=None):
    return argv[argv.index(flag) + 1] if flag in argv else default


d, j, k = Path(argv[0]), int(argv[1]), int(argv[2])
seconds = float(opt("--seconds", 300))
meta = json.loads((d / "meta.json").read_text())
premise = And(*parse_smt2_file(str(d / "premise.smt2")))
x = And(*parse_smt2_file(str(d / f"x86_{j}.smt2")))
conj = be._conjuncts(And(*parse_smt2_file(str(d / f"evm_{meta['proposed'][j]}.smt2"))))
others = [i for i in range(len(conj)) if i != k]
if opt("--others") is not None:
    others = others[:int(opt("--others"))]
T0 = time.monotonic()


def log(*a):
    print(f"[{time.monotonic() - T0:8.1f}s]", *a, flush=True)


cases = (("single", conj[k]), (f"group+{len(others)}", And(conj[k], *(conj[i] for i in others))))
if "--single" in argv:
    cases = cases[:1]
for label, goal in cases:
    forwarded, canon = {}, {}
    f = be.canon_binders(be.forward_selects(And(premise, x, Not(goal)), forwarded), canon)
    f, _ = be.skolemize_array_disequalities(f)
    started = time.monotonic()
    normalized, rewrites = be.normalize_word_arith(f)
    log(label, f"normalize: {len(rewrites)} rewrites {time.monotonic() - started:.1f}s",
        "unchanged" if normalized.eq(simplify(f, bv_sort_ac=True)) else "changed")
    for name, target in (("blast+norm", normalized), ("blast", f))[:1 if "--norm-only" in argv else 2]:
        started = time.monotonic()
        answer = be.solve_query(simplify(target, blast_select_store=True), int(seconds * 1000))
        log(label, name, answer, f"{time.monotonic() - started:.1f}s")
