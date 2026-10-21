"""Last conjunct of each "all" x86 row of a dump_paths.py directory, with big memory reads named.

Usage (repo root, PYTHONPATH=.): row_tails.py DUMP_DIR [J ...]   (default: every "all" row of meta.json)
Shows what the row's final branch checked (e.g. a cost overflow) and the row's kind/location.
"""
import json
import sys
from pathlib import Path

from z3 import And, Const, Z3_OP_UNINTERPRETED, is_app, is_select, parse_smt2_file, substitute

import verification.block_equivalence as be

d = Path(sys.argv[1])
meta = json.loads((d / "meta.json").read_text())
rows = [int(j) for j in sys.argv[2:]] or [j for j, t in enumerate(meta["found"]) if t == "all"]


def named(t):
    subs, seen, work, sizes = {}, set(), [t], {}
    while work:
        u = work.pop()
        if u.get_id() in seen or not is_app(u):
            continue
        seen.add(u.get_id())
        big = len(u.sexpr()) > 300
        if big and (is_select(u) or (u.decl().kind() == Z3_OP_UNINTERPRETED and u.num_args() > 0)):
            subs[u.get_id()] = (u, Const(f"m{len(subs)}", u.sort()))
            continue
        work.extend(u.children())
    return substitute(t, *subs.values()) if subs else t


for j in rows:
    conj = be._conjuncts(And(*parse_smt2_file(str(d / f"x86_{j}.smt2"))))
    # the row's own last branch: the first conjunct (path conditions are stored newest-first
    # after flattening) -- print both ends.
    for label, c in (("first", conj[0]), ("last", conj[-1])):
        text = " ".join(str(named(c)).split())
        print(f"row {j} {meta['x86'][j]['kind']}@{meta['x86'][j]['location']} {label}: {text[:300]}")
