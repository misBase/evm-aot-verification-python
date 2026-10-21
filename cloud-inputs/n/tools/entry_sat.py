"""Decide a captured summary-hit premise (x86_profile.py rejected_entry_*.smt2) several ways.

Usage (repo root, PYTHONPATH=.): entry_sat.py FILE.smt2 [--ms N]
Prints each strategy's answer and time: the direct query (as VerifiedSummaryRuntime._solve),
the constant-UF witness tiers (sat_by_constant_array_ufs), and the UF inventory.
Diagnostics only.
"""
import sys
from time import monotonic

from z3 import And, parse_smt2_file, simplify

import verification.block_equivalence as be

argv = sys.argv[1:]
ms = int(argv[argv.index("--ms") + 1]) if "--ms" in argv else 30000
premise = And(*parse_smt2_file(argv[0]))
print("size", len(premise.sexpr()), "ufs", sorted({a.decl().name() for apps in be._uf_applications(premise) for a in apps}),
      "tiers", [len(t) for t in be._witness_tiers(premise)], flush=True)
for name, run in (("direct", lambda: be.solve_query(simplify(premise, expand_select_store=True), ms)),
                  ("constant-ufs", lambda: be.sat_by_constant_array_ufs(premise, ms))):
    started = monotonic()
    print(name, run(), f"{monotonic() - started:.1f}s", flush=True)
