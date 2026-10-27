"""Production _correspondence on a dump_paths.py directory, without executor witnesses (worst case).

Usage (repo root, PYTHONPATH=.): correspondence.py DUMPDIR [--seconds N]
Prints the proposal per x86 row and the time. Diagnostics only (proposals are never proofs).
"""
import json
import sys
import time
from pathlib import Path
from types import SimpleNamespace

from z3 import And, parse_smt2_file

import verification.block_equivalence as be

argv = sys.argv[1:]
d = Path(argv[0])
seconds = float(argv[argv.index("--seconds") + 1]) if "--seconds" in argv else 7200
meta = json.loads((d / "meta.json").read_text())


def path(name):
    return SimpleNamespace(condition=And(*parse_smt2_file(str(d / f"{name}.smt2"))), witness=None)


premise = And(*parse_smt2_file(str(d / "premise.smt2")))
evm = [path(f"evm_{i}") for i in range(len(meta["evm"]))]
x86 = [path(f"x86_{j}") for j in range(len(meta["x86"]))]
prover = be.BlockEquivalenceProver([], [], {}, timeout_ms=30000)
prover.deadline = time.monotonic() + seconds
started = time.monotonic()
found = prover._correspondence(evm, x86, premise, [])
print(f"{time.monotonic() - started:.1f}s", list(found), flush=True)
print("all rows:", [j for j, s in enumerate(found) if s == "all"], "dump run had:",
      [j for j, s in enumerate(meta["found"]) if s == "all"], flush=True)
