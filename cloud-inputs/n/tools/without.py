"""Run another diagnostic tool with one of this task's fixes switched off (A/B timing).

Usage (repo root, PYTHONPATH=.): without.py FIX TOOL.py ARGS...
FIX: range (potential_range_axioms -> []), words (_generalize_product_words -> None).
The tool runs as __main__ with sys.argv = [TOOL.py, ARGS...]. Diagnostics only.
"""
import runpy
import sys

import verification.block_equivalence as be

fix, tool = sys.argv[1], sys.argv[2]
if fix == "range":
    be.potential_range_axioms = lambda formula: []
elif fix == "words":
    be._generalize_product_words = lambda formula, min_width=128: None
else:
    raise SystemExit(f"unknown fix {fix}")
sys.argv = sys.argv[2:]
runpy.run_path(tool, run_name="__main__")
