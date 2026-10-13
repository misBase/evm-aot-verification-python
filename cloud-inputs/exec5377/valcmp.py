"""Compare two xseg output dirs: valcmp.py A B"""
import json
import re
import sys
from pathlib import Path

a, b = Path(sys.argv[1]), Path(sys.argv[2])


def load(d, f):
    p = d / f
    return json.loads(p.read_text()) if p.exists() else None


for f in ("paths.json", "evm_paths.json"):
    x, y = load(a, f), load(b, f)
    if isinstance(x, dict):
        x, y = x["x86"], y["x86"]
    same = x == y
    print(f, "identical" if same else f"DIFF {len(x or [])} vs {len(y or [])}, common {len(set(map(tuple, x or [])) & set(map(tuple, y or [])))}")
oa, ob = load(a, "outcome.json"), load(b, "outcome.json")
if oa and ob:
    print("status", oa["status"], ob["status"], "| paths", oa["evm_paths"], oa["x86_paths"], ob["evm_paths"], ob["x86_paths"])
    print("correspondence identical" if oa["correspondence"] == ob["correspondence"] else
          f"correspondence differs: {oa['correspondence']} vs {ob['correspondence']}")
    ra, rb = dict(map(tuple, oa["records"])), dict(map(tuple, ob["records"]))
    print("records", len(ra), len(rb), "only base", sorted(set(ra) - set(rb))[:20], "only opt", sorted(set(rb) - set(ra))[:20])
    print("answer changes", {k: (ra[k], rb[k]) for k in set(ra) & set(rb) if ra[k] != rb[k]})
for d in (a, b):
    lines = (d / "trace.log").read_text().splitlines()
    keep = [re.sub(r"\(0, .*\)$", "(...)", l)[:260] for l in lines if "PHASE" in l or "DONE" in l or "TOTAL" in l]
    print(d.name)
    for l in keep[-8:]:
        print("   ", l)
