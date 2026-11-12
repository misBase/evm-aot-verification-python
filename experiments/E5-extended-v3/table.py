"""The extended-budget V3 table from complete-contract reports.

Usage: python table.py ROOT
ROOT holds <Contract>/report.json (a fresh run, see run.sh) or <Contract>.json files (the paper's reports in
expected/). For each report: status, wall time, proof instances and contexts, and how many proof instances the
instruction-level lockstep proved. VERIFIED requires the program certificate check to pass (status "verified").
"""
import json
import sys
from collections import Counter
from pathlib import Path

ORDER = ("ENSRegistry", "Permit2", "Safe", "CErc20", "PoolManager", "Pool")


def reports(root):
    root = Path(root)
    for name in ORDER:
        for path in (root / name / "report.json", root / f"{name}.json"):
            if path.is_file():
                yield name, json.loads(path.read_text())
                break


def main(root):
    print("| Contract | Status | Wall (s) | Blocks | Contexts | Proof instances | Instruction-level | Reasons |")
    print("|---|---|---:|---:|---:|---:|---:|---|")
    for name, r in reports(root):
        kinds = Counter(i.get("proof_kind", "block-level")
                        for v in r.get("diagnostics", {}).values() for i in v.get("instances", [])
                        if i.get("status") == "proved")
        closure = (r.get("closure_checks") or [{}])[0]
        reasons = "; ".join(str(x)[:80] for x in r.get("reasons", [])[:2])
        print(f"| {name} | {r.get('status')} | {r.get('process_wall_seconds', 0):.0f} | {r.get('evm_blocks')} | "
              f"{closure.get('contexts')} | {r.get('attempted_instances')} | {kinds.get('instruction-chain/1', 0)} | "
              f"{reasons} |")


if __name__ == "__main__":
    main(sys.argv[1])
