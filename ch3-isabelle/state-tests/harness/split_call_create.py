#!/usr/bin/env python3
"""Split the runnable candidates of classify_official_tests.py into call records (transaction.to set; these are the
records compare_state_suite.py runs) and create records (empty `to`; top-level deployment, not run).

usage: split_call_create.py CANDIDATES_JSONL TESTS_ROOT [--out JSON]
TESTS_ROOT is the directory the candidate `file` paths are relative to (the state-tests directory).
"""
from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from run_official_benchmarks import load_state_tests  # noqa: E402


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("candidates", type=Path)
    parser.add_argument("tests_root", type=Path)
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()

    records_by_file: dict[Path, dict[str, dict]] = {}
    total, post_variants, by_dir = Counter(), Counter(), Counter()
    for line in args.candidates.open(encoding="utf-8"):
        cand = json.loads(line)
        path = args.tests_root / cand["file"]
        if path not in records_by_file:
            records_by_file[path] = {r["name"]: r for r in load_state_tests(path)}
        record = records_by_file[path][cand["name"]]  # fixture keys are the full "<file>.json::<test>" names
        kind = "call" if record["transaction"]["to"] else "create"
        total[kind] += 1
        post_variants[kind] += len(record["post"])
        by_dir[f"{cand['name'].split('/')[1]}/{kind}"] += 1

    summary = {"records": dict(sorted(total.items())), "post_variants": dict(sorted(post_variants.items())),
               "records_by_top_level_directory": dict(sorted(by_dir.items()))}
    text = json.dumps(summary, indent=2, sort_keys=True)
    if args.out:
        args.out.write_text(text + "\n", encoding="utf-8")
    print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
