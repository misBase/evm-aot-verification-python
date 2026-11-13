#!/usr/bin/env python3
"""Re-judge the runner outputs recorded while the semantic errors were being fixed (results/process-records/).

Each input line is one post-state run of the development runner: record name, fork, post index, the command the
development harness ran (including its --check-* expected values) and the runner's stdout. Nothing is executed:
every line is looked up in the pinned snapshot (TESTS_ROOT/GeneralStateTests) to confirm it belongs to it, and the
recorded stdout is judged against the checks recorded in its command with the evaluation of compare_state_suite.py.
The development runner named the outcomes CoreReturn/CoreFail; they are mapped to ContractReturn/ContractFail.

These early outputs cannot be judged against checks rebuilt by today's harness: the early runner printed a
different set of balance/nonce/storage lines, so most lines would fail on reporting differences alone.

usage: recheck_process_reports.py TESTS_ROOT REPORT.jsonl... [--out JSON]
"""
from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
for d in (HERE, HERE.parent):
    sys.path.insert(0, str(d))
from compare_state_suite import evaluate  # noqa: E402
from compare_state_test import parse_command_checks, parse_runner_stdout  # noqa: E402
from run_official_benchmarks import load_state_tests  # noqa: E402
from run_one_state_test import created_expected_code  # noqa: E402

RESULT_NAMES = {"CoreReturn": "ContractReturn", "CoreFail": "ContractFail"}


def judge(line: dict, tests_root: Path, cache: dict) -> tuple[str, list[str]]:
    path = tests_root / (line["name"].split(".json::", 1)[0] + ".json")
    if path not in cache:
        cache[path] = {r["name"]: r for r in load_state_tests(path)}
    record = cache[path][line["name"]]
    post = next(p for p in record["post"] if p["fork"] == line["fork"] and str(p["index"]) == str(line["index"]))
    info = parse_runner_stdout(line.get("output") or "")
    info["result"] = RESULT_NAMES.get(info["result"], info["result"])
    if info["result"] is None:
        return "NO_RESULT", ["runner produced no result line"]
    exp_storage, exp_balance, exp_nonce, exp_out, exp_exc, gasprice = parse_command_checks(line["command"])
    ok, issues = evaluate(info, exp_storage, exp_balance, exp_nonce, exp_out, exp_exc, gasprice,
                          created_expected_code(record, post))
    return ("PASS" if ok else "FAIL"), issues


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("tests_root", type=Path)
    parser.add_argument("reports", type=Path, nargs="+")
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()

    cache: dict = {}
    summary = {}
    for report in args.reports:
        counts, failing = Counter(), []
        for raw in report.open(encoding="utf-8"):
            line = json.loads(raw)
            verdict, issues = judge(line, args.tests_root, cache)
            counts[verdict] += 1
            if verdict != "PASS":
                failing.append({"name": line["name"], "fork": line["fork"], "index": line["index"],
                                "verdict": verdict, "issues": issues})
        summary[report.name] = {"post_states": sum(counts.values()), "verdicts": dict(sorted(counts.items())),
                                "not_passing": failing}
        print(f"{report.name}: {dict(sorted(counts.items()))}")
    if args.out:
        args.out.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
