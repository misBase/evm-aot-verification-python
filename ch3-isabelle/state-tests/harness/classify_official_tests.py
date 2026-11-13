#!/usr/bin/env python3
"""Classify every official GeneralStateTests record without executing it."""
from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))

from run_official_benchmarks import load_state_tests  # noqa: E402


def empty_accounts_storage(record) -> bool:
    return all(not account["storage"] for account in record["pre"].values())


def empty_tx_data(record) -> bool:
    data = record["transaction"]["data"]
    if data is None:
        return True
    return all(v in (None, "", "0x") for v in data)


def empty_tx_value(record) -> bool:
    values = record["transaction"]["value"]
    if values is None:
        return True
    return all(v in (None, "", "0x", "0x0") for v in values)


def code_accounts(record):
    return [account for account in record["pre"].values() if account["code"] != "0x"]


def classify_record(record):
    accounts = code_accounts(record)
    if not accounts:
        return {"stage": "no_code_account"}

    unsupported = sorted({x for account in accounts for x in account["classification"]["unsupported"]})
    host_required = sorted({x for account in accounts for x in account["classification"]["host_required"]})
    pre_storage = not empty_accounts_storage(record)
    tx_data = not empty_tx_data(record)
    tx_value = not empty_tx_value(record)

    return {
        "stage": "runnable_no_host" if not unsupported and not host_required else "needs_host_or_unsupported",
        "unsupported": unsupported,
        "host_required": host_required,
        "pre_storage": pre_storage,
        "tx_data": tx_data,
        "tx_value": tx_value,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("tests_dir", type=Path)
    parser.add_argument("--report", type=Path, default=HERE / "official_test_classification.json")
    parser.add_argument("--candidates", type=Path, default=HERE / "official_runnable_candidates.jsonl")
    args = parser.parse_args()

    files = sorted(args.tests_dir.glob("**/*.json"))
    if not files:
        print(f"no JSON files under {args.tests_dir}", file=sys.stderr)
        return 2

    total_files = 0
    total_records = 0
    no_code_account = 0
    runnable_no_host = 0
    needs_host_or_unsupported = 0
    unsupported_count = 0
    host_required_count = 0
    pre_storage_count = 0
    tx_data_count = 0
    tx_value_count = 0
    by_dir: Counter[str] = Counter()
    failed_files = []

    with args.candidates.open("w", encoding="utf-8") as out:
        for index, path in enumerate(files, 1):
            try:
                records = load_state_tests(path)
            except Exception as exc:
                failed_files.append({"file": str(path), "error": str(exc)})
                if index % 100 == 0:
                    print(f"[{index}/{len(files)}] processed, failed={len(failed_files)}")
                continue

            rel_dir = path.relative_to(args.tests_dir).parts[0]
            by_dir[rel_dir] += len(records)
            total_files += 1
            total_records += len(records)

            for record in records:
                info = classify_record(record)
                if info["stage"] == "no_code_account":
                    no_code_account += 1
                    continue
                if info["stage"] == "runnable_no_host":
                    runnable_no_host += 1
                    out.write(json.dumps({
                        "file": str(path),
                        "name": record["name"],
                        "code": next(account["code"] for account in code_accounts(record)),
                        "classification": info,
                    }, sort_keys=True) + "\n")
                else:
                    needs_host_or_unsupported += 1
                if info["unsupported"]:
                    unsupported_count += 1
                if info["host_required"]:
                    host_required_count += 1
                if info["pre_storage"]:
                    pre_storage_count += 1
                if info["tx_data"]:
                    tx_data_count += 1
                if info["tx_value"]:
                    tx_value_count += 1

            if index % 100 == 0:
                print(
                    f"[{index}/{len(files)}] records={total_records} "
                    f"runnable_no_host={runnable_no_host} needs_host={needs_host_or_unsupported} "
                    f"failed_files={len(failed_files)}"
                )

    summary = {
        "tests_dir": str(args.tests_dir),
        "total_files": total_files,
        "total_json_files_scanned": len(files),
        "failed_files": failed_files,
        "total_records": total_records,
        "no_code_account": no_code_account,
        "runnable_no_host_records": runnable_no_host,
        "needs_host_or_unsupported_records": needs_host_or_unsupported,
        "records_with_unsupported_opcode": unsupported_count,
        "records_with_host_required": host_required_count,
        "records_with_pre_storage": pre_storage_count,
        "records_with_tx_data": tx_data_count,
        "records_with_tx_value": tx_value_count,
        "records_by_top_level_directory": dict(by_dir.most_common()),
    }

    args.report.write_text(json.dumps(summary, indent=2, sort_keys=True), encoding="utf-8")
    print(json.dumps(summary, indent=2, sort_keys=True))
    print(f"candidates: {args.candidates}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
