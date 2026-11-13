#!/usr/bin/env python3
"""Run one minimal state-test fixture through the generated Rust runner.

The fixture is intentionally small: it executes ``PUSH1 0x2a MSTORE PUSH1
0x20 PUSH1 0x00 RETURN`` and checks that the runner returns 0x2a.  This smoke
test does not depend on the ethereum/tests checkout.
"""
from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
FIXTURE = HERE / "fixtures" / "minimal_add_ret.json"
RUNNER = HERE / "runner" / "target" / "release" / "evm_execute_runner_stage2"


def normalize_hex(value: str) -> str:
    text = (value or "").strip().lower()
    if text.startswith("0x"):
        text = text[2:]
    return text or "0"


def main() -> int:
    payload = json.loads(FIXTURE.read_text(encoding="utf-8"))
    record = next(iter(payload.values()))
    address = next(addr for addr, account in record["pre"].items() if account.get("code") != "0x")
    code = record["pre"][address]["code"]
    expected_out = record.get("out", "0x")

    cmd = [
        str(RUNNER),
        "--code", code,
        "--address", address,
        "--gas", record["transaction"]["gasLimit"][0],
        "--network", "Cancun",
    ]
    proc = subprocess.run(cmd, capture_output=True, text=True)
    if proc.returncode != 0:
        print(proc.stdout, end="")
        print(proc.stderr, end="", file=sys.stderr)
        return proc.returncode

    result = None
    actual_out = None
    for line in proc.stdout.splitlines():
        if line.startswith("result="):
            result = line.split("=", 1)[1]
        elif line.startswith("return_data="):
            actual_out = line.split("=", 1)[1]

    ok = result == "ContractReturn" and normalize_hex(actual_out or "") == normalize_hex(expected_out)
    print(f"runner={RUNNER}")
    print(f"code={code}")
    print(f"result={result}")
    print(f"expected_out={expected_out}")
    print(f"actual_out={actual_out}")
    print("SMOKE PASS" if ok else "SMOKE FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
