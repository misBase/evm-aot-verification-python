#!/usr/bin/env python3
"""Compare one official GeneralStateTests result with the generated Rust runner.

Parse the runner output into expected/actual values and print PASS/FAIL rows.
"""
from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent
HARNESS = REPO / "harness"
DEV_RUNNER = (REPO / "runner" / "target" / "release" / "evm_execute_runner_stage2")

if str(HARNESS) not in sys.path:
    sys.path.insert(0, str(HARNESS))

from run_official_benchmarks import load_state_tests, decode_code  # noqa: E402
from run_one_state_test import (  # noqa: E402
    build_command,
    contract_account,
    created_expected_code,
    execution_account,
    first_post,
    parse_hex_int,
    pick_record,
)

GREEN = "\033[32m"
RED = "\033[31m"
YELLOW = "\033[33m"
BOLD = "\033[1m"
RESET = "\033[0m"

STORAGE_RE = re.compile(r"^storage\[([^\]]+)\]=(.*)$")
BALANCE_RE = re.compile(r"^balance\[([^\]]+)\]=(.*)$")
NONCE_RE = re.compile(r"^nonce\[([^\]]+)\]=(.*)$")


def color(text: str, code: str, enabled: bool) -> str:
    return f"{code}{text}{RESET}" if enabled else text


def parse_int(text: str) -> int:
    text = text.strip()
    if text.lower().startswith("0x"):
        return int(text[2:] or "0", 16)
    return int(text or "0", 10)


def normalize_hex(text: str) -> str:
    return text.strip().lower().lstrip("0x") or "0"


def parse_runner_stdout(text: str) -> dict:
    info = {
        "storage": {},
        "balance": {},
        "nonce": {},
        "result": None,
        "return_data": None,
        "gas": None,
        "pc": None,
        "logs": None,
        "failure_reasons": None,
    }
    for raw in text.splitlines():
        line = raw.strip()
        m = STORAGE_RE.match(line)
        if m:
            info["storage"][parse_int(m.group(1))] = parse_int(m.group(2))
            continue
        m = BALANCE_RE.match(line)
        if m:
            info["balance"][normalize_hex(m.group(1))] = parse_int(m.group(2))
            continue
        m = NONCE_RE.match(line)
        if m:
            info["nonce"][normalize_hex(m.group(1))] = parse_int(m.group(2))
            continue
        for key in ("result", "return_data", "gas", "pc", "logs", "failure_reasons"):
            prefix = key + "="
            if line.startswith(prefix):
                info[key] = line[len(prefix):]
                break
    return info


def parse_command_checks(cmd: list[str]) -> tuple:
    storage, balance, nonce = {}, {}, {}
    expected_out = None
    expected_exception = None
    gasprice = 0
    i = 0
    while i < len(cmd):
        arg = cmd[i]
        nxt = cmd[i + 1] if i + 1 < len(cmd) else None
        if arg == "--check-storage" and nxt:
            key, value = nxt.split("=", 1)
            storage[parse_int(key)] = parse_int(value)
        elif arg == "--check-balance" and nxt:
            addr, value = nxt.split("=", 1)
            balance[normalize_hex(addr)] = parse_int(value)
        elif arg == "--check-nonce" and nxt:
            addr, value = nxt.split("=", 1)
            nonce[normalize_hex(addr)] = parse_int(value)
        elif arg == "--expect-out" and nxt:
            expected_out = nxt
        elif arg == "--expect-exception" and nxt:
            expected_exception = nxt
        elif arg == "--gasprice" and nxt:
            gasprice = parse_int(nxt)
        i += 1
    return storage, balance, nonce, expected_out, expected_exception, gasprice


def print_row(label: str, expected: str, actual: str, diff: str, ok: bool, use_color: bool) -> None:
    mark = color("PASS", GREEN, use_color) if ok else color("FAIL", RED, use_color)
    print(f"  {label:<34} {expected:>24} {actual:>24} {diff:>16}  {mark}")


def compare_numeric(
    label: str,
    expected: dict,
    actual: dict,
    use_color: bool,
    gasprice: int,
    caller: str,
) -> tuple[int, list[str]]:
    failed = 0
    notes = []
    keys = sorted(set(expected) | set(actual))
    for key in keys:
        exp = expected.get(key)
        act = actual.get(key)
        if act is None:
            print_row(f"{label}[{key}]", str(exp), "?", "?", False, use_color)
            failed += 1
            notes.append(f"{label}[{key}] missing actual value")
            continue
        if exp is None:
            print_row(f"{label}[{key}]", "?", str(act), "?", False, use_color)
            failed += 1
            notes.append(f"{label}[{key}] unexpected actual value")
            continue
        diff = act - exp
        if diff == 0:
            diff_text = "0"
            ok = True
        else:
            diff_text = f"{diff:+d}"
            ok = False
            failed += 1
        print_row(f"{label}[{key}]", str(exp), str(act), diff_text, ok, use_color)
        if not ok and label == "balance" and gasprice:
            gas_hint = diff / gasprice
            notes.append(
                f"balance[{key}] diff {diff:+d} wei ~ {gas_hint:+.1f} gas (gasprice={gasprice})"
            )
    return failed, notes


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("json_file", type=Path)
    parser.add_argument("--name", help="only run records whose name contains this")
    parser.add_argument("--index", type=int, default=0, help="0-based post index")
    parser.add_argument("--runner", type=Path, default=DEV_RUNNER)
    parser.add_argument("--no-color", action="store_true")
    parser.add_argument("--verbose", action="store_true", help="print the full command and raw runner output")
    args = parser.parse_args()

    use_color = not args.no_color and sys.stdout.isatty()
    records = load_state_tests(args.json_file)
    record = pick_record(records, args.name, args.index)
    post = first_post(record)
    account = execution_account(record, post)

    cmd = build_command(record, args.runner, post)
    if args.verbose:
        print("$", " ".join(cmd))

    proc = subprocess.run(cmd, check=False, capture_output=True, text=True)
    info = parse_runner_stdout(proc.stdout)
    exp_storage, exp_balance, exp_nonce, exp_out, exp_exc, gasprice = parse_command_checks(cmd)
    exp_code = created_expected_code(record, post)

    print(color("=" * 74, BOLD, use_color))
    print(color(f"{record['name']}   fork={post['fork']}   index={post['index']}", BOLD, use_color))
    print(f"code      {account['code']}")
    print(f"asm       {' '.join(m for _, m in decode_code(account['code']))}")
    print(f"result    {info['result']}   gas={info['gas']}   pc={info['pc']}   logs={info['logs']}")
    if info["failure_reasons"]:
        print(f"failure   {info['failure_reasons']}")
    print(color("-" * 74, BOLD, use_color))
    print(f"  {'check':<34} {'expected':>24} {'actual':>24} {'diff':>16}  result")

    failed = 0
    notes: list[str] = []

    n, extra = compare_numeric("storage", exp_storage, info["storage"], use_color, gasprice, "")
    failed += n
    notes += extra

    n, extra = compare_numeric(
        "balance",
        exp_balance,
        info["balance"],
        use_color,
        gasprice,
        normalize_hex(record["transaction"]["sender"] or "0"),
    )
    failed += n
    notes += extra

    n, extra = compare_numeric("nonce", exp_nonce, info["nonce"], use_color, gasprice, "")
    failed += n
    notes += extra

    if exp_code is not None:
        actual_code = normalize_hex(info['return_data'] or '')
        expected_code = normalize_hex(exp_code)
        ok = actual_code == expected_code
        print_row('code', '0x' + expected_code, '0x' + actual_code, '0' if ok else 'MISMATCH', ok, use_color)
        if not ok:
            failed += 1

    if exp_out is not None:
        actual_out = normalize_hex(info["return_data"] or "")
        expected_out = normalize_hex(exp_out)
        ok = actual_out == expected_out
        print_row("out", "0x" + expected_out, "0x" + actual_out, "0" if ok else "MISMATCH", ok, use_color)
        if not ok:
            failed += 1

    if exp_exc is not None:
        ok = info["result"] not in (None, "ContractReturn")
        print_row(
            "expectException",
            exp_exc,
            info["result"] or "?",
            "OK" if ok else "NOT RAISED",
            ok,
            use_color,
        )
        if not ok:
            failed += 1

    print(color("-" * 74, BOLD, use_color))
    total = (
        len(set(exp_storage) | set(info["storage"]))
        + len(set(exp_balance) | set(info["balance"]))
        + len(set(exp_nonce) | set(info["nonce"]))
        + (1 if exp_code is not None else 0)
        + (1 if exp_out is not None else 0)
        + (1 if exp_exc is not None else 0)
    )
    if failed == 0:
        print(color(f"PASS  {total}/{total} checks passed", GREEN, use_color))
    else:
        print(color(f"FAIL  {failed}/{total} checks failed", RED, use_color))

    for note in notes:
        print(color("  -> " + note, YELLOW, use_color))

    if args.verbose and proc.stdout:
        print(color("-" * 74, BOLD, use_color))
        print(proc.stdout, end="")
    if args.verbose and proc.stderr:
        print(proc.stderr, end="")

    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
