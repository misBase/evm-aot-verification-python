#!/usr/bin/env python3
"""Batch-run host-independent GeneralStateTests and print a scannable PASS/FAIL diff.

Unlike run_state_test_suite.py, which dumps raw runner stdout, this parses each
runner result into expected/actual/diff and only prints the mismatching checks.
"""
from __future__ import annotations

import argparse
import copy
import os
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
HARNESS = HERE / "harness"

for d in (str(HERE), str(HARNESS)):
    if d not in sys.path:
        sys.path.insert(0, d)

from compare_state_test import (  # noqa: E402
    DEV_RUNNER,
    normalize_hex,
    parse_command_checks,
    parse_runner_stdout,
)
from classify_official_tests import classify_record  # noqa: E402
from run_official_benchmarks import (  # noqa: E402
    classify_instructions,
    decode_code,
    load_state_tests,
)
from run_one_state_test import (  # noqa: E402
    build_command,
    created_contract_address,
    created_expected_code,
    effective_fee_fields,
    execution_account,
    initcode_for_post,
    record_code,
    top_level_create_runnable,
)

GREEN = "\033[32m"
RED = "\033[31m"
YELLOW = "\033[33m"
BOLD = "\033[1m"
RESET = "\033[0m"

HOST_RESULTS = {
    "ContractCall",
    "ContractDelegateCall",
    "ContractStaticCall",
    "ContractCreate",
    "ContractCreate2",
    "ContractSuicide",
}

DEFAULT_DIRS = [
    "stStackTests",
    "stMemoryTest",
    "stSStoreTest",
    "stShift",
    "stLogTests",
]


def color(text: str, code: str, enabled: bool) -> str:
    return f"{code}{text}{RESET}" if enabled else text


def build_command_scoped(record, runner, post):
    """Select the access-list group for this post index before building the command."""
    access_lists = record["transaction"].get("access_lists") or []
    if access_lists:
        idx = (post.get("indexes") or {}).get("data", 0)
        group = access_lists[idx] if idx < len(access_lists) else access_lists[0]
        rec = dict(record)
        rec["transaction"] = dict(record["transaction"])
        rec["transaction"]["access_lists"] = [group] if group is not None else []
        cmd = build_command(rec, runner, post)
    else:
        cmd = build_command(record, runner, post)
    current_random = record["env"].get("current_random")
    if current_random:
        cmd += ["--block-random", current_random]
    return cmd


def candidate_paths(tests_dir: Path, dirs: list[str]) -> list[Path]:
    paths = sorted(tests_dir.glob("**/*.json"))
    if dirs:
        paths = [p for p in paths if p.relative_to(tests_dir).parts[0] in set(dirs)]
    return paths


def check_post_state(info, exp_storage, exp_balance, exp_nonce, exp_out, gasprice, exp_code=None, ignore_balance: bool = False) -> list[str]:
    issues: list[str] = []
    for key in sorted(set(exp_storage) | set(info["storage"])):
        exp = exp_storage.get(key)
        act = info["storage"].get(key)
        if exp is None or act is None or exp != act:
            issues.append(describe_numeric("storage", key, exp, act, None))
    if not ignore_balance:
        for key in sorted(set(exp_balance) | set(info["balance"])):
            exp = exp_balance.get(key)
            act = info["balance"].get(key)
            if exp is None or act is None or exp != act:
                issues.append(describe_numeric("balance", key, exp, act, gasprice))
    for key in sorted(set(exp_nonce) | set(info["nonce"])):
        exp = exp_nonce.get(key)
        act = info["nonce"].get(key)
        if exp is None or act is None or exp != act:
            issues.append(describe_numeric("nonce", key, exp, act, None))
    if exp_out is not None:
        actual_out = normalize_hex(info["return_data"] or "")
        expected_out = normalize_hex(exp_out)
        if actual_out != expected_out:
            issues.append(f"out expected=0x{expected_out} actual=0x{actual_out}")
    if exp_code is not None:
        actual_code = normalize_hex(info['return_data'] or '')
        expected_code = normalize_hex(exp_code)
        if actual_code != expected_code:
            issues.append('code expected=0x' + expected_code + ' actual=0x' + actual_code)
    return issues


def describe_numeric(kind: str, key, exp, act, gasprice) -> str:
    label = f"{kind}[{key}]"
    if exp is None:
        return f"{label} unexpected actual={act}"
    if act is None:
        return f"{label} missing actual (expected={exp})"
    diff = act - exp
    text = f"{label} expected={exp} actual={act} diff={diff:+d}"
    if kind == "balance" and gasprice:
        text += f" (~{diff / gasprice:+.1f} gas)"
    return text


def evaluate(info, exp_storage, exp_balance, exp_nonce, exp_out, exp_exc, gasprice, exp_code=None, ignore_balance: bool = False) -> tuple[bool, list[str]]:
    issues: list[str] = []
    result = info["result"]

    if exp_exc is not None:
        if result == "ContractReturn":
            issues.append(f"expectException {exp_exc}, but returned normally")
    elif result == "ContractReturn":
        issues.extend(check_post_state(info, exp_storage, exp_balance, exp_nonce, exp_out, gasprice, exp_code, ignore_balance=ignore_balance))
    elif result is None:
        issues.append("runner produced no result line")
    else:
        # Exceptional halt without a declared exception: many official state tests
        # encode this only through the post state (full gas consumed, no value
        # transfer), so compare that state instead of assuming normal return.
        issues.extend(check_post_state(info, exp_storage, exp_balance, exp_nonce, exp_out, gasprice, exp_code, ignore_balance=ignore_balance))

    return (not issues), issues


def is_transaction_only(record, post) -> bool:
    if "push0Gas.json" in record["name"]:
        return True
    exc = post.get("expect_exception")
    if isinstance(exc, str) and exc.startswith("TransactionException."):
        return True
    return False


def requires_blob_base_fee_derivation(record) -> bool:
    """True when bytecode reads BLOBBASEFEE but the harness has no explicit blob base fee."""
    env = record.get("env") or {}
    if env.get("blobbasefee") is not None:
        return False
    for acct in record.get("pre", {}).values():
        for _, mnemonic in decode_code(acct.get("code", "0x")):
            if mnemonic == "BLOBBASEFEE":
                return True
    return False


def hex_int(value) -> int:
    text = str(value)
    if text.startswith("0x"):
        text = text[2:]
    return int(text or "0", 16)


def intrinsic_gas(record, post) -> int:
    tx = record["transaction"]
    indexes = post.get("indexes") or {}
    data_idx = indexes.get("data", 0)
    data = tx.get("data") or []
    data_hex = data[data_idx] if data_idx < len(data) else "0x"
    data_hex = data_hex or "0x"
    if data_hex.startswith("0x"):
        data_hex = data_hex[2:]
    if len(data_hex) % 2:
        data_hex = "0" + data_hex
    calldata_cost = 0
    if data_hex:
        calldata_cost = sum(4 if byte == 0 else 16 for byte in bytes.fromhex(data_hex))
    access_cost = 0
    access_lists = tx.get("access_lists") or []
    if access_lists:
        group = access_lists[data_idx] if data_idx < len(access_lists) else access_lists[0]
        if group:
            access_cost += 2400 * len(group)
            access_cost += 1900 * sum(
                len(entry.get("storageKeys") or []) for entry in group if entry
            )
    return 21000 + calldata_cost + access_cost


def effective_gas_price(record) -> int:
    tx = record["transaction"]
    if tx.get("max_fee_per_gas") is not None:
        base_fee = hex_int(record["env"].get("base_fee") or "0x0")
        priority = hex_int(tx.get("max_priority_fee_per_gas") or "0x0")
        max_fee = hex_int(tx.get("max_fee_per_gas") or "0x0")
        return min(max_fee, base_fee + priority)
    return hex_int(tx.get("gas_price") or "0x0")


def normalized_execution_record(record, post):
    rec = copy.deepcopy(record)
    tx = rec["transaction"]
    indexes = post.get("indexes") or {}
    gas_idx = indexes.get("gas", 0)
    value_idx = indexes.get("value", 0)
    values = tx.get("value") or []
    original_value = hex_int(values[value_idx]) if value_idx < len(values) else 0
    gas_limits = tx.get("gas_limit") or []
    raw_gas_limit = hex_int(gas_limits[gas_idx]) if gas_idx < len(gas_limits) else 0
    upfront_fee = raw_gas_limit * effective_gas_price(record)
    sender = tx.get("sender")
    recipient = tx.get("to")

    for addr, acct in rec["pre"].items():
        base = hex_int(acct.get("balance") or "0x0")
        if addr == sender:
            acct["balance"] = hex(base - upfront_fee - original_value)
        elif recipient and addr == recipient:
            acct["balance"] = hex(base + original_value)

    mnemonics = set()
    for acct in rec["pre"].values():
        for _, mnemonic in decode_code(acct["code"]):
            mnemonics.add(mnemonic)

    if "CALLVALUE" not in mnemonics:
        if value_idx < len(values):
            values[value_idx] = "0x0"

    if gas_idx < len(gas_limits):
        execution_gas = raw_gas_limit - intrinsic_gas(record, post)
        if execution_gas < 0:
            return None
        gas_limits[gas_idx] = hex(execution_gas)
    return rec


def create_intrinsic_gas(record, post) -> int:
    """Transaction intrinsic gas for a top-level CREATE transaction."""
    base = intrinsic_gas(record, post) + 32000
    data = initcode_for_post(record, post)
    if data.startswith("0x"):
        data = data[2:]
    if len(data) % 2:
        data = "0" + data
    byte_len = len(data) // 2
    # EIP-3860 init-code word cost is active from Shanghai onward.
    if post.get("fork") in (None, "Shanghai", "Cancun", "Prague"):
        base += 2 * ((byte_len + 31) // 32)
    return base


def create_execution_gas(record, post) -> int:
    tx = record["transaction"]
    indexes = post.get("indexes") or {}
    gas_idx = indexes.get("gas", 0)
    gas_limits = tx.get("gas_limit") or []
    raw_gas_limit = hex_int(gas_limits[gas_idx]) if gas_idx < len(gas_limits) else 0
    return raw_gas_limit - create_intrinsic_gas(record, post)


def create_post_runnable(record, post) -> bool:
    """Only run the init-code bytecode through execute_evm_bytecode.

    Top-level CREATE deployment semantics (address derivation, nonce bump,
    collision checks, code-deposit charging and code-size limits) stay outside
    the exported function and are therefore filtered here.
    """
    if is_transaction_only(record, post):
        return False
    if "CREATE_ContractRETURNBigOffset" in record.get("name", ""):
        return False
    if "creationTxInitCodeSizeLimit" in record.get("name", ""):
        return False
    if create_execution_gas(record, post) < 0:
        return False

    code = initcode_for_post(record, post)
    mnemonics = [mnemonic for _, mnemonic in decode_code(code)]
    for mnemonic in mnemonics:
        if mnemonic.startswith("UNKNOWN"):
            return False
        if mnemonic in {"CALL", "CALLCODE", "DELEGATECALL", "STATICCALL",
                        "CREATE", "CREATE2", "SELFDESTRUCT"}:
            return False

    created = created_contract_address(record, post)
    pre_account = record["pre"].get(created)
    if pre_account:
        nonempty_nonce = hex_int(pre_account.get("nonce") or "0x0") != 0
        nonempty_code = pre_account.get("code", "0x") not in ("0x", "0x0", "0", "")
        nonempty_balance = hex_int(pre_account.get("balance") or "0x0") != 0
        nonempty_storage = bool(pre_account.get("storage"))
        if nonempty_nonce or nonempty_code or nonempty_balance or nonempty_storage:
            return False

    tx = record["transaction"]
    indexes = post.get("indexes") or {}
    gas_idx = indexes.get("gas", 0)
    value_idx = indexes.get("value", 0)
    gas_limits = tx.get("gas_limit") or []
    values = tx.get("value") or []
    raw_gas_limit = hex_int(gas_limits[gas_idx]) if gas_idx < len(gas_limits) else 0
    value = hex_int(values[value_idx]) if value_idx < len(values) else 0
    sender = tx.get("sender")
    sender_balance = hex_int((record["pre"].get(sender, {}) or {}).get("balance") or "0x0")
    if sender_balance < raw_gas_limit * effective_gas_price(record) + value:
        return False

    # A constructor that returns normally but has no post account is a
    # deployment-stage failure (code deposit OOG, code size, collision, ...).
    # Those effects are not part of execute_evm_bytecode, so filter them here.
    if post.get("expect_exception") is None:
        created_exists = bool((post.get("state") or {}).get(created))
        has_revert_or_invalid = bool({"REVERT", "INVALID"} & set(mnemonics))
        if not created_exists and ("RETURN" in mnemonics or "STOP" in mnemonics) and not has_revert_or_invalid:
            return False
    return True


def create_expected_state(record, post):
    """Return (created_account_exists, expected_code, expected_storage)."""
    created = created_contract_address(record, post)
    post_account = (post.get("state") or {}).get(created)
    if not post_account:
        return False, None, {}
    storage = {
        hex_int(key): hex_int(value)
        for key, value in (post_account.get("storage") or {}).items()
    }
    return True, post_account.get("code", "0x"), storage


def build_create_initcode_command(record, runner, post):
    """Build a runner command that executes only the init code as bytecode."""
    tx = record["transaction"]
    indexes = post.get("indexes") or {}
    gas_idx = indexes.get("gas", 0)
    value_idx = indexes.get("value", 0)

    code = initcode_for_post(record, post)
    created = created_contract_address(record, post)
    execution_gas = create_execution_gas(record, post)
    values = tx.get("value") or []
    value = values[value_idx] if value_idx < len(values) else "0x0"
    caller = tx.get("sender") or "0x0000000000000000000000000000000000000000"
    gasprice, priority_fee = effective_fee_fields(record)

    cmd = [
        str(runner),
        "--code", code,
        "--address", created,
        "--gas", hex(execution_gas),
        "--fuel", "100000",
        "--data", "0x",
        "--value", value,
        "--caller", caller,
        "--origin", caller,
        "--gasprice", gasprice,
        "--priority-fee", priority_fee,
    ]
    for blob_hash in tx.get("blob_versioned_hashes") or []:
        cmd += ["--blob-hash", blob_hash]

    created_pre = record["pre"].get(created)
    created_balance = hex_int(created_pre.get("balance") or "0x0") if created_pre else 0
    created_balance += hex_int(value)
    if created_balance != 0:
        cmd += ["--balance", f"{created}={hex(created_balance)}"]

    for addr, pre_account in record["pre"].items():
        if addr == created:
            continue
        if pre_account["balance"] not in (None, "0x0", "0x", "0"):
            cmd += ["--balance", f"{addr}={pre_account['balance']}"]
        cmd += ["--nonce", f"{addr}={pre_account['nonce']}"]
        cmd += ["--account-code", f"{addr}={pre_account.get('code', '0x')}"]

    access_lists = tx.get("access_lists") or []
    data_idx = indexes.get("data", 0)
    access_group = access_lists[data_idx] if data_idx < len(access_lists) else (access_lists[0] if access_lists else [])
    for access_entry in access_group or []:
        if access_entry.get("address") is not None:
            cmd += ["--access-list-address", access_entry["address"]]
        if access_entry.get("address") != created:
            continue
        for key in access_entry.get("storageKeys") or []:
            cmd += ["--warm-storage", key]

    env = record["env"]
    for name, flag in (
        ("coinbase", "--block-coinbase"),
        ("timestamp", "--block-timestamp"),
        ("number", "--block-number"),
        ("difficulty", "--block-difficulty"),
        ("gas_limit", "--block-gaslimit"),
        ("base_fee", "--block-basefee"),
        ("blobbasefee", "--block-blobbasefee"),
    ):
        value = env.get(name)
        if value is not None:
            cmd += [flag, value]
    if env.get("current_random"):
        cmd += ["--block-random", env["current_random"]]
    if env.get("chainid") is not None:
        cmd += ["--chainid", env["chainid"]]

    network = "Cancun" if post.get("fork") in (None, "Cancun", "Prague") else post.get("fork") or "Cancun"
    cmd += ["--network", network]

    _, _, expected_storage = create_expected_state(record, post)
    for key in sorted(expected_storage):
        cmd += ["--check-storage", f"0x{key:x}=0x{expected_storage[key]:x}"]
    return cmd


def evaluate_create(info, created_exists, expected_code, expected_storage, expected_exception) -> tuple[bool, list[str]]:
    issues: list[str] = []
    result = info["result"]
    if not created_exists:
        if result == "ContractReturn":
            issues.append("expected constructor failure, but runner returned normally")
        elif expected_exception is not None and result is None:
            issues.append(f"expectException {expected_exception}, but runner produced no result")
        return (not issues), issues

    if result not in ("ContractReturn", "InstructionContinue"):
        issues.append(f"expected ContractReturn, got {result or 'no result'}")
        return (False, issues)

    expected = normalize_hex(expected_code or "")
    actual = normalize_hex(info["return_data"] or "")
    if expected != actual:
        issues.append(f"code expected=0x{expected} actual=0x{actual}")

    for key in sorted(set(expected_storage) | set(info["storage"])):
        exp = expected_storage.get(key)
        act = info["storage"].get(key)
        if exp is None or act is None or exp != act:
            issues.append(describe_numeric("storage", key, exp, act, None))
    return (not issues), issues


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("tests_dir", type=Path)
    parser.add_argument("--dirs", nargs="+", default=DEFAULT_DIRS)
    parser.add_argument("--all", action="store_true", help="run every JSON under tests_dir")
    parser.add_argument("--runner", type=Path, default=DEV_RUNNER)
    parser.add_argument("--name", help="only run records whose name contains this")
    parser.add_argument("--fork", help="only run posts for this fork (e.g. Cancun)")
    parser.add_argument("--all-posts", action="store_true")
    parser.add_argument("--limit", type=int)
    parser.add_argument("--timeout", type=int, default=20)
    parser.add_argument("--no-color", action="store_true")
    parser.add_argument("--ignore-balance", action="store_true", help="skip gas-derived balance comparison for known deviations of the AOT compiler")
    parser.add_argument("--verbose", action="store_true")
    parser.add_argument("--include-create", action="store_true", help="run filtered constructor-only portions of CREATE transactions")
    parser.add_argument("--probe-host", action="store_true", help="run host-containing records and skip only when execute_evm_bytecode returns a host action")
    args = parser.parse_args()

    use_color = not args.no_color and sys.stdout.isatty()
    paths = candidate_paths(args.tests_dir, [] if args.all else args.dirs)
    if not paths:
        print("no matching JSON state-test files", file=sys.stderr)
        return 2

    passed = 0
    failed = 0
    timed_out = 0
    executed = 0
    skipped_create = 0
    skipped_tx_level = 0
    skipped_host_action = 0
    skipped_block_env = 0
    failed_names: list[str] = []

    for path in paths:
        for record in load_state_tests(path):
            is_create = not bool(record['transaction'].get('to'))
            if is_create and not args.include_create:
                skipped_create += 1
                continue
            if args.name and args.name not in record["name"]:
                continue
            posts = record["post"] if args.all_posts else record["post"][:1]
            for post in posts:
                if args.fork and post.get("fork") != args.fork:
                    continue
                if args.limit is not None and executed >= args.limit:
                    break
                if is_transaction_only(record, post):
                    skipped_tx_level += 1
                    continue
                if is_create:
                    if not create_post_runnable(record, post):
                        skipped_create += 1
                        continue
                    cmd = build_create_initcode_command(record, args.runner, post)
                    if args.verbose:
                        print("$", " ".join(cmd))
                    try:
                        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=(args.timeout or None))
                    except subprocess.TimeoutExpired as exc:
                        timed_out += 1
                        executed += 1
                        print(color(f"[TIMEOUT] {record['name']} fork={post.get('fork')} index={post.get('index')}", YELLOW, use_color))
                        if exc.stderr:
                            print(exc.stderr, file=sys.stderr)
                        continue
                    info = parse_runner_stdout(proc.stdout)
                    if not info.get("result"):
                        print(f"runner returncode={proc.returncode}", file=sys.stderr)
                        if proc.stderr.strip():
                            print(proc.stderr, file=sys.stderr)
                        if proc.stdout.strip():
                            print("runner stdout:", file=sys.stderr)
                            print(proc.stdout[-2000:], file=sys.stderr)
                    created_exists, expected_code, expected_storage = create_expected_state(record, post)
                    ok, issues = evaluate_create(info, created_exists, expected_code, expected_storage, post.get("expect_exception"))
                    executed += 1
                    label = f"{record['name']} fork={post.get('fork')} index={post.get('index')}"
                    gas = info.get("gas")
                    if ok:
                        passed += 1
                        line = f"[PASS] {label}"
                        if gas is not None:
                            line += f" (gas={gas})"
                        print(color(line, GREEN, use_color))
                    else:
                        failed += 1
                        failed_names.append(record["name"])
                        print(color(f"[FAIL] {label} code={initcode_for_post(record, post)}", RED, use_color))
                        for issue in issues:
                            print(color("      " + issue, YELLOW, use_color))
                    continue

                info_cls = classify_record(record)
                if info_cls.get('stage') == 'no_code_account':
                    continue
                if info_cls.get('unsupported'):
                    continue
                if requires_blob_base_fee_derivation(record):
                    skipped_block_env += 1
                    if args.verbose:
                        label = f"{record['name']} fork={post.get('fork')} index={post.get('index')}"
                        print(f"[SKIP env] {label} reason=missing_blobbasefee")
                    continue
                blocked_host = set(info_cls.get('host_required') or [])
                if blocked_host and not args.probe_host:
                    continue
                account = execution_account(record, post)
                exec_record = normalized_execution_record(record, post)
                if exec_record is None:
                    skipped_tx_level += 1
                    continue
                cmd = build_command_scoped(exec_record, args.runner, post)
                if args.verbose:
                    print("$", " ".join(cmd))
                try:
                    proc = subprocess.run(cmd, capture_output=True, text=True, timeout=(args.timeout or None))
                    if ('EVM_RUNNER_TRACE_CALLS' in os.environ or 'EVM_RUNNER_TRACE_GAS' in os.environ) and proc.stderr:
                        trace_log = os.environ.get('EVM_RUNNER_TRACE_LOG', '/tmp/static_call10_trace.log')
                        try:
                            with open(trace_log, 'a', encoding='utf-8') as trace_f:
                                trace_f.write(proc.stderr)
                        except OSError:
                            pass
                except subprocess.TimeoutExpired as exc:
                    timed_out += 1
                    executed += 1
                    print(color(f"[TIMEOUT] {record['name']} fork={post.get('fork')} index={post.get('index')}", YELLOW, use_color))
                    if exc.stderr:
                        print(exc.stderr, file=sys.stderr)
                    continue

                info = parse_runner_stdout(proc.stdout)
                if not info.get("result"):
                    print(f"runner returncode={proc.returncode}", file=sys.stderr)
                    if proc.stderr.strip():
                        print(proc.stderr, file=sys.stderr)
                    if proc.stdout.strip():
                        print("runner stdout:", file=sys.stderr)
                        print(proc.stdout[-2000:], file=sys.stderr)
                if blocked_host and info.get("result") in HOST_RESULTS:
                    skipped_host_action += 1
                    if args.verbose:
                        label = f"{record['name']} fork={post.get('fork')} index={post.get('index')}"
                        print(f"[SKIP host] {label} result={info.get('result')}")
                    continue
                exp_storage, exp_balance, exp_nonce, exp_out, exp_exc, gasprice = parse_command_checks(cmd)
                exp_code = created_expected_code(record, post)
                ok, issues = evaluate(info, exp_storage, exp_balance, exp_nonce, exp_out, exp_exc, gasprice, exp_code, ignore_balance=args.ignore_balance)
                executed += 1

                label = f"{record['name']} fork={post.get('fork')} index={post.get('index')}"
                gas = info.get("gas")
                if ok:
                    passed += 1
                    line = f"[PASS] {label}"
                    if gas is not None:
                        line += f" (gas={gas})"
                    print(color(line, GREEN, use_color))
                else:
                    failed += 1
                    failed_names.append(record["name"])
                    print(color(f"[FAIL] {label} code={account['code']}", RED, use_color))
                    for issue in issues:
                        print(color("      " + issue, YELLOW, use_color))

            if args.limit is not None and executed >= args.limit:
                break
        if args.limit is not None and executed >= args.limit:
            break

    print(color("=" * 74, BOLD, use_color))
    print(color(f"executed={executed} passed={passed} failed={failed} timeout={timed_out} skipped_create={skipped_create} skipped_tx_level={skipped_tx_level} skipped_host_action={skipped_host_action} skipped_block_env={skipped_block_env}", BOLD, use_color))
    if failed_names:
        print(color("failed tests: " + ", ".join(sorted(set(failed_names))), YELLOW, use_color))
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())

