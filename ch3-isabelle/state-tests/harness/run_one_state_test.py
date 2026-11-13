#!/usr/bin/env python3
"""Run one official GeneralStateTests record through the Rust benchmark entry."""
from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))

from run_official_benchmarks import load_state_tests  # noqa: E402
from keccak import contract_address  # noqa: E402


def pick_record(records, name_filter, index):
    if name_filter:
        records = [r for r in records if name_filter in r["name"]]
    if not records:
        raise SystemExit("no matching state-test record")
    if index >= len(records):
        raise SystemExit(f"record index {index} is out of range for {len(records)} records")
    return records[index]


def contract_account(record):
    pre = record["pre"]
    tx_to = record["transaction"]["to"]
    if tx_to and tx_to in pre and pre[tx_to]["code"] != "0x":
        return pre[tx_to]
    for addr in pre:
        if pre[addr]["code"] != "0x":
            return pre[addr]
    raise SystemExit("state test has no code-bearing account")


def first_post(record):
    posts = record['post']
    if not posts:
        raise SystemExit('state test has no post state')
    return posts[0]


def initcode_for_post(record, post):
    idx = (post.get('indexes') or {}).get('data', 0)
    data = record['transaction'].get('data') or []
    return data[idx] if idx < len(data) else '0x'


def derived_contract_address(record):
    sender = record["transaction"]["sender"]
    nonce = parse_hex_int((record["pre"].get(sender, {}) or {}).get("nonce"))
    return contract_address(sender, nonce)


def created_contract_address(record, post=None):
    return derived_contract_address(record)

def top_level_create_runnable(record, post=None):
    post = post or first_post(record)
    if post.get("expect_exception") is not None:
        return False
    # The generated cut_memory/iota0 path builds large return slices recursively.
    if "CREATE_ContractRETURNBigOffset" in record.get("name", ""):
        return False
    return True

def created_expected_code(record, post=None):
    post = post or first_post(record)
    if record["transaction"].get("to"):
        return None
    address = created_contract_address(record, post)
    pre_account = record["pre"].get(address, {})
    pre_code = pre_account.get("code", "0x")
    if parse_hex_int(pre_account.get("nonce")) != 0 or pre_code not in ("0x", "0x0", "0", ""):
        return None
    post_account = (post.get("state") or {}).get(address, {})
    return post_account.get("code", "0x")

def execution_account(record, post=None):
    post = post or first_post(record)
    tx = record['transaction']
    if tx.get('to'):
        return contract_account(record)
    code = initcode_for_post(record, post)
    return {
        'address': created_contract_address(record, post),
        'code': code,
        'storage': {},
    }


def record_code(record, post=None):
    post = post or first_post(record)
    if record['transaction'].get('to'):
        return contract_account(record)['code']
    return initcode_for_post(record, post)


def parse_hex_int(value):
    if value is None:
        return 0
    text = value[2:] if value.startswith("0x") else value
    return int(text or "0", 16)


def effective_fee_fields(record):
    tx = record["transaction"]
    env = record["env"]
    base_fee = parse_hex_int(env.get("base_fee"))
    max_fee = tx.get("max_fee_per_gas")
    priority = tx.get("max_priority_fee_per_gas")
    if max_fee is not None:
        max_fee_int = parse_hex_int(max_fee)
        priority_int = parse_hex_int(priority) if priority is not None else 0
        effective = min(max_fee_int, base_fee + priority_int)
        return hex(effective), hex(priority_int)
    return tx.get("gas_price") or "0x0", "0x0"


def build_command(record, runner: Path, post=None) -> list[str]:
    post = post or first_post(record)
    account = execution_account(record, post)
    tx = record["transaction"]
    indexes = post.get("indexes") or {}
    gas_idx = indexes.get("gas", 0)
    value_idx = indexes.get("value", 0)
    data_idx = indexes.get("data", 0)
    gas = (
        tx["gas_limit"][gas_idx]
        if tx.get("gas_limit") and gas_idx < len(tx["gas_limit"])
        else (post.get("gas_limit") or "0x0186a0")
    )
    value = (
        tx["value"][value_idx]
        if tx.get("value") and value_idx < len(tx["value"])
        else "0x0"
    )
    create_mode = not bool(tx.get('to'))
    data = (
        tx["data"][data_idx]
        if tx.get("data") and data_idx < len(tx["data"])
        else "0x"
    )
    caller = tx["sender"] or "0x0000000000000000000000000000000000000000"
    gasprice, priority_fee = effective_fee_fields(record)
    env = record["env"]

    cmd = [
        str(runner),
        "--code", account["code"],
        "--address", account["address"],
        "--gas", gas,
        "--fuel", "100000",
        "--data", ("0x" if create_mode else data),
        "--value", value,
        "--caller", caller,
        "--origin", caller,
        "--gasprice", gasprice,
        "--priority-fee", priority_fee,
    ]
    for blob_hash in tx.get("blob_versioned_hashes") or []:
        cmd += ["--blob-hash", blob_hash]

    if create_mode:
        cmd += ["--create"]
        cmd += ["--create-data", account['code']]

    for key, val in account["storage"].items():
        cmd += ["--storage", f"{key}={val}"]

    for access_group in tx.get("access_lists") or []:
        if not access_group:
            continue
        for access_entry in access_group:
            if access_entry.get("address") is not None:
                cmd += ["--access-list-address", access_entry["address"]]
            if access_entry.get("address") != account["address"]:
                continue
            for key in access_entry.get("storageKeys") or []:
                cmd += ["--warm-storage", key]

    for addr, pre_account in record["pre"].items():
        if pre_account["balance"] not in (None, "0x0", "0x", "0"):
            cmd += ["--balance", f"{addr}={pre_account['balance']}"]
        cmd += ["--nonce", f"{addr}={pre_account['nonce']}"]
        cmd += ["--account-code", f"{addr}={pre_account.get('code', '0x')}"]

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

    chainid = env.get("chainid")
    if chainid is not None:
        cmd += ["--chainid", chainid]

    network = "Cancun" if post.get("fork") in (None, "Cancun", "Prague") else post.get("fork") or "Cancun"
    cmd += ["--network", network]

    post_state = post.get("state") or {}
    post_account = post_state.get(account["address"], {})
    expected_storage = post_account.get("storage", {})
    storage_keys = sorted(set(account["storage"]) | set(expected_storage))
    for key in storage_keys:
        cmd += ["--check-storage", f"{key}={expected_storage.get(key, '0x0')}"]

    if record.get("out") is not None:
        cmd += ["--expect-out", record["out"]]

    expected_exception = post.get("expect_exception")
    if expected_exception is not None:
        cmd += ["--expect-exception", expected_exception]

    return cmd


def run_record(record, runner: Path, post=None, quiet: bool = False) -> int:
    post = post or first_post(record)
    account = execution_account(record, post)
    cmd = build_command(record, runner, post)
    if not quiet:
        print(f"[{record['name']}] code={account['code']} gas={post.get('gas_limit') or record['transaction']['gas_limit'][0]}")
        print(f"[run] {' '.join(cmd)}")
    return subprocess.run(cmd, check=False).returncode


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("json_file", type=Path)
    parser.add_argument("--name")
    parser.add_argument("--index", type=int, default=0)
    parser.add_argument(
        "--runner",
        type=Path,
        default=HERE.parent / "runner" / "target" / "release" / "evm_execute_runner_stage2",
    )
    args = parser.parse_args()

    records = load_state_tests(args.json_file)
    record = pick_record(records, args.name, args.index)
    return run_record(record, args.runner)


if __name__ == "__main__":
    raise SystemExit(main())

