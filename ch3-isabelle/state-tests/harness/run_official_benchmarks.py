#!/usr/bin/env python3
"""Load and classify official ethereum/tests GeneralStateTests files.

This is the first stage of the official EVM conformance integration.  It reads
the StateTest JSON layout consumed by go-ethereum and normalizes
each subtest into a stable Python record.  It does not replace the generated
Rust engine; the normalized records are the input contract for the next Rust
runner stage.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


# Byte -> mnemonic map used by the lightweight parser bridge.  The values here
# only need to be complete enough to classify benchmark cases; unknown bytes
# are reported as unsupported rather than silently interpreted.
OPCODES = {
    0x00: "STOP",
    0x01: "ADD",
    0x02: "MUL",
    0x03: "SUB",
    0x04: "DIV",
    0x05: "SDIV",
    0x06: "MOD",
    0x07: "SMOD",
    0x08: "ADDMOD",
    0x09: "MULMOD",
    0x0A: "EXP",
    0x0B: "SIGNEXTEND",
    0x10: "LT",
    0x11: "GT",
    0x12: "SLT",
    0x13: "SGT",
    0x14: "EQ",
    0x15: "ISZERO",
    0x16: "AND",
    0x17: "OR",
    0x18: "XOR",
    0x19: "NOT",
    0x1A: "BYTE",
    0x1B: "SHL",
    0x1C: "SHR",
    0x1D: "SAR",
    0x20: "KECCAK256",
    0x30: "ADDRESS",
    0x31: "BALANCE",
    0x32: "ORIGIN",
    0x33: "CALLER",
    0x34: "CALLVALUE",
    0x35: "CALLDATALOAD",
    0x36: "CALLDATASIZE",
    0x37: "CALLDATACOPY",
    0x38: "CODESIZE",
    0x39: "CODECOPY",
    0x3A: "GASPRICE",
    0x3B: "EXTCODESIZE",
    0x3C: "EXTCODECOPY",
    0x3D: "RETURNDATASIZE",
    0x3E: "RETURNDATACOPY",
    0x3F: "EXTCODEHASH",
    0x40: "BLOCKHASH",
    0x41: "COINBASE",
    0x42: "TIMESTAMP",
    0x43: "NUMBER",
    0x44: "DIFFICULTY",
    0x45: "GASLIMIT",
    0x46: "CHAINID",
    0x47: "SELFBALANCE",
    0x48: "BASEFEE",
    0x49: "BLOBHASH",
    0x4A: "BLOBBASEFEE",
    0x50: "POP",
    0x51: "MLOAD",
    0x52: "MSTORE",
    0x53: "MSTORE8",
    0x54: "SLOAD",
    0x55: "SSTORE",
    0x56: "JUMP",
    0x57: "JUMPI",
    0x58: "PC",
    0x59: "MSIZE",
    0x5A: "GAS",
    0x5B: "JUMPDEST",
    0x5C: "TLOAD",
    0x5D: "TSTORE",
    0x5E: "MCOPY",
    0x5F: "PUSH0",
    0x80: "DUP1",
    0x81: "DUP2",
    0x82: "DUP3",
    0x83: "DUP4",
    0x84: "DUP5",
    0x85: "DUP6",
    0x86: "DUP7",
    0x87: "DUP8",
    0x88: "DUP9",
    0x89: "DUP10",
    0x8A: "DUP11",
    0x8B: "DUP12",
    0x8C: "DUP13",
    0x8D: "DUP14",
    0x8E: "DUP15",
    0x8F: "DUP16",
    0x90: "SWAP1",
    0x91: "SWAP2",
    0x92: "SWAP3",
    0x93: "SWAP4",
    0x94: "SWAP5",
    0x95: "SWAP6",
    0x96: "SWAP7",
    0x97: "SWAP8",
    0x98: "SWAP9",
    0x99: "SWAP10",
    0x9A: "SWAP11",
    0x9B: "SWAP12",
    0x9C: "SWAP13",
    0x9D: "SWAP14",
    0x9E: "SWAP15",
    0x9F: "SWAP16",
    0xA0: "LOG0",
    0xA1: "LOG1",
    0xA2: "LOG2",
    0xA3: "LOG3",
    0xA4: "LOG4",
    0xF0: "CREATE",
    0xF1: "CALL",
    0xF2: "CALLCODE",
    0xF3: "RETURN",
    0xF4: "DELEGATECALL",
    0xF5: "CREATE2",
    0xFA: "STATICCALL",
    0xFD: "REVERT",
    0xFE: "INVALID",
    0xFF: "SELFDESTRUCT",
}

PUSH_RANGE = range(0x60, 0x80)

HOST_REQUIRED = {
    "CALL",
    "CALLCODE",
    "DELEGATECALL",
    "STATICCALL",
    "CREATE",
    "CREATE2",
    "SELFDESTRUCT",
}


def hex_to_bytes(value: str) -> bytes:
    if value.startswith("0x"):
        value = value[2:]
    if len(value) % 2:
        value = "0" + value
    return bytes.fromhex(value)


def decode_code(code: str | bytes) -> list[tuple[int, str]]:
    if isinstance(code, str):
        code = hex_to_bytes(code)
    out: list[tuple[int, str]] = []
    i = 0
    while i < len(code):
        b = code[i]
        if b in PUSH_RANGE:
            size = b - 0x5F
            out.append((i, f"PUSH{size}"))
            i += 1 + size
        else:
            out.append((i, OPCODES.get(b, f"UNKNOWN(0x{b:02x})")))
            i += 1
    return out


def normalize_uint(value: Any) -> str:
    if value is None:
        return "0x0"
    if isinstance(value, int):
        return hex(value)
    if isinstance(value, str):
        return value if value.startswith("0x") else "0x" + value
    return str(value)


def normalize_account(addr: str, account: dict[str, Any]) -> dict[str, Any]:
    code = account.get("code", "0x")
    storage = {
        normalize_uint(k): normalize_uint(v)
        for k, v in (account.get("storage") or {}).items()
    }
    return {
        "address": addr,
        "balance": normalize_uint(account.get("balance", "0x0")),
        "nonce": normalize_uint(account.get("nonce", "0x0")),
        "code": code,
        "storage": storage,
        "instructions": decode_code(code),
        "classification": classify_instructions(decode_code(code)),
    }


def classify_instructions(instructions: list[tuple[int, str]]) -> dict[str, list[str]]:
    unsupported = []
    host_required = []
    for _, mnemonic in instructions:
        if mnemonic.startswith("UNKNOWN"):
            unsupported.append(mnemonic)
        elif mnemonic in HOST_REQUIRED:
            host_required.append(mnemonic)
    return {
        "unsupported": sorted(set(unsupported)),
        "host_required": sorted(set(host_required)),
    }


def load_state_tests(path: Path) -> list[dict[str, Any]]:
    with path.open("r", encoding="utf-8") as f:
        payload = json.load(f)

    # ethereum/tests GeneralStateTests files usually contain multiple named
    # StateTest objects, while ipsilon/evm-benchmarks files contain one.
    records = []
    for name, test in payload.items():
        env = test.get("env", {})
        tx = test.get("transaction", {})
        pre = {addr: normalize_account(addr, acc) for addr, acc in (test.get("pre") or {}).items()}

        subtests = []
        for fork, posts in (test.get("post") or {}).items():
            for idx, post in enumerate(posts):
                subtests.append({
                    "fork": fork,
                    "index": idx,
                    "indexes": post.get("indexes", {}),
                    "expect_exception": post.get("expectException"),
                    "gas_limit": normalize_uint(tx.get("gasLimit", [])[idx] if idx < len(tx.get("gasLimit", [])) else None),
                    "state": {
                        addr: normalize_account(addr, acc)
                        for addr, acc in (post.get("state") or {}).items()
                    },
                    "value": normalize_uint(tx.get("value", [])[idx] if idx < len(tx.get("value", [])) else None),
                    "logs": post.get("logs"),
                })

        records.append({
            "file": str(path),
            "name": name,
            "env": {
                "coinbase": env.get("currentCoinbase"),
                "difficulty": normalize_uint(env.get("currentDifficulty")),
                "current_random": normalize_uint(env.get("currentRandom")),
                "gas_limit": normalize_uint(env.get("currentGasLimit")),
                "number": normalize_uint(env.get("currentNumber")),
                "timestamp": normalize_uint(env.get("currentTimestamp")),
                "base_fee": normalize_uint(env.get("currentBaseFee")),
                "chainid": normalize_uint(test.get("config", {}).get("chainid")),
            },
            "transaction": {
                "to": tx.get("to"),
                "data": tx.get("data", []),
                "gas_limit": [normalize_uint(v) for v in tx.get("gasLimit", [])],
                "gas_price": normalize_uint(tx["gasPrice"]) if "gasPrice" in tx else None,
                "max_fee_per_gas": normalize_uint(tx["maxFeePerGas"]) if "maxFeePerGas" in tx else None,
                "max_priority_fee_per_gas": normalize_uint(tx["maxPriorityFeePerGas"]) if "maxPriorityFeePerGas" in tx else None,
                "value": [normalize_uint(v) for v in tx.get("value", [])],
                "sender": tx.get("sender"),
                "secret_key": tx.get("secretKey"),
                "access_lists": tx.get("accessLists", []),
                "blob_versioned_hashes": tx.get("blobVersionedHashes", []),
            },
            "out": test.get("out"),
            "pre": pre,
            "post": subtests,
        })

    return records


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("tests_dir", type=Path, help="path to ethereum/tests/GeneralStateTests")
    parser.add_argument("--json", action="store_true", help="print normalized records as JSON")
    args = parser.parse_args()

    files = sorted(args.tests_dir.glob("**/*.json"))
    if not files:
        print(f"no JSON state-test files under {args.tests_dir}")
        return 2

    records = [record for path in files for record in load_state_tests(path)]
    if args.json:
        print(json.dumps(records, indent=2, sort_keys=True))
        return 0

    for record in records:
        print(f"[{record['name']}] file={record['file']}")
        print(f"  env number={record['env']['number']} timestamp={record['env']['timestamp']}")
        print(f"  tx.to={record['transaction']['to']}")
        print(f"  tx.data={record['transaction']['data']}")
        for post in record["post"]:
            print(f"  post {post['fork']}/{post['index']} gas={post['gas_limit']} value={post['value']}")
        for addr, account in record["pre"].items():
            print(f"  pre {addr}: nonce={account['nonce']} balance={account['balance']} code={account['code']}")
            print(f"    instructions={account['instructions']}")
            print(f"    unsupported={account['classification']['unsupported']}")
            print(f"    host_required={account['classification']['host_required']}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
