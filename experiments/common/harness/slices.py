"""B-fn candidates, canonical inputs and a conservative sample-admission gate.

Importing this module uses only the standard library. IR dispatcher matches are
structural evidence, not an ABI proof; admission also needs complete whole/slice
measurements on both sides. Missing measurements never become a valid sample.
"""
import argparse
from hashlib import sha256
import json
import os
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
from source_pin import SHA256 as EXPECTED_SOURCE_PIN, FILES as EXPECTED_SOURCE_FILES  # noqa: E402
SELECTOR_ENCODING = "shared-calldata-store4-be-v1"
EXPECTED_ANALYSIS_CONFIG = {
    "x86_base_addr": 0x1000,
    "x86_merge": False,
    "x86_reachability_timeout_ms": 250,
    "x86_summary": {
        "builtin_modes": dict.fromkeys(("calldataload", "copy_loop", "mul", "div", "memgas", "shift", "sdiv", "smod"), "fallback"),
        "prove_mul_hits": True,
        "prove_div_hits": True,
        "mul_proof_timeout_ms": 10000,
        "div_proof_timeout_ms": 30000,
    },
    "symbolic_gas": False,
    "gas_budget": 1000000000,
    "host_gas_uf_enabled": False,
    "assume_calldata_offset_no_overflow": False,
    "abstract_calldataload_words": False,
}


def validity_analysis_config():
    """Return independent JSON metadata for the fixed V2 reference profile."""
    return json.loads(json.dumps(EXPECTED_ANALYSIS_CONFIG))


def _reference_profile(profile):
    try:
        # JSON spelling also rejects int/float substitutes for booleans/integers.
        return json.dumps(profile, sort_keys=True) == json.dumps(EXPECTED_ANALYSIS_CONFIG, sort_keys=True)
    except (TypeError, ValueError):
        return False

# Formal-run r4 bytes; source: measurement-work/z6-reissue-plan/INPUTS.md. A same-named
# tests/data artifact is not a substitute. Paths are configurable; bytes are not.
CANONICAL_HASHES = {
    "CErc20": ("527fd12470d2c80272dcf6fc515d10d946abb34ed05025ceb864e5ddb82b8488", "6707f92f00d26e14e7c247dfa7481f7d0f4e8462075096f0ddef4c15c1e82c0e"),
    "Safe": ("94fc9f7c44cf00c39ed5b76015e64e033faeeed9a91d33029a02bbc566cffac5", "abf180cdf1e4086832533aeb4c257b2915a5fa0b90d2d8b08460f26c65f1efa8"),
    "ENSRegistry": ("2cb2f4e172ad7e5906fa772372685ca6aabbe17212f88c9538ef85ff1cf1ce2e", "a63b0ef8ed4075ac63ebc6374a621218f92c8b352ead69fc388c34948c93051b"),
    "Permit2": ("4adcdb781168d50e9d3f9be7848cc2f0f502e68c7b9121219edb899e6625aecf", "40f362e2e12dd8ab20c9fc2098c7c0d88747b3dafebe02f8e9461819362464e1"),
    "PoolManager": ("1d40b9d12b04c2984c95621b8093f59dd0687892a8aa4d1baa13616a94d15a03", "1ae33a365dabbdb8a22451bd57d029cbb04074a87d3e1b6a3de6722492e33c1a"),
    "Pool": ("8b7ff12132610ce147c70ccc257dca54555b72993d506c7f73e62588c867a5d2", "04aa03ffcc5a70f0d297184b602c948c945534c5edef918747a3e045ef86195c"),
}

CONTRACTS = {  # name -> fixture directory under tests/data/ext_contracts
    "ENSRegistry": "ens_registry",
    "CErc20": "compound_cerc20",
    "Safe": "safe",
    "Permit2": "uniswap_permit2",
    "PoolManager": "uniswap_v4_pool_manager",
    "Pool": "aave_v3_pool",
}

# (contract, function, selector, calldata size in bytes; None = symbolic size)
SLICES = [
    ("ENSRegistry", "owner(bytes32)", 0x02571BE3, 36),
    ("ENSRegistry", "resolver(bytes32)", 0x0178B8BF, 36),
    ("ENSRegistry", "setOwner(bytes32,address)", 0x5B0FC9C3, 68),
    ("ENSRegistry", "setSubnodeOwner(bytes32,bytes32,address)", 0x06AB5923, 100),
    ("ENSRegistry", "setRecord(bytes32,address,address,uint64)", 0xCF408823, 132),
    ("CErc20", "decimals()", 0x313CE567, 4),
    ("CErc20", "balanceOf(address)", 0x70A08231, 36),
    ("CErc20", "exchangeRateStored()", 0x182DF0F5, 4),
    ("CErc20", "transfer(address,uint256)", 0xA9059CBB, 68),
    ("CErc20", "mint(uint256)", 0xA0712D68, 36),
    ("Safe", "getThreshold()", 0xE75235B8, 4),
    ("Safe", "nonce()", 0xAFFED0E0, 4),
    ("Safe", "isOwner(address)", 0x2F54BF6E, 36),
    ("Safe", "getOwners()", 0xA0E67E2B, 4),
    ("Permit2", "DOMAIN_SEPARATOR()", 0x3644E515, 4),
    ("Permit2", "allowance(address,address,address)", 0x927DA105, 100),
    ("Permit2", "approve(address,address,uint160,uint48)", 0x87517C45, 132),
    ("PoolManager", "extsload(bytes32)", 0x1E2EAEAF, 36),
    ("PoolManager", "exttload(bytes32)", 0xF135BAAA, 36),
    ("PoolManager", "settle()", 0x11DA60B4, 4),
    ("Pool", "getReservesList()", 0xD1946DBC, 4),
    ("Pool", "getReserveData(address)", 0x35EA6A75, 36),
]


def fixture_receipt(stem):
    stem = Path(stem).resolve()
    if stem.name not in CANONICAL_HASHES:
        raise ValueError(f"not a canonical r4 contract: {stem.name}")
    actual = {}
    for suffix, expected in zip((".json", ".hex"), CANONICAL_HASHES[stem.name]):
        digest = sha256(Path(str(stem) + suffix).read_bytes()).hexdigest()
        if digest != expected:
            raise ValueError(f"canonical r4 SHA mismatch: {stem}{suffix}")
        actual[suffix] = digest
    return dict(contract=stem.name, stem=str(stem), program_sha256=actual)


def fixture_directory(value=None):
    value = value or os.environ.get("PAPER_FIXTURES")
    if not value:
        raise ValueError("explicit --fixtures or PAPER_FIXTURES is required (canonical r4 bytes)")
    return Path(value).resolve()


def selector_binding(selector, calldata_size):
    if type(selector) is not int or not 0 <= selector < 2**32:
        raise ValueError("selector must be a uint32")
    if calldata_size is not None and (type(calldata_size) is not int or calldata_size < 4):
        raise ValueError("a selector needs at least four calldata bytes")
    return dict(selector=f"0x{selector:08x}", calldata_size=calldata_size,
                encoding=SELECTOR_ENCODING, applied=True)


def pin_selector(state, selector, calldata_size):
    """Use one shared calldata array for both semantic views; no code slicing."""
    binding = selector_binding(selector, calldata_size)
    from z3 import BitVecVal, Store, UGE
    if calldata_size is None:
        state.add_assumption(UGE(state.calldatasize, BitVecVal(4, 64)))
    for offset, byte in enumerate(selector.to_bytes(4, "big")):
        state.calldata = Store(state.calldata, BitVecVal(offset, 64), BitVecVal(byte, 8))
    return binding


def _integer(value):
    if type(value) is int:
        return value
    if isinstance(value, str):
        return int(value, 16) if value.startswith("0x") else int(value)
    raise ValueError("not an IR integer")


def dispatcher_matches(data, selector=None):
    """Find PUSH4/EQ/static-JUMPI comparisons, not arbitrary numeric occurrences."""
    matches = []
    for frame in data.get("control_frames", []):
        ops = [op for op in frame.get("operations", []) if op.get("kind") not in ("TAG", "BLOCKEND")]
        for index, op in enumerate(ops[:-2]):
            if op.get("kind") != "PUSH" or op.get("param") != 4:
                continue
            try:
                immediate = _integer(op.get("immediate"))
                target = _integer(ops[index + 2].get("immediate"))
            except (ValueError, TypeError):
                continue
            if (0 <= immediate < 2**32 and (selector is None or immediate == selector)
                    and ops[index + 1].get("kind") == "EQ"
                    and ops[index + 2].get("kind") == "JUMPI"
                    and ops[index + 2].get("is_static") is True):
                matches.append(dict(selector=f"0x{immediate:08x}", dispatcher_pc=frame["pc"],
                                    instruction_pc=op.get("pc"), target_pc=target))
    return matches


def ir_constants(contract, fixtures=None):
    stem = fixture_directory(fixtures) / contract
    fixture_receipt(stem)
    return {int(row["selector"], 16) for row in dispatcher_matches(json.loads(stem.with_suffix(".json").read_bytes()))}


def _canonical_report(report):
    item = report.get("input")
    if not isinstance(item, dict) or item.get("contract") not in CANONICAL_HASHES:
        return False
    return item.get("program_sha256") == dict(zip((".json", ".hex"), CANONICAL_HASHES[item["contract"]]))


def _count(value):
    return type(value) is int and value >= 0


def _mapping(value):
    return value if isinstance(value, dict) else {}


def evaluate_validity(report, whole_report):
    """Pure metadata gate. Missing/failed evidence means unvalidated, not unreachable."""
    report, whole = _mapping(report), _mapping(whole_report)
    binding = report.get("selector_binding")
    checks = dict(canonical_slice_input=_canonical_report(report), canonical_whole_input=_canonical_report(whole) if whole else None)
    try:
        expected = selector_binding(int(binding["selector"], 16), binding["calldata_size"])
        checks["selector_bound"] = binding == expected
    except (TypeError, KeyError, ValueError):
        checks["selector_bound"] = False
    matches = report.get("dispatcher_matches")
    valid_matches = [row for row in matches if isinstance(row, dict)
                     and isinstance(binding, dict) and row.get("selector") == binding.get("selector")
                     and type(row.get("dispatcher_pc")) is int] if isinstance(matches, list) else []
    checks["dispatcher_match"] = bool(valid_matches) if matches is not None else None
    checks["slice_domain_sat"] = _mapping(report.get("domain")).get("answer") == "sat" if "domain" in report else None
    checks["whole_domain_sat"] = _mapping(whole.get("domain")).get("answer") == "sat" if "domain" in whole else None
    checks["same_input"] = _mapping(report.get("input")).get("program_sha256") == _mapping(whole.get("input")).get("program_sha256") if whole else None
    checks["whole_unpinned"] = whole.get("selector_binding") is None and whole.get("calldata_size") is None if whole else None
    checks["whole_completed"] = whole.get("result") == "WHOLE-METRICS" and whole.get("verified") is False if whole else None
    checks["no_measurement_errors"] = not report.get("measurement_error") and not whole.get("measurement_error")
    checks["slice_reference_profile"] = _reference_profile(report.get("analysis_config"))
    checks["whole_reference_profile"] = _reference_profile(whole.get("analysis_config"))
    checks["off_gas"] = report.get("gas_check") == "off" and whole.get("gas_check") == "off"
    for key in ("source_pin", "max_depth", "gas_check", "analysis_config"):
        left, right = report.get(key), whole.get(key)
        checks["same_" + key] = left == right if left is not None and right is not None else None
    checks["source_unchanged"] = report.get("source_unchanged") is True and whole.get("source_unchanged") is True if whole else None
    differences = {}
    for side in ("evm", "x86"):
        left = _mapping(report.get("metrics")).get(side)
        right = _mapping(whole.get("metrics")).get(side)
        if not isinstance(left, dict) or not isinstance(right, dict):
            checks[side + "_coverage_complete"] = checks[side + "_paths_reduced"] = None
            continue
        complete = left.get("coverage_complete"), right.get("coverage_complete")
        checks[side + "_coverage_complete"] = all(complete) if all(type(v) is bool for v in complete) else None
        a, b = left.get("terminal_paths"), right.get("terminal_paths")
        checks[side + "_paths_reduced"] = 0 < a < b if _count(a) and _count(b) else None
        differences[side] = dict(slice_paths=a, whole_paths=b, slice_coverage=left.get("coverage_complete"),
                                 whole_coverage=right.get("coverage_complete"), slice_reason=left.get("coverage_reason"),
                                 whole_reason=right.get("coverage_reason"))
    a = _mapping(_mapping(report.get("metrics")).get("evm"))
    b = _mapping(_mapping(whole.get("metrics")).get("evm"))
    aset, bset = a.get("block_pcs"), b.get("block_pcs")
    if isinstance(aset, list) and isinstance(bset, list) and all(type(pc) is int for pc in aset + bset):
        checks["evm_blocks_reduced"] = bool(aset) and set(aset) < set(bset)
        checks["dispatcher_explored"] = any(row["dispatcher_pc"] in aset for row in valid_matches)
        differences["evm_blocks"] = dict(slice=len(set(aset)), whole=len(set(bset)),
            removed=sorted(set(bset) - set(aset)), extra=sorted(set(aset) - set(bset)),
            retained_fraction=len(set(aset)) / len(set(bset)) if bset else None)
    else:
        checks["evm_blocks_reduced"] = None
        checks["dispatcher_explored"] = None
    accepted = all(value is True for value in checks.values())
    return dict(status="accepted" if accepted else "unvalidated", accepted=accepted, checks=checks,
                missing=[key for key, value in checks.items() if value is None],
                not_satisfied=[key for key, value in checks.items() if value is False], differences=differences,
                reasons=[key + (": missing" if value is None else ": not established") for key, value in checks.items() if value is not True])


def receipt_failure(record, stem, selector, size, expected_pin=EXPECTED_SOURCE_PIN):
    """Return a rejection reason for a reach-job receipt; None admits this sample."""
    try:
        actual = fixture_receipt(stem)
        if record.get("input", {}).get("program_sha256") != actual["program_sha256"]:
            return "canonical input receipt mismatch"
        if record.get("source_pin") != expected_pin or record.get("source_unchanged") is not True:
            return "source pin missing, changed or unexpected"
        if record.get("selector_binding") != selector_binding(selector, size):
            return "selector/length/shared-array binding mismatch"
        validation = evaluate_validity(record, record.get("whole_baseline"))
        if record.get("result") != "SLICE-VALID" or record.get("verified") is not False or not validation["accepted"]:
            return "slice unvalidated: " + "; ".join(validation["reasons"])
    except (OSError, ValueError, TypeError, KeyError, AttributeError) as error:
        return f"invalid slice receipt: {error}"
    return None


def check(fixtures=None):
    fixtures = fixture_directory(fixtures)
    cache, bad = {}, []
    for contract, function, selector, _ in SLICES:
        if contract not in cache:
            cache[contract] = ir_constants(contract, fixtures)
        ok = selector in cache[contract]
        print(f"{'ok ' if ok else 'MISSING'} {contract}.{function} 0x{selector:08x}")
        if not ok:
            bad.append((contract, function))
    return bad


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fixtures", default=os.environ.get("PAPER_FIXTURES"))
    args = parser.parse_args()
    try:
        sys.exit(1 if check(args.fixtures) else 0)
    except (ValueError, OSError) as error:
        parser.error(str(error))
