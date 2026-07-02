"""External contract fixture verification smoke tests."""

from pathlib import Path

import pytest
from z3 import BitVecVal, Store

from evm_ir.json_parser import load_ir_from_json
from evm_ir.program import EVMProgram
from state.smt_state import SMTState
from verification.program_verifier import ProgramEquivalenceChecker
from x86_64.program import X86Program
from x86_64.summaries import TRUSTED_SUMMARY_CONFIG


EXT_CONTRACT_ROOT = Path(__file__).resolve().parents[1] / "data" / "ext_contracts"
GO_AMD64_MAX_SLICE_LEN = (1 << 63) - 1


def _load_ext_contract_pair(case: str, contract: str) -> tuple[EVMProgram, X86Program]:
    case_dir = EXT_CONTRACT_ROOT / case
    evm_program = EVMProgram(load_ir_from_json(str(case_dir / f"{contract}.json")))
    x86_program = X86Program.from_hex(
        (case_dir / f"{contract}.hex").read_text(encoding="utf-8").strip(),
        base_addr=0,
    )
    return evm_program, x86_program


def _selector_state(selector: int, calldata_size: int | None = None) -> SMTState:
    state = SMTState.create_initial_state(calldata_size_bytes=calldata_size)
    for offset, byte in enumerate(selector.to_bytes(4, "big")):
        state.calldata = Store(
            state.calldata,
            BitVecVal(offset, 64),
            BitVecVal(byte, 8),
        )
    return state


def _whole_contract_state() -> SMTState:
    state = SMTState.create_initial_state(
        calldata_size_max_bytes=GO_AMD64_MAX_SLICE_LEN,
    )
    state.abstract_calldataload_words = True
    return state


def _verify_contract(
    evm_program: EVMProgram,
    x86_program: X86Program,
    initial_state: SMTState,
) -> tuple[bool, str | None]:
    checker = ProgramEquivalenceChecker(timeout_ms=1_200_000, verbose=False)
    return checker.verify_program_pair(
        evm_program,
        x86_program,
        initial_state,
        stack_check=None,
        path_observations=True,
        path_pair_workers=4,
        enable_merge=False,
        summary_config=TRUSTED_SUMMARY_CONFIG,
        x86_reachability_timeout_ms=250,
        # CFG 更深，默认 max_depth 会触发 depth-pruned coverage-incomplete
        max_depth=100_000,
    )

@pytest.mark.skip(reason="时间太长，暂时禁用")
def test_verify_ext_ens_registry_whole_contract():
    """Verify the whole ENSRegistry fixture with symbolic calldata and size."""
    evm_program, x86_program = _load_ext_contract_pair("ens_registry", "ENSRegistry")
    initial_state = _whole_contract_state()

    verified, msg = _verify_contract(evm_program, x86_program, initial_state)

    assert verified, f"ENSRegistry whole-contract fixture check failed: {msg}"
    assert x86_program.last_summary_stats["calldataload"]["hits"] >= 1


def test_verify_ext_compound_cerc20_decimals_selector():
    """Verify CErc20.decimals() without entering the generated string loops."""
    evm_program, x86_program = _load_ext_contract_pair("compound_cerc20", "CErc20")
    initial_state = _selector_state(0x313CE567, calldata_size=4)  # decimals()

    verified, msg = _verify_contract(evm_program, x86_program, initial_state)

    assert verified, f"CErc20 decimals() fixture check failed: {msg}"
    assert x86_program.last_summary_stats["calldataload"]["hits"] >= 1
