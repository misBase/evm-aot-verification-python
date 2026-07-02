"""Shared call-site identity mapping for EVM IR and x86 host bridge sites."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, List, Tuple

from evm_ir.program import EVMProgram
from x86_64.cfg import identify_basic_blocks
from x86_64.cfg_executor import X86SymbolicExecutor
from x86_64.program import X86Program


EVM_HOST_OP_KINDS = {
    "SHA3",
    "BALANCE",
    "EXTCODESIZE",
    "EXTCODECOPY",
    "EXTCODEHASH",
    "BLOCKHASH",
    "SELFBALANCE",
    "SLOAD",
    "SSTORE",
    "LOG",
    "CREATE",
    "CALL",
    "CALLCODE",
    "DELEGATECALL",
    "CREATE2",
    "STATICCALL",
    "SELFDESTRUCT",
    "TLOAD",
    "TSTORE",
}

EVM_KIND_TO_HOST_FUNC_NAME = {
    "SHA3": "sha3",
    "BALANCE": "balance",
    "EXTCODESIZE": "extCodeSize",
    "EXTCODECOPY": "extCodeCopy",
    "EXTCODEHASH": "extCodeHash",
    "BLOCKHASH": "blockHash",
    "SELFBALANCE": "selfBalance",
    "SLOAD": "sload",
    "SSTORE": "sstore",
    "LOG": "log",
    "CREATE": "create",
    "CALL": "call",
    "CALLCODE": "callCode",
    "DELEGATECALL": "delegateCall",
    "CREATE2": "create2",
    "STATICCALL": "staticCall",
    "SELFDESTRUCT": "selfDestruct",
    "TLOAD": "tload",
    "TSTORE": "tstore",
}


@dataclass(frozen=True)
class CallSiteInfo:
    """EVM host-call metadata matched to one x86 host bridge site."""

    pc: int
    kind: str
    immediate: int | None = None


@dataclass(frozen=True)
class CallSiteMapping:
    """Maps x86 host-bridge block addresses to corresponding EVM host sites."""

    x86_ret_block_to_evm_site: Dict[int, CallSiteInfo]

    def get_evm_site(self, x86_ret_block_addr: int) -> CallSiteInfo:
        """Return the matched EVM host-call site for a x86 bridge block."""
        try:
            return self.x86_ret_block_to_evm_site[x86_ret_block_addr]
        except KeyError as exc:
            raise KeyError(
                f"missing EVM call-site mapping for x86 ret block 0x{x86_ret_block_addr:x}"
            ) from exc

    def get_evm_pc(self, x86_ret_block_addr: int) -> int:
        """Return the mapped EVM pc for a given x86 host bridge site."""
        return self.get_evm_site(x86_ret_block_addr).pc

    def __len__(self) -> int:
        return len(self.x86_ret_block_to_evm_site)


def build_call_site_mapping(evm_program: EVMProgram, x86_program: X86Program) -> CallSiteMapping:
    """Build a structural mapping from x86 host bridge sites to EVM op.pc values."""
    evm_sites = _enumerate_evm_host_sites(evm_program)
    x86_sites = _enumerate_x86_host_bridge_sites(x86_program)

    if len(evm_sites) != len(x86_sites):
        raise ValueError(
            "host call-site count mismatch: "
            f"EVM has {len(evm_sites)} host ops, x86 has {len(x86_sites)} host bridge sites"
        )

    mapping: Dict[int, CallSiteInfo] = {}
    for (evm_pc, evm_kind, evm_immediate), (x86_addr, x86_func_name) in zip(
        evm_sites,
        x86_sites,
    ):
        expected_func_name = EVM_KIND_TO_HOST_FUNC_NAME.get(evm_kind)
        if expected_func_name is None:
            raise ValueError(f"unsupported EVM host op kind for call-site mapping: {evm_kind}")
        if x86_func_name != expected_func_name:
            raise ValueError(
                "host call-site kind mismatch: "
                f"EVM pc 0x{evm_pc:x} kind {evm_kind} expects x86 host func '{expected_func_name}', "
                f"but x86 block 0x{x86_addr:x} uses '{x86_func_name}'"
            )
        mapping[x86_addr] = CallSiteInfo(evm_pc, evm_kind, evm_immediate)
    return CallSiteMapping(mapping)


def _enumerate_evm_host_sites(
    evm_program: EVMProgram,
) -> List[Tuple[int, str, int | None]]:
    sites: List[Tuple[int, str, int | None]] = []
    for block in evm_program.blocks:
        for op in block.operations:
            if op.kind in EVM_HOST_OP_KINDS:
                sites.append((op.pc, op.kind, op.immediate))
    return sites


def _enumerate_x86_host_bridge_sites(x86_program: X86Program) -> List[Tuple[int, str]]:
    instructions = x86_program._get_instructions()
    if not instructions:
        return []

    blocks = identify_basic_blocks(instructions)
    if not blocks:
        return []

    executor = X86SymbolicExecutor(
        blocks=blocks,
        enable_go_bridge=True,
        enable_merge=False,
        aot_profile=x86_program.aot_profile,
    )
    host_status = executor.aot_profile.status_codes["call_go_host_function"]

    sites: List[Tuple[int, str]] = []
    for block in blocks:
        if not executor._is_call_go_function_pattern(block):
            continue
        if executor._extract_status_code(block) == host_status:
            func_index = executor._extract_function_index(block, host_status)
            if func_index is None:
                raise ValueError(
                    f"missing host func_index for x86 host bridge block 0x{block.start_addr:x}"
                )
            func_name = executor.aot_profile.resolve_host_function_name(func_index)
            if func_name is None:
                raise ValueError(
                    f"unknown host func_index={func_index} at "
                    f"x86 host bridge block 0x{block.start_addr:x}; "
                    "this index is not defined by the active go-hpc-evm host ABI table"
                )
            sites.append((block.start_addr, func_name))
    return sites
