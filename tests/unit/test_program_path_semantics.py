#!/usr/bin/env python3
"""Program-level terminal path observation API tests."""

import x86_64.program as x86_program_module
from evm_ir.json_parser import CompilerEVMResult
from evm_ir.models import EVMBlock, EvmOperator
from evm_ir.program import EVMProgram
from state.smt_state import SMTState
from verification.refinement_checker import RefinementChecker
from x86_64.models import X86Block, X86Instruction
from x86_64.program import X86Program


OBSERVATION_KEYS = {
    "condition",
    "offset",
    "length",
    "memory",
    "base_addr",
    "has_return_data",
    "storage",
    "transient_storage",
}


def _stop_evm_program() -> EVMProgram:
    stop = EvmOperator(kind="STOP", pc=0)
    block = EVMBlock(
        pc=0,
        stack_depth=0,
        min_depth=0,
        max_depth=1024,
        static_gas=0,
        is_jump_target=False,
        is_inner_block=False,
        is_stop=True,
        operations=[stop],
    )
    stop.block = block
    return EVMProgram(CompilerEVMResult(blocks=[block]))


def test_evm_program_to_z3_paths_returns_observations_without_merge():
    program = _stop_evm_program()
    state = SMTState.create_initial_state()

    paths = program.to_z3_paths(state, merge_state=False)

    assert len(paths.global_states) == 1
    assert len(paths.observations) == 1
    assert paths.merged_state is None
    assert set(paths.observations[0].as_dict()) == OBSERVATION_KEYS
    assert paths.observations[0].base_addr is None


def test_x86_program_to_z3_paths_empty_fallback_returns_one_observation():
    program = X86Program()
    state = SMTState.create_initial_state()

    paths = program.to_z3_paths(state, merge_state=False)

    assert paths.global_states == []
    assert len(paths.observations) == 1
    assert paths.merged_state is None
    assert set(paths.observations[0].as_dict()) == OBSERVATION_KEYS


def test_x86_program_to_z3_paths_sequential_fallback_returns_one_observation(monkeypatch):
    instruction = X86Instruction(
        addr=0,
        mnemonic="nop",
        op_str="",
        bytes=b"\x90",
        size=1,
    )
    block = X86Block(start_addr=0, end_addr=1, instructions=[instruction])
    program = X86Program.from_blocks([block])
    state = SMTState.create_initial_state()

    monkeypatch.setattr(x86_program_module, "identify_basic_blocks", lambda _instructions: [])
    paths = program.to_z3_paths(state, merge_state=False)

    assert len(paths.global_states) == 1
    assert len(paths.observations) == 1
    assert paths.merged_state is None
    assert set(paths.observations[0].as_dict()) == OBSERVATION_KEYS


def test_to_z3_paths_merge_state_can_feed_stack_check():
    initial_state = SMTState.create_initial_state(num_inputs=1)
    evm_paths = _stop_evm_program().to_z3_paths(initial_state, merge_state=True)
    x86_paths = X86Program().to_z3_paths(initial_state, merge_state=True)

    assert evm_paths.merged_state is not None
    assert x86_paths.merged_state is not None

    checker = RefinementChecker(timeout_ms=1000)
    verified, message = checker.check_stack_equivalence(
        evm_paths.merged_state,
        x86_paths.merged_state,
        initial_state,
        n_elements=1,
    )

    assert verified, message
