#!/usr/bin/env python3
"""Program-level terminal path observation API tests."""

import threading

import x86_64.program as x86_program_module
from common.path_observation import PathObservation
from evm_ir.json_parser import CompilerEVMResult
from evm_ir.models import EVMBlock, EvmOperator
from evm_ir.program import EVMProgram
from state.smt_state import SMTState
from verification.refinement_checker import RefinementChecker, _PathPairChunkCheckResult
from x86_64.models import X86Block, X86Instruction
from x86_64.program import X86Program
from z3 import BitVec, BitVecVal, BoolVal


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


def test_refinement_checker_can_check_path_pairs_in_parallel():
    state = SMTState.create_initial_state()
    selector = BitVec("parallel_path_selector", 1)
    evm_observations = [
        PathObservation(
            condition=selector == BitVecVal(0, 1),
            offset=BitVecVal(0, 64),
            length=BitVecVal(0, 64),
            memory=state.evm_memory.Memory,
            base_addr=None,
            has_return_data=BoolVal(False),
            storage=state.evm_storage.Storage,
            transient_storage=state.evm_transient_storage.TransientStorage,
        ),
        PathObservation(
            condition=selector == BitVecVal(1, 1),
            offset=BitVecVal(0, 64),
            length=BitVecVal(0, 64),
            memory=state.evm_memory.Memory,
            base_addr=None,
            has_return_data=BoolVal(False),
            storage=state.evm_storage.Storage,
            transient_storage=state.evm_transient_storage.TransientStorage,
        ),
    ]
    x86_observations = [
        PathObservation(
            condition=BoolVal(True),
            offset=BitVecVal(0, 64),
            length=BitVecVal(0, 64),
            memory=state.x86_memory.evm_mem,
            base_addr=BitVecVal(0, 64),
            has_return_data=BoolVal(False),
            storage=state.evm_storage.Storage,
            transient_storage=state.evm_transient_storage.TransientStorage,
        )
    ]

    checker = RefinementChecker(timeout_ms=1000)
    verified, message = checker.check_refinement_paths(
        evm_observations,
        x86_observations,
        path_pair_workers=2,
    )

    assert verified, message
    assert "2/2 feasible pair(s)" in message


def test_parallel_path_pair_check_drains_after_failure_and_cancels_workers(monkeypatch):
    checker = RefinementChecker(timeout_ms=1000)
    cancelled_worker_started = threading.Event()
    cancelled_worker_saw_cancel = threading.Event()

    def fake_check_chunk(pair_specs, _evm_results, _x86_results, _deadline, cancel_event, skip_feasibility=False):
        if pair_specs[0] == (0, 0):
            return _PathPairChunkCheckResult(
                checked_pair_count=1,
                verified=False,
                message="boom",
                logs=["failure worker log"],
            )

        cancelled_worker_started.set()
        assert cancel_event.wait(timeout=1.0)
        cancelled_worker_saw_cancel.set()
        return _PathPairChunkCheckResult(
            checked_pair_count=1,
            verified=True,
            message=None,
            logs=["cancelled worker log"],
        )

    monkeypatch.setattr(checker, "_check_path_pair_chunk", fake_check_chunk)

    checked_pair_count, pair_count, failure = checker._check_path_pairs_parallel(
        evm_results=[object(), object()],
        x86_results=[object(), object()],
        deadline=None,
        path_pair_workers=2,
    )

    assert cancelled_worker_started.is_set()
    assert cancelled_worker_saw_cancel.is_set()
    assert failure == "boom"
    assert pair_count == 4
    assert checked_pair_count == 2
