#!/usr/bin/env python3
"""Program-level terminal path observation API tests."""

import threading

import x86_64.program as x86_program_module
from common.path_observation import PathCoverageCertificate, PathObservation
from evm_ir.json_parser import CompilerEVMResult
from evm_ir.models import EVMBlock, EvmOperator
from evm_ir.program import EVMProgram
from state.smt_state import SMTState
from verification.refinement_checker import RefinementChecker, _PathPairChunkCheckResult
from x86_64.cfg import identify_basic_blocks
from x86_64.cfg_executor import X86SymbolicExecutor
from x86_64.disassembler import disassemble_hex
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


def test_path_coverage_is_checked_under_precondition():
    state = SMTState.create_initial_state()
    selector = BitVec("coverage_selector", 1)
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
        )
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
        coverage_precondition=selector == BitVecVal(0, 1),
    )

    assert verified, message


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

    monkeypatch.setattr(checker._paths, "_check_path_pair_chunk", fake_check_chunk)

    checked_pair_count, pair_count, failure = checker._paths._check_path_pairs_parallel(
        evm_results=[object(), object()],
        x86_results=[object(), object()],
        deadline=None,
        path_pair_workers=2,
    )

    assert cancelled_worker_started.is_set()
    assert cancelled_worker_saw_cancel.is_set()
    assert failure == "boom"
    assert pair_count == 4
    assert 2 <= checked_pair_count <= pair_count


def test_path_coverage_accepts_complete_certificate_without_solver(monkeypatch):
    checker = RefinementChecker(timeout_ms=1000)

    def fail_if_called(_deadline):
        raise AssertionError("coverage solver should not run")

    monkeypatch.setattr(
        checker._paths._ctx,
        "reset_solver_with_budget",
        fail_if_called,
    )

    verified, message = checker._paths._check_path_coverage(
        [],
        "x86",
        deadline=None,
        coverage=PathCoverageCertificate.by_construction(
            "unit-test certificate",
            source="test",
        ),
    )

    assert verified
    assert message is None


def test_x86_executor_reports_complete_coverage_for_modeled_branch():
    # xor rax,rax; je +1; ret; ret，两条后继都在本地 CFG 内。
    instructions = disassemble_hex("4831c07401c3c3", base_addr=0)
    blocks = identify_basic_blocks(instructions)
    executor = X86SymbolicExecutor(
        blocks,
        max_depth=10,
        use_reachability_check=False,
    )

    final_states = executor.execute(SMTState.create_initial_state(), entry_addr=0)
    certificate = executor.path_coverage_certificate()

    assert len(final_states) == 2
    assert certificate.complete, certificate.reason


def test_x86_executor_coverage_certificate_fails_closed_for_external_jmp():
    # jmp 0x1000，目标超出本地反汇编范围。
    instructions = disassemble_hex("e9fb0f0000", base_addr=0)
    blocks = identify_basic_blocks(instructions)
    executor = X86SymbolicExecutor(blocks, max_depth=10)

    executor.execute(SMTState.create_initial_state(), entry_addr=0)
    certificate = executor.path_coverage_certificate()

    assert not certificate.complete
    assert "outside the local CFG" in certificate.reason
