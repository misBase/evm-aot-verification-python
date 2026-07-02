#!/usr/bin/env python3
"""ProgramEquivalenceChecker 的 timeout 预算拆分回归测试。"""

from z3 import BitVecVal, BoolVal

from common.path_observation import PathObservation, PathSemantics
import verification.program_verifier as program_verifier_module
from state.smt_state import SMTState
from verification.program_verifier import ProgramEquivalenceChecker


class _DummyEVMProgram:
    def to_z3(self, state, **_kwargs):
        return state, {
            'offset': BitVecVal(0, 64),
            'length': BitVecVal(0, 64),
            'memory': state.evm_memory.Memory,
            'base_addr': None,
            'has_return_data': BoolVal(False),
            'storage': state.evm_storage.Storage,
            'transient_storage': state.evm_transient_storage.TransientStorage,
        }

    def to_z3_paths(self, state, merge_state=False, **_kwargs):
        return PathSemantics(
            global_states=[],
            observations=[
                PathObservation(
                    condition=BoolVal(True),
                    offset=BitVecVal(0, 64),
                    length=BitVecVal(0, 64),
                    memory=state.evm_memory.Memory,
                    base_addr=None,
                    has_return_data=BoolVal(False),
                    storage=state.evm_storage.Storage,
                    transient_storage=state.evm_transient_storage.TransientStorage,
                )
            ],
            merged_state=state if merge_state else None,
        )


class _DummyX86Program:
    def to_z3(self, state, call_site_mapping=None, **_kwargs):
        return state, {
            'offset': BitVecVal(0, 64),
            'length': BitVecVal(0, 64),
            'memory': state.x86_memory.evm_mem,
            'base_addr': BitVecVal(0, 64),
            'has_return_data': BoolVal(False),
            'storage': state.evm_storage.Storage,
            'transient_storage': state.evm_transient_storage.TransientStorage,
        }

    def to_z3_paths(self, state, call_site_mapping=None, merge_state=False, **_kwargs):
        return PathSemantics(
            global_states=[],
            observations=[
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
            ],
            merged_state=state if merge_state else None,
        )


def test_verify_program_pair_forwards_max_depth_to_evm_and_x86_to_z3(monkeypatch):
    """verify_program_pair 的 max_depth 必须能透传到两侧 to_z3，
    否则任一侧默认值回退成保守值后，大合约验证无法通过显式传参绕开
    coverage-incomplete。"""
    checker = ProgramEquivalenceChecker(timeout_ms=123, verbose=False)
    initial_state = SMTState.create_initial_state()
    evm_program = _DummyEVMProgram()
    x86_program = _DummyX86Program()
    captured = {}

    def _capturing_evm_to_z3(state, **kwargs):
        captured["evm_max_depth"] = kwargs.get("max_depth")
        return evm_program.__class__.to_z3(evm_program, state, **kwargs)

    def _capturing_x86_to_z3(state, call_site_mapping=None, **kwargs):
        captured["x86_max_depth"] = kwargs.get("max_depth")
        return x86_program.__class__.to_z3(x86_program, state, call_site_mapping=call_site_mapping, **kwargs)

    monkeypatch.setattr(evm_program, "to_z3", _capturing_evm_to_z3)
    monkeypatch.setattr(x86_program, "to_z3", _capturing_x86_to_z3)
    monkeypatch.setattr(program_verifier_module, "build_call_site_mapping", lambda *_args, **_kwargs: {})
    monkeypatch.setattr(
        checker.refinement_checker,
        "check_refinement",
        lambda _evm_result, _x86_result, **_kwargs: (True, "ok"),
    )

    verified, msg = checker.verify_program_pair(
        evm_program,
        x86_program,
        initial_state,
        max_depth=12345,
    )

    assert verified
    assert captured["evm_max_depth"] == 12345
    assert captured["x86_max_depth"] == 12345


def test_verify_program_pair_forwards_max_depth_to_evm_and_x86_to_z3_paths(monkeypatch):
    """path_observations=True 分支同样必须透传 max_depth 到两侧 to_z3_paths。"""
    checker = ProgramEquivalenceChecker(timeout_ms=123, verbose=False)
    initial_state = SMTState.create_initial_state()
    evm_program = _DummyEVMProgram()
    x86_program = _DummyX86Program()
    captured = {}

    def _capturing_evm_to_z3_paths(state, merge_state=False, **kwargs):
        captured["evm_max_depth"] = kwargs.get("max_depth")
        return evm_program.__class__.to_z3_paths(
            evm_program, state, merge_state=merge_state, **kwargs
        )

    def _capturing_x86_to_z3_paths(state, call_site_mapping=None, merge_state=False, **kwargs):
        captured["x86_max_depth"] = kwargs.get("max_depth")
        return x86_program.__class__.to_z3_paths(
            x86_program, state, call_site_mapping=call_site_mapping, merge_state=merge_state, **kwargs
        )

    monkeypatch.setattr(evm_program, "to_z3_paths", _capturing_evm_to_z3_paths)
    monkeypatch.setattr(x86_program, "to_z3_paths", _capturing_x86_to_z3_paths)
    monkeypatch.setattr(program_verifier_module, "build_call_site_mapping", lambda *_args, **_kwargs: {})
    monkeypatch.setattr(
        checker.refinement_checker,
        "check_refinement_paths",
        lambda _evm_results, _x86_results, **_kwargs: (True, "ok"),
    )

    verified, msg = checker.verify_program_pair(
        evm_program,
        x86_program,
        initial_state,
        path_observations=True,
        max_depth=54321,
    )

    assert verified
    assert captured["evm_max_depth"] == 54321
    assert captured["x86_max_depth"] == 54321


def test_verify_program_pair_uses_independent_stack_check_budget(monkeypatch):
    checker = ProgramEquivalenceChecker(timeout_ms=123, verbose=False)
    initial_state = SMTState.create_initial_state()
    evm_program = _DummyEVMProgram()
    x86_program = _DummyX86Program()
    captured = {}

    monkeypatch.setattr(program_verifier_module, "build_call_site_mapping", lambda *_args, **_kwargs: {})
    monkeypatch.setattr(program_verifier_module.time, "time", lambda: 1000.0)
    monkeypatch.setattr(
        checker.refinement_checker,
        "check_refinement",
        lambda _evm_result, _x86_result, **_kwargs: (True, "ok"),
    )

    def _fake_stack_check(_evm_state, _x86_state, _initial_state, n_elements, deadline=None):
        captured["n_elements"] = n_elements
        captured["deadline"] = deadline
        return True, "ok"

    monkeypatch.setattr(checker.refinement_checker, "check_stack_equivalence", _fake_stack_check)

    verified, msg = checker.verify_program_pair(
        evm_program,
        x86_program,
        initial_state,
        stack_check=1,
        stack_check_timeout_ms=456,
    )

    assert verified
    assert msg == "ok"
    assert captured["n_elements"] == 1
    assert captured["deadline"] == 1000.456


def test_verify_program_pair_rewrites_refinement_timeout_message(monkeypatch):
    checker = ProgramEquivalenceChecker(timeout_ms=123, verbose=False)
    initial_state = SMTState.create_initial_state()
    evm_program = _DummyEVMProgram()
    x86_program = _DummyX86Program()

    monkeypatch.setattr(program_verifier_module, "build_call_site_mapping", lambda *_args, **_kwargs: {})
    monkeypatch.setattr(
        checker.refinement_checker,
        "check_refinement",
        lambda _evm_result, _x86_result, **_kwargs: (
            False, checker.refinement_checker._timeout_message(),
        ),
    )

    verified, msg = checker.verify_program_pair(
        evm_program,
        x86_program,
        initial_state,
    )

    assert not verified
    assert msg == "? TIMEOUT: refinement check exceeded overall timeout (123 ms)"


def test_verify_program_pair_rewrites_path_refinement_timeout_message(monkeypatch):
    checker = ProgramEquivalenceChecker(timeout_ms=123, verbose=False)
    initial_state = SMTState.create_initial_state()
    evm_program = _DummyEVMProgram()
    x86_program = _DummyX86Program()

    monkeypatch.setattr(program_verifier_module, "build_call_site_mapping", lambda *_args, **_kwargs: {})
    monkeypatch.setattr(
        checker.refinement_checker,
        "check_refinement_paths",
        lambda _evm_results, _x86_results, **_kwargs: (
            False,
            checker.refinement_checker._timeout_message(),
        ),
    )

    verified, msg = checker.verify_program_pair(
        evm_program,
        x86_program,
        initial_state,
        path_observations=True,
    )

    assert not verified
    assert msg == "? TIMEOUT: refinement check exceeded overall timeout (123 ms)"
