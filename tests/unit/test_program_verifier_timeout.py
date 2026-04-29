#!/usr/bin/env python3
"""ProgramEquivalenceChecker 的 timeout 预算拆分回归测试。"""

from z3 import BitVecVal, BoolVal

import verification.program_verifier as program_verifier_module
from state.smt_state import SMTState
from verification.program_verifier import ProgramEquivalenceChecker


class _DummyEVMProgram:
    def to_z3(self, state):
        return state, {
            'offset': BitVecVal(0, 64),
            'length': BitVecVal(0, 64),
            'memory': state.evm_memory.Memory,
            'base_addr': None,
            'has_return': BoolVal(False),
            'storage': state.evm_storage.Storage,
            'transient_storage': state.evm_transient_storage.TransientStorage,
        }


class _DummyX86Program:
    def to_z3(self, state, call_site_mapping=None):
        return state, {
            'offset': BitVecVal(0, 64),
            'length': BitVecVal(0, 64),
            'memory': state.x86_memory.evm_mem,
            'base_addr': BitVecVal(0, 64),
            'has_return': BoolVal(False),
            'storage': state.evm_storage.Storage,
            'transient_storage': state.evm_transient_storage.TransientStorage,
        }


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
        lambda _evm_result, _x86_result: (True, "ok"),
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
        lambda _evm_result, _x86_result: (False, checker.refinement_checker._timeout_message()),
    )

    verified, msg = checker.verify_program_pair(evm_program, x86_program, initial_state)

    assert not verified
    assert msg == "? TIMEOUT: refinement check exceeded overall timeout (123 ms)"
