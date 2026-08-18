"""Tests for single-instruction equivalence helper rewrites."""

from z3 import BitVec, BitVecVal, BoolVal, Concat, Extract, If, Solver, simplify, unsat

from state.smt_state import MemoryDomain, SMTState
from tests.support import instruction_equivalence as equivalence
from tests.support.instruction_equivalence import (
    InstructionEquivalenceCase,
    _initialize_evm_readonly_sources,
    _initialize_x86_readonly_sources,
    _normalize_equivalence_bv,
)


def _empty_readonly_words():
    return {"calldata": [], "code": [], "return_data": []}


def _minimal_case(**kwargs):
    return InstructionEquivalenceCase(
        name="TEST",
        evm_kind="CALLDATALOAD",
        arity=1,
        x86_core_hex="",
        base_addr=0,
        **kwargs,
    )


def _bytewise_zero_ite_concat(condition, source, high=255, low=0):
    return Concat(
        *[
            If(condition, BitVecVal(0, 8), Extract(offset + 7, offset, source))
            for offset in range(high - 7, low - 1, -8)
        ]
    )


def test_normalize_equivalence_bv_folds_bytewise_zero_ite_concat():
    source = BitVec("source", 512)
    condition = BitVec("condition", 1) == BitVecVal(1, 1)

    normalized = _normalize_equivalence_bv(_bytewise_zero_ite_concat(condition, source))
    expected = If(condition, BitVecVal(0, 256), Extract(255, 0, source))

    solver = Solver()
    solver.add(normalized != expected)
    assert solver.check() == unsat


def test_normalize_equivalence_bv_rejects_mixed_conditions():
    source = BitVec("source", 16)
    condition_a = BitVec("condition_a", 1) == BitVecVal(1, 1)
    condition_b = BitVec("condition_b", 1) == BitVecVal(1, 1)
    expr = Concat(
        If(condition_a, BitVecVal(0, 8), Extract(15, 8, source)),
        If(condition_b, BitVecVal(0, 8), Extract(7, 0, source)),
    )

    assert _normalize_equivalence_bv(expr).eq(simplify(expr))


def test_normalize_equivalence_bv_rejects_mixed_sources():
    source_a = BitVec("source_a", 16)
    source_b = BitVec("source_b", 16)
    condition = BitVec("condition", 1) == BitVecVal(1, 1)
    expr = Concat(
        If(condition, BitVecVal(0, 8), Extract(15, 8, source_a)),
        If(condition, BitVecVal(0, 8), Extract(7, 0, source_b)),
    )

    assert _normalize_equivalence_bv(expr).eq(simplify(expr))


def test_normalize_equivalence_bv_rejects_non_contiguous_extracts():
    source = BitVec("source", 24)
    condition = BitVec("condition", 1) == BitVecVal(1, 1)
    expr = Concat(
        If(condition, BitVecVal(0, 8), Extract(23, 16, source)),
        If(condition, BitVecVal(0, 8), Extract(7, 0, source)),
    )

    assert _normalize_equivalence_bv(expr).eq(simplify(expr))


def test_rewrite_stack_outputs_under_path_prunes_implied_large_bv_ite():
    source = BitVec("path_rewrite_source", 256)
    guard = Extract(7, 0, source) == BitVecVal(0, 8)
    expr = If(guard, BitVecVal(1, 256), BitVecVal(2, 256))

    evm_stack, x86_stack = equivalence._rewrite_stack_outputs_under_path(
        (expr,),
        (expr,),
        source == BitVecVal(0, 256),
        (),
        (),
    )

    assert evm_stack[0].eq(BitVecVal(1, 256))
    assert x86_stack[0].eq(BitVecVal(1, 256))


def test_rewrite_stack_outputs_under_path_keeps_unproved_large_bv_ite():
    source = BitVec("path_rewrite_unproved_source", 256)
    guard = source == BitVecVal(0, 256)
    expr = If(guard, BitVecVal(1, 256), BitVecVal(2, 256))

    evm_stack, x86_stack = equivalence._rewrite_stack_outputs_under_path(
        (expr,),
        (expr,),
        BoolVal(True),
        (),
        (),
    )

    assert evm_stack[0].eq(expr)
    assert x86_stack[0].eq(expr)


def test_instruction_equivalence_evm_uses_symbolic_calldata_size_when_unfixed():
    state = SMTState()
    case = _minimal_case(calldata_size_bytes=None)

    _initialize_evm_readonly_sources(state, case, _empty_readonly_words())

    solver = Solver()
    solver.add(state.callengine_input_size_bytes != state.calldatasize)
    assert solver.check() == unsat


def test_instruction_equivalence_x86_stores_symbolic_calldata_size_when_unfixed():
    state = SMTState()
    case = _minimal_case(calldata_size_bytes=None)

    _initialize_x86_readonly_sources(state, case, _empty_readonly_words())

    input_size_field = state.x86_memory.load_limb(
        BitVecVal(0x98, 64),
        domain=MemoryDomain.CALLENGINE,
    )

    solver = Solver()
    solver.add(state.callengine_input_size_bytes != state.calldatasize)
    assert solver.check() == unsat

    solver = Solver()
    solver.add(input_size_field != state.calldatasize)
    assert solver.check() == unsat


def test_instruction_equivalence_cfg_uses_merged_state_by_default(monkeypatch):
    case = _minimal_case(
        expected_stack_height=0,
        x86_execution_mode="cfg",
    )
    calls = []

    monkeypatch.setattr(equivalence, "_build_evm_final_state", lambda *_args: object())
    monkeypatch.setattr(equivalence, "_build_x86_final_state", lambda *_args: object())
    monkeypatch.setattr(
        equivalence,
        "_build_x86_final_global_states",
        lambda *_args: (_ for _ in ()).throw(AssertionError("unexpected terminal-path branch")),
    )

    def _merged_mismatches(*_args):
        calls.append("merged")
        return [BoolVal(False)]

    monkeypatch.setattr(equivalence, "_state_observation_mismatches", _merged_mismatches)
    monkeypatch.setattr(
        equivalence,
        "_path_observation_mismatches",
        lambda *_args: (_ for _ in ()).throw(AssertionError("unexpected path mismatches")),
    )

    equivalence.assert_instruction_equivalent(case)

    assert calls == ["merged"]


def test_instruction_equivalence_cfg_can_compare_terminal_paths(monkeypatch):
    case = _minimal_case(
        expected_stack_height=0,
        x86_execution_mode="cfg",
        x86_compare_terminal_paths=True,
    )
    calls = []

    monkeypatch.setattr(equivalence, "_build_evm_final_state", lambda *_args: object())
    monkeypatch.setattr(
        equivalence,
        "_build_x86_final_state",
        lambda *_args: (_ for _ in ()).throw(AssertionError("unexpected merged-state branch")),
    )
    monkeypatch.setattr(equivalence, "_build_x86_final_global_states", lambda *_args: ["path"])

    def _path_mismatches(*_args):
        calls.append("paths")
        return [BoolVal(False)]

    monkeypatch.setattr(equivalence, "_path_observation_mismatches", _path_mismatches)
    monkeypatch.setattr(
        equivalence,
        "_state_observation_mismatches",
        lambda *_args: (_ for _ in ()).throw(AssertionError("unexpected merged mismatches")),
    )

    equivalence.assert_instruction_equivalent(case)

    assert calls == ["paths"]
