"""Reverse probes: every success here must carry actual query evidence."""
from dataclasses import replace
from types import SimpleNamespace

import pytest
from z3 import And, BitVecVal, Bool, BoolVal, Not, Or, Store, unknown

import verification.block_equivalence as blocks
from verification.block_relation import BlockRelationSchema
from verification.block_specialization import BlockSpecialization
from verification.loop_induction import SegmentPath
from evm_ir.models import EVMBlock
from x86_64.models import X86Block, Register

SPEC = BlockSpecialization(0, 0, 0, 0)


def prover(monkeypatch, ep=None, xp=None):
    def outcomes(state, side):
        s = state.copy()
        s.error_code = BitVecVal(2, 8)
        s.callengine_status_code = BitVecVal(2, 8)
        return [SegmentPath("terminal", 0, And(*(s.assumptions or [])), s)]
    def run_e(_b, state, _entry, stops, **kwargs):
        assert 0 in stops
        return (ep(state) if ep else outcomes(state, "evm")), []
    def run_x(_b, state, _entry, stops, **kwargs):
        assert 100 in stops
        return (xp(state) if xp else outcomes(state, "x86")), [], []
    monkeypatch.setattr(blocks, "run_evm_segment", run_e)
    monkeypatch.setattr(blocks, "run_x86_segment", run_x)
    return blocks.BlockEquivalenceProver([EVMBlock.from_json({"pc": 0})],
        [X86Block(100, 101)], {0: 100}, timeout_ms=1000)


def test_plain_status_is_not_a_certificate():
    assert not blocks.BlockProofResult(SPEC, status="proved").proved


def test_complete_terminal_proof_and_missing_obligation(monkeypatch):
    r = prover(monkeypatch).prove(SPEC)
    assert r.proved, r.reasons
    assert r.queries >= 5
    r.theorem = replace(r.theorem, obligations=r.theorem.obligations[:-1])
    r._issuer._issued_theorems.append(r.theorem)
    assert not r.proved


def test_cross_kind_guard_swap_rejected_with_complete_coverage(monkeypatch):
    c = Bool("choice")
    def ep(s):
        return [SegmentPath("exit", 0, c, s.copy()), SegmentPath("terminal", 0, Not(c), s.copy())]
    def xp(s):
        return [SegmentPath("exit", 100, Not(c), s.copy()), SegmentPath("terminal", 100, c, s.copy())]
    r = prover(monkeypatch, ep, xp).prove(SPEC)
    assert not r.proved and "outcome mismatch" in str(r.reasons)


@pytest.mark.parametrize("mutation", ["status", "gas", "storage", "transient", "return", "length"])
def test_terminal_one_sided_mutations(monkeypatch, mutation):
    def xp(s):
        s = s.copy()
        s.callengine_status_code = BitVecVal(2, 8)
        if mutation == "status": s.callengine_status_code = BitVecVal(255, 8)
        if mutation == "gas": s.callengine_gas_remaining += 1
        if mutation == "storage": s.evm_storage.Storage = Store(s.evm_storage.Storage, BitVecVal(0, 256), BitVecVal(17, 256))
        if mutation == "transient": s.evm_transient_storage.TransientStorage = Store(s.evm_transient_storage.TransientStorage, BitVecVal(0, 256), BitVecVal(17, 256))
        if mutation == "return": s.return_offset = BitVecVal(1, 64)
        if mutation == "length": s.return_length = BitVecVal(1, 64)
        return [SegmentPath("terminal", 0, And(*(s.assumptions or [])), s)]
    r = prover(monkeypatch, xp=xp).prove(SPEC)
    assert not r.proved and "outcome mismatch" in str(r.reasons)


@pytest.mark.parametrize("defect", ["empty", "unclassified", "missing_guard", "assumption", "pending", "missing_field"])
def test_incomplete_evidence_fails_closed(monkeypatch, defect):
    def xp(s):
        if defect == "empty": return []
        s = s.copy()
        s.callengine_status_code = BitVecVal(2, 8)
        guard, kind = BoolVal(True), "terminal"
        if defect == "unclassified": kind = "mystery"
        if defect == "missing_guard": guard = Bool("only_one_branch")
        if defect == "assumption": s.add_assumption(Bool("unproved_input_filter"))
        if defect == "pending": s.pending_constraints.append(BoolVal(True))
        if defect == "missing_field": s.return_offset = None
        return [SegmentPath(kind, 0, guard, s)]
    assert not prover(monkeypatch, xp=xp).prove(SPEC).proved


def test_unknown_and_executor_exception(monkeypatch):
    p = prover(monkeypatch)
    monkeypatch.setattr(blocks, "_solver", lambda *_: SimpleNamespace(add=lambda *_: None, check=lambda: unknown))
    assert not p.prove(SPEC).proved


def test_pre_tag_r14_and_flags_are_arbitrary():
    from z3 import Solver, sat
    schema = BlockRelationSchema()
    c = schema.build_havoc(0, memory_size=0, free_memory_pointer=0)
    s = Solver()
    s.add(*(c.state.assumptions or []))
    s.add(c.state.x86_registers.get_register(Register.R14) != c.state.callengine_stack_base)
    s.add(c.state.x86_registers.get_flag("CF") == 1)
    assert s.check() == sat


@pytest.mark.parametrize("triple", [(-1, 0, 0), (1025, 0, 0), (0, -32, 0), (0, 1, 0), (0, 1 << 64, 0), (0, 0, -1), (0, 0, 1 << 256)])
def test_invalid_specializations_do_not_wrap(triple):
    with pytest.raises(ValueError): BlockSpecialization(0, *triple)


def test_jump_candidates_cannot_hide_a_legal_source_successor():
    from z3 import Solver, sat, unsat
    from verification.loop_induction import run_evm_segment
    blocks = [EVMBlock.from_json(d) for d in (
        dict(pc=0, stack_depth=-1, min_depth=1, max_depth=1024, operations=[
            dict(kind="TAG", pc=0), dict(kind="BLOCKEND", pc=1),
            dict(kind="JUMP", pc=1, is_static=False, immediate_set=[10])]),
        dict(pc=10, is_jump_target=True, operations=[dict(kind="STOP", pc=10)]),
        dict(pc=20, is_jump_target=True, operations=[dict(kind="STOP", pc=20)]))]
    context = BlockRelationSchema().build_havoc(1, memory_size=0, free_memory_pointer=0)
    paths, defects = run_evm_segment(blocks, context.state.copy(), 0, {0, 10, 20})
    assert not defects
    assert {p.location for p in paths if p.kind != "terminal"} == {10, 20}
    solver = Solver()
    solver.add(*(context.state.assumptions or []))
    solver.add(Not(Or(*(p.condition for p in paths))))
    assert solver.check() == unsat


def test_havoc_scratch_cannot_be_a_default_constant(monkeypatch):
    def xp(s):
        s = s.copy()
        s.callengine_status_code = BitVecVal(2, 8)
        s.callengine_gas_remaining = s.x86_registers.get_register(Register.RAX)
        return [SegmentPath("terminal", 0, And(*(s.assumptions or [])), s)]
    assert not prover(monkeypatch, xp=xp).prove(SPEC).proved
