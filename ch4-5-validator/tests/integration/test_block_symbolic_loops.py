"""Compiler-produced loops: no bound on the number of EVM loop iterations."""
from dataclasses import replace

import pytest
from z3 import And, Not, Or, Solver, BitVecVal, sat

from tests.integration.test_block_program import load
from verification.block_program import BlockProgramVerifier
from verification.block_relation import BlockRelationSchema
from verification.block_specialization import BlockSpecialization
from verification.program_verifier import GasCheck


@pytest.mark.parametrize("name", ["lockstep_counter_loop", "lockstep_fmp_loop", "lockstep_calldata_loop", "lockstep_return_loop", "lockstep_storage_loop"])
@pytest.mark.parametrize("mode", [GasCheck.FIXED_BUDGET, GasCheck.FULL])
def test_compiler_generated_unbounded_loops_have_complete_certificates(name, mode):
    r = BlockProgramVerifier(gas_check=mode, timeout_ms=10000, max_depth=100,
                             wall_timeout_seconds=180).verify_program_pair(*load(name, mode))
    assert r.verified, r.message
    assert r.certificate.entry.edges
    assert any(e.source.pc == e.target_pc or e.source.pc > e.target_pc for e in r.certificate.edges)
    assert all(e.obligation.proved for e in r.certificate.edges)
    if name == "lockstep_fmp_loop":
        assert any(s.memory_size is None and s.free_memory_pointer is None
                   for s in r.certificate.specializations)
    if name == "lockstep_return_loop":
        assert any(s.stack_constants == ((0, 0),) for s in r.certificate.specializations)
    if name == "lockstep_calldata_loop":
        # Both normal RETURN and OOG are actually checked in local theorems.
        assert sum(n.terminals_proved for n in r.nodes) > 0


def test_symbolic_havoc_has_multiple_memory_parameters():
    c = BlockRelationSchema().build_havoc(0, memory_size=None, free_memory_pointer=None)
    from verification.cutpoint_relation import read_evm_memory_word
    for m, f in [(0, 0), (96, 128), (4096, 1 << 255)]:
        solver = Solver()
        solver.add(*c.state.assumptions, c.state.evm_memory.MSize == m,
                   read_evm_memory_word(c.state, 0x40) == f)
        assert solver.check() == sat


def test_local_failure_does_not_skip_another_queued_instance(monkeypatch):
    import verification.block_equivalence as be
    original = be.BlockEquivalenceProver.prove
    def fail_first(self, spec):
        if spec.memory_size == 0:
            return be.BlockProofResult.inconclusive(spec, "injected local failure")
        return original(self, spec)
    monkeypatch.setattr(be.BlockEquivalenceProver, "prove", fail_first)
    proposals = {0: (BlockSpecialization(0, 0, 0, 0), BlockSpecialization(0, 0, 96, 128))}
    r = BlockProgramVerifier(timeout_ms=3000).verify_program_pair(*load("mstore_return"), candidates=proposals)
    assert not r.verified and r.certificate is None
    assert len(r.nodes) == 2 and not r.nodes[0].proved and r.nodes[1].proved
    assert len(r.diagnostics[0]["instances"]) == 2
    assert any(c["phase"] == "final" for c in r.closure_checks)


def test_symbolic_successor_still_checks_memory_equality(monkeypatch):
    import verification.block_equivalence as be
    from state.x86_state import MemoryDomain
    from x86_64.models import Register
    original = be.run_x86_segment
    def corrupt(*args, **kwargs):
        paths, defects, notes = original(*args, **kwargs)
        for p in paths:
            if p.kind != "terminal":
                r15 = p.state.x86_registers.get_register(Register.R15)
                p.state.x86_memory = p.state.x86_memory.store_byte(
                    r15 + 0x40, BitVecVal(0xff, 8), domain=MemoryDomain.EVM)
        return paths, defects, notes
    monkeypatch.setattr(be, "run_x86_segment", corrupt)
    r = BlockProgramVerifier(gas_check=GasCheck.FULL, timeout_ms=5000).verify_program_pair(
        *load("lockstep_fmp_loop", GasCheck.FULL))
    assert not r.verified and "H2" in r.message
    assert any(s.spec.free_memory_pointer is None for s in r.nodes)


def test_obligation_manifest_does_not_follow_deleted_query_records(monkeypatch):
    import verification.block_equivalence as be
    original = be.BlockEquivalenceProver.check_paths
    def omit(self, evm, x86, premise, initial, records):
        # Whichever route proved it (_check, the quick exact query, the prefix tree), drop the record.
        out = original(self, evm, x86, premise, initial, records)
        records[:] = [r for r in records if r.name != "x86_coverage"]
        return out
    monkeypatch.setattr(be.BlockEquivalenceProver, "check_paths", omit)
    r = BlockProgramVerifier(timeout_ms=3000).verify_program_pair(*load("lockstep_counter_loop"))
    assert not r.verified


def test_return_tag_predicate_is_checked_at_actual_arrival():
    # Both node relations are satisfiable, but the caller supplies tag 0, not 6.
    candidates = {
        0: (BlockSpecialization(0, 0, 0, 0),),
        6: (BlockSpecialization(6, 1, 0, 0, ((0, 6),)),),
    }
    r = BlockProgramVerifier(timeout_ms=3000).verify_program_pair(
        *load("lockstep_return_loop"), candidates=candidates)
    assert not r.verified and "H2" in r.message
    assert any(c["phase"] == "final" and c["answer"] == "sat" for c in r.closure_checks)


def test_return_tag_predicate_havoc_binds_both_views():
    from verification.cutpoint_relation import read_x86_stack_slot
    from z3 import unsat
    c = BlockRelationSchema().build_havoc(3, memory_size=None,
        free_memory_pointer=None, stack_constants=((0, 17), (2, 23)))
    for index, value in ((0, 17), (2, 23)):
        solver = Solver()
        solver.add(*c.state.assumptions, Or(c.state.evm_stack.peek(index) != value,
                   read_x86_stack_slot(c.state, index) != value))
        assert solver.check() == unsat


@pytest.mark.parametrize("constants", [((1, 0),), ((0, -1),), ((0, 1 << 256),),
                                       ((0, 0), (0, 1)), ((True, 0),)])
def test_malformed_stack_predicates_rejected(constants):
    with pytest.raises(ValueError):
        BlockSpecialization(0, 1, None, None, constants)


def test_node_budget_expiry_continues_queue_and_restores_program_deadline(monkeypatch):
    import verification.block_equivalence as be
    from time import monotonic
    clock = [monotonic()]
    original = be.run_evm_segment
    calls = []
    def slow_first(*args, **kwargs):
        result = original(*args, **kwargs)
        calls.append(True)
        if len(calls) == 1:
            clock[0] += 11
        return result
    monkeypatch.setattr(be, "monotonic", lambda: clock[0])
    monkeypatch.setattr(be, "run_evm_segment", slow_first)
    candidates = {0: (BlockSpecialization(0, 0, 0, 0), BlockSpecialization(0, 0, 96, 128))}
    r = BlockProgramVerifier(timeout_ms=3000, node_timeout_seconds=10).verify_program_pair(
        *load("mstore_return"), candidates=candidates)
    assert not r.verified
    assert len(r.nodes) == 2 and r.nodes[1].proved
    assert "wall budget exhausted" in str(r.nodes[0].reasons)
    assert r._prover.deadline > clock[0] + 10


def test_loop_storage_corruption_is_rejected_by_edge_closure(monkeypatch):
    import verification.block_equivalence as be
    from z3 import Store, Select
    original = be.run_x86_segment
    def corrupt(*args, **kwargs):
        paths, defects, notes = original(*args, **kwargs)
        for path in paths:
            if path.kind != "terminal":
                storage = path.state.evm_storage.Storage
                key = BitVecVal(0, 256)
                path.state.evm_storage.Storage = Store(storage, key, Select(storage, key) + 1)
        return paths, defects, notes
    monkeypatch.setattr(be, "run_x86_segment", corrupt)
    r = BlockProgramVerifier(gas_check=GasCheck.FULL, timeout_ms=5000).verify_program_pair(
        *load("lockstep_storage_loop", GasCheck.FULL))
    assert not r.verified and "H2" in r.message
