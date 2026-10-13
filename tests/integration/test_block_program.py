from dataclasses import replace

import pytest
from z3 import And, BitVecVal, Store

from evm_ir.json_parser import load_ir_from_json
from evm_ir.program import EVMProgram
from state.smt_state import SMTState
from verification.block_program import BlockProgramVerifier
from verification.block_specialization import BlockSpecialization
from verification.program_verifier import GasCheck, ProgramEquivalenceChecker
from x86_64.program import X86Program


def load(name="three_block", gas_check=GasCheck.FIXED_BUDGET):
    evm = EVMProgram(load_ir_from_json(f"tests/data/{name}.json"))
    with open(f"tests/data/{name}.hex") as f:
        x86 = X86Program.from_hex(f.read().strip(), base_addr=0x1000)
    initial = SMTState.create_initial_state(num_inputs=0, symbolic_gas=gas_check == GasCheck.FULL)
    initial.assume_calldata_offset_no_overflow = False
    initial.host_gas_uf_enabled = gas_check != GasCheck.OFF
    return evm, x86, initial


@pytest.mark.parametrize("name", ["three_block", "mstore_return", "gas_sload", "gas_two_sload", "gas_sstore"])
@pytest.mark.parametrize("mode", [GasCheck.FIXED_BUDGET, GasCheck.FULL])
def test_real_programs_have_base_edges_and_closed_graph(name, mode):
    r = BlockProgramVerifier(gas_check=mode, timeout_ms=3000).verify_program_pair(*load(name, mode))
    assert r.verified, r.message
    assert r.certificate.entry.edges
    assert r.certificate.worklist_closed
    assert all(n.proved for n in r.nodes)


@pytest.fixture(scope="module")
def closed():
    r = BlockProgramVerifier(timeout_ms=3000).verify_program_pair(*load())
    assert r.verified, r.message
    assert r.certificate.edges
    return r


@pytest.mark.parametrize("missing", ["base", "edge", "node", "scope", "identity", "progress"])
def test_consumer_rejects_deleted_evidence(closed, missing):
    c = closed.certificate
    if missing == "base": c = replace(c, entry=None)
    if missing == "edge": c = replace(c, edges=c.edges[:-1])
    if missing == "node": c = replace(c, nodes=c.nodes[:-1])
    if missing == "scope": c = replace(c, scope="")
    if missing == "identity": c = replace(c, identity="wrong-program")
    if missing == "progress": c = replace(c, worklist_closed=False)
    changed = replace(closed, certificate=c)
    # Also exercise dependency validation after simulating producer issuance;
    # do not let this test pass only because replace() made an unissued object.
    old = closed._prover._issued_program_certificate
    closed._prover._issued_program_certificate = c
    try:
        assert not changed.verified
    finally:
        closed._prover._issued_program_certificate = old


def test_wrong_initial_specialization_is_not_saved_by_local_success():
    e, x, initial = load("mstore_return")
    candidates = {e.blocks[0].pc: (BlockSpecialization(e.blocks[0].pc, 0, 96, 128),)}
    r = BlockProgramVerifier(timeout_ms=3000).verify_program_pair(e, x, initial, candidates=candidates)
    assert not r.verified and "H0" in r.message


def test_missing_successor_is_rejected(closed):
    e, x, initial = load()
    first = closed.certificate.entry.evm_entry
    candidates = {first: tuple(s for s in closed.certificate.specializations if s.pc == first)}
    r = BlockProgramVerifier(timeout_ms=3000).verify_program_pair(e, x, initial, candidates=candidates)
    assert not r.verified and "H2" in r.message


def test_primary_verifier_uses_same_consumer():
    e, x, initial = load("mstore_return")
    checker = ProgramEquivalenceChecker(timeout_ms=3000, gas_check=GasCheck.FIXED_BUDGET)
    ok, message = checker.verify_program_pair(e, x, initial, proof_mode="block-lockstep")
    assert ok and "closed block lockstep certificate" in message
    ok, message = checker.verify_program_pair(e, x, initial, proof_mode="block-lockstep", block_options={"max_instances": 0})
    assert not ok


def test_empty_initial_domain_not_vacuously_verified():
    from z3 import BoolVal
    e, x, initial = load("mstore_return")
    initial.add_assumption(BoolVal(False))
    r = BlockProgramVerifier(timeout_ms=3000).verify_program_pair(e, x, initial)
    assert not r.verified and "initial domain" in r.message


def test_independent_fallback_is_a_fresh_complete_proof(monkeypatch):
    import verification.block_program as bp
    from verification.block_program import IndependentProgramCertificate
    e, x, initial = load("mstore_return")
    verifier = BlockProgramVerifier(timeout_ms=3000, fallback="full-program")
    baseline = verifier.verify_program_pair(e, x, initial, candidates={})
    assert baseline.verified, baseline.message
    assert isinstance(baseline.certificate, IndependentProgramCertificate)
    assert baseline.block_failure_reasons
    real = bp.run_x86_segment
    def corrupted(*args, **kwargs):
        paths, defects, notes = real(*args, **kwargs)
        for p in paths:
            if p.kind == "terminal":
                p.state.callengine_status_code = BitVecVal(255, 8)
        return paths, defects, notes
    monkeypatch.setattr(bp, "run_x86_segment", corrupted)
    bad = verifier.verify_program_pair(e, x, initial, candidates={})
    assert not bad.verified and "independent rerun" in bad.message


def _self_loop(*, broken_r14=False, internal_spin=False):
    from evm_ir.models import EvmOperator
    e, x, initial = load("mstore_return", GasCheck.FULL)
    block = e.blocks[0]
    block.is_jump_target = True
    block.stack_depth = 0
    block.operations = [EvmOperator.from_json(op, block) for op in (
        {"kind": "TAG", "pc": 0, "param": 1}, {"kind": "BLOCKEND", "pc": 1},
        {"kind": "JUMP", "pc": 1, "is_static": True, "immediate": "0"})]
    code = bytearray(b"".join(bytes(i.bytes) for i in x.instructions))
    # Real fixture TAG ends at 0x37 with jmp +0x33 over the error stubs.
    # Redirect it to the pre-TAG cutpoint; a self-loop is one finite macro step.
    assert code[0x37] == 0xeb
    code[0x38] = 0xfe if internal_spin else (0x0c - 0x39) & 0xff
    x = X86Program.from_hex(code.hex(), base_addr=0x1000)
    return e, x, initial


def test_self_loop_closes_without_unrolling_to_initial_gas():
    e, x, initial = _self_loop()
    r = BlockProgramVerifier(gas_check=GasCheck.FULL, timeout_ms=3000, max_depth=40).verify_program_pair(e, x, initial)
    assert r.verified, r.message
    assert len(r.nodes) == 1 and len(r.certificate.edges) == 1
    assert r.certificate.edges[0].source.pc == r.certificate.edges[0].target_pc


def test_internal_one_sided_spin_is_not_a_finite_macro():
    e, x, initial = _self_loop(internal_spin=True)
    r = BlockProgramVerifier(gas_check=GasCheck.FULL, timeout_ms=1000, max_depth=20).verify_program_pair(e, x, initial)
    assert not r.verified and "coverage incomplete" in r.message


def test_r14_rebuild_mutation_checked_by_actual_semantics(monkeypatch):
    import verification.block_equivalence as be
    e, x, initial = load("mstore_return")
    real = be.run_x86_segment
    def omit_rebuild(blocks, *args, **kwargs):
        import copy
        bad = copy.deepcopy(blocks)
        for b in bad:
            for insn in b.instructions:
                if insn.addr == 0x1030:
                    insn.mnemonic, insn.op_str = "nop", ""
        return real(bad, *args, **kwargs)
    baseline = BlockProgramVerifier(timeout_ms=3000).verify_program_pair(e, x, initial)
    assert baseline.verified, baseline.message
    monkeypatch.setattr(be, "run_x86_segment", omit_rebuild)
    r = BlockProgramVerifier(timeout_ms=1000).verify_program_pair(e, x, initial)
    assert not r.verified
