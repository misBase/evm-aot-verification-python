"""Real producer regressions. Local success is not a whole-program claim."""
import pytest
from z3 import BitVecVal, Store

from evm_ir.json_parser import load_ir_from_json
from evm_ir.program import EVMProgram
from tools.tag_align import build_block_alignment
from verification.block_equivalence import BlockEquivalenceProver
from verification.block_partition import split_at_cutpoints
from verification.block_specialization import BlockSpecialization
from x86_64.cfg import identify_basic_blocks
from x86_64.program import X86Program
from state.x86_state import MemoryDomain
from x86_64.models import Register

MSIZE, FMP = 0x60, 0x80
BASE_ADDR = 0x1000


@pytest.fixture(scope="module")
def program():
    evm = sorted(EVMProgram(load_ir_from_json("tests/data/muti_block.json")).blocks, key=lambda b: b.pc)
    with open("tests/data/muti_block.hex") as fh:
        x86p = X86Program.from_hex(fh.read().strip(), base_addr=BASE_ADDR)
    basic_blocks = identify_basic_blocks(x86p.instructions)
    alignment = build_block_alignment(evm, x86p.instructions, basic_blocks)
    return evm, x86p, split_at_cutpoints(basic_blocks, alignment.pc_to_addr.values()), alignment


def test_alignment_and_raw_entry_are_distinct(program):
    evm, x86p, bb, alignment = program
    assert len(alignment) == len(evm) == 40
    assert alignment.non_block_regions
    assert alignment.pc_to_addr[0] != x86p.instructions[0].addr
    assert alignment.pc_to_addr[0] in {b.start_addr for b in bb}
    assert x86p.instructions[0].addr in {b.start_addr for b in bb}


@pytest.mark.parametrize("pc", [0, 13, 120])
def test_real_local_baselines(program, pc):
    evm, _, bb, alignment = program
    # Symbolic partial CALLDATALOAD coverage needs headroom under xdist load.
    # This remains a real UNSAT obligation, not an accepted timeout.
    prover = BlockEquivalenceProver(evm, bb, alignment.pc_to_addr, timeout_ms=10000)
    block = next(b for b in evm if b.pc == pc)
    r = prover.prove(BlockSpecialization(pc, block.min_depth, MSIZE, FMP))
    assert r.proved, r.reasons
    assert r.queries > 0
    if pc == 13:
        assert r.paired_transitions > 1


@pytest.mark.parametrize("field", ["status", "return_bytes", "storage", "transient", "gas"])
def test_real_terminal_producer_mutation(program, monkeypatch, field):
    import verification.block_equivalence as be
    evm, _, bb, alignment = program
    prover = BlockEquivalenceProver(evm, bb, alignment.pc_to_addr, timeout_ms=3000)
    spec = BlockSpecialization(120, 0, MSIZE, FMP)
    baseline = prover.prove(spec)
    assert baseline.proved, baseline.reasons
    original = be.run_x86_segment
    touched = []
    def corrupted(*args, **kwargs):
        paths, defects, notes = original(*args, **kwargs)
        for p in paths:
            if p.kind != "terminal": continue
            s = p.state
            touched.append(p)
            if field == "status": s.callengine_status_code = BitVecVal(255, 8)
            if field == "gas": s.callengine_gas_remaining += 1
            if field == "return_bytes":
                address = s.x86_registers.get_register(Register.R15)
                value = s.x86_memory.load_byte(address, domain=MemoryDomain.EVM)
                s.x86_memory = s.x86_memory.store_byte(address, value + 1, domain=MemoryDomain.EVM)
            if field == "storage":
                old = s.evm_storage.Storage
                s.evm_storage.Storage = Store(old, BitVecVal(0, 256), old[BitVecVal(0, 256)] + 1)
            if field == "transient":
                old = s.evm_transient_storage.TransientStorage
                s.evm_transient_storage.TransientStorage = Store(old, BitVecVal(0, 256), old[BitVecVal(0, 256)] + 1)
        return paths, defects, notes
    monkeypatch.setattr(be, "run_x86_segment", corrupted)
    result = prover.prove(spec)
    assert touched and not result.proved
    assert "outcome mismatch" in str(result.reasons)


def test_unmapped_block_is_rejected(program):
    evm, _, bb, alignment = program
    r = BlockEquivalenceProver(evm, bb, alignment.pc_to_addr).prove(BlockSpecialization(0xDEAD, 0, MSIZE, FMP))
    assert not r.proved
    assert "authoritative mapping" in r.reasons[0]


def test_node_deadline_interrupts_raw_execution_without_a_theorem(program, monkeypatch):
    evm, _, bb, alignment = program
    monkeypatch.setattr("x86_64.cfg_executor.monotonic", lambda: float("inf"))
    prover = BlockEquivalenceProver(evm, bb, alignment.pc_to_addr,
                                    timeout_ms=3000, node_timeout_seconds=30)
    result = prover.prove(BlockSpecialization(120, 0, MSIZE, FMP))
    assert not result.proved and result.theorem is None
    assert "x86 segment execution deadline exhausted" in str(result.reasons)


def test_summary_templates_are_discovered_once_per_program(program, monkeypatch):
    import verification.block_summaries as summaries
    from x86_64.summaries import X86SummaryConfig
    original, calls = summaries.build_x86_summary_runtime, []
    def discover(*args, **kwargs):
        calls.append(True)
        return original(*args, **kwargs)
    monkeypatch.setattr(summaries, "build_x86_summary_runtime", discover)
    evm, _, bb, alignment = program
    prover = BlockEquivalenceProver(evm, bb, alignment.pc_to_addr,
        summary_config=X86SummaryConfig.enabled(calldataload="fallback"))
    first = prover.prove(BlockSpecialization(120, 0, MSIZE, FMP))
    second = prover.prove(BlockSpecialization(120, 0, MSIZE, FMP))
    assert first.proved and second.proved
    assert first.context is not second.context and first.theorem is not second.theorem
    assert len(calls) == 1
