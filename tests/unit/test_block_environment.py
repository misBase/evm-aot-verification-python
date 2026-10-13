"""Symbolic environment binding and one-sided ABI corruption regressions."""
import pytest
from z3 import And, Bool, Extract, Not, Solver, sat, simplify, unsat

from state.smt_state import SMTState
from state.x86_state import MemoryDomain
from verification.block_relation import BlockRelationSchema
from verification.block_specialization import BlockSpecialization
from x86_64.disassembler import disassemble_hex
from x86_64.models import Register


@pytest.mark.parametrize("field,offset", [
    ("block_number", 0x50), ("block_timestamp", 0x58), ("gaslimit", 0x60),
])
@pytest.mark.parametrize("havoc", [False, True])
def test_symbolic_environment_reads_and_mirrors(field, offset, havoc):
    schema = BlockRelationSchema()
    context = schema.build_havoc(0, memory_size=0, free_memory_pointer=0) if havoc else None
    state = context.state if havoc else SMTState.create_initial_state(num_inputs=0)
    original = getattr(state, field)
    # Exercise the full-width fast path and byte-width backing-memory path.
    for code, expected in [(f"498b45{offset:02x}", original),
                           (f"410fb645{offset:02x}", Extract(7, 0, original))]:
        out = disassemble_hex(code, base_addr=0)[0].to_z3(state.copy())
        solver = Solver()
        value = out.x86_registers.get_register(Register.RAX)
        solver.add(Extract(expected.size() - 1, 0, value) != expected)
        assert solver.check() == unsat
    solver = Solver()
    solver.add(*(state.assumptions or []), original == (1 << 64) - 1)
    assert solver.check() == sat  # No concrete context value smuggled in.
    if not havoc:
        return
    spec = BlockSpecialization(0, 0, 0, 0)
    for mutation in ("none", "field", "bytes"):
        out = state.copy()
        if mutation == "field":
            setattr(out, "callengine_" + field, original + 1)
        if mutation == "bytes":
            addr = out.x86_registers.get_register(Register.R13) + offset
            out.x86_memory = out.x86_memory.store_limb(
                addr, original + 1, domain=MemoryDomain.CALLENGINE)
        goals = And(*(g.condition for g in schema.relation_goals(
            state, out, spec, memory_snapshot=context.memory_snapshot)))
        solver = Solver()
        solver.add(*(state.assumptions or []), simplify(Not(goals)))
        assert solver.check() == (unsat if mutation == "none" else sat)


def test_block_environment_machine_writes_survive_copy_and_merge():
    state = SMTState.create_initial_state()
    original = state.block_number
    # mov [r13+0x50], rax must not mutate the EVM environment.
    changed = state.copy()
    changed.x86_registers.set_register(Register.RAX, original + 1)
    changed = disassemble_hex("49894550", base_addr=0)[0].to_z3(changed).copy()
    branch = Bool("changed_block_context")
    merged = state.copy()
    SMTState.merge_callengine_side_channels(merged, [state, changed], [Not(branch), branch])
    solver = Solver()
    solver.add(branch, merged.callengine_block_number != original + 1)
    assert solver.check() == unsat
    assert changed.block_number.eq(original)
