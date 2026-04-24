#!/usr/bin/env python3
"""程序级 merge 应保留调试用栈元数据。"""

from z3 import BoolVal

from evm_ir.cfg_state import GlobalState
from evm_ir.json_parser import CompilerEVMResult
from evm_ir.program import EVMProgram
from state.smt_state import SMTState
from x86_64.cfg_state import X86GlobalState
from x86_64.program import X86Program


def test_evm_program_merge_preserves_stack_debug_metadata():
    program = EVMProgram(CompilerEVMResult(blocks=[]))
    base_state = SMTState.create_initial_state(2)

    state_a = GlobalState(base_state.copy())
    state_b = GlobalState(base_state.copy())
    state_a.add_constraint(BoolVal(True))
    state_b.add_constraint(BoolVal(False))

    merged = program._merge_global_states([state_a, state_b])

    assert merged.stack_base is base_state.stack_base
    assert merged.stack_num_inputs == 2


def test_x86_program_merge_preserves_stack_debug_metadata():
    program = X86Program()
    base_state = SMTState.create_initial_state(2)

    state_a = X86GlobalState(base_state.copy())
    state_b = X86GlobalState(base_state.copy())
    state_a.add_constraint(BoolVal(True))
    state_b.add_constraint(BoolVal(False))

    merged = program._merge_global_states([state_a, state_b])

    assert merged.stack_base is base_state.stack_base
    assert merged.stack_num_inputs == 2
