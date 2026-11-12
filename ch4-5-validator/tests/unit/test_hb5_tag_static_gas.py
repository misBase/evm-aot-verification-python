"""TAG prepayment regressions; native execution requires the root's test slot."""
import hashlib
import json
import os
from pathlib import Path

import pytest
from z3 import And, BitVec, BitVecVal, Int, IntVal, Not, Or, Solver, ULT, simplify, unsat

from evm_ir.cfg_executor import SymbolicExecutor
from evm_ir.json_parser import load_ir_from_json
from evm_ir.models import EVMBlock, EvmOperator
from evm_ir.status_code import EvmStatusCode as S
from state.evm_gas_state import EVMGasState
from state.evm_stack_state import EVMStackState
from state.smt_state import SMTState


def block(minimum, maximum, static, tag=True):
    result = EVMBlock(pc=0, stack_depth=0, min_depth=minimum, max_depth=maximum,
        static_gas=static, is_jump_target=False, is_inner_block=False, is_stop=True)
    result.operations = ([EvmOperator(kind="TAG", pc=0, block=result)] if tag else [])
    result.operations.append(EvmOperator(kind="STOP", pc=1, block=result))
    return result


def run(current, gas, sp):
    state = SMTState.create_initial_state(symbolic_gas=False, gas_budget=12)
    state.evm_gas = EVMGasState(initial_gas=gas)
    state.callengine_gas_remaining = gas
    state.evm_stack = EVMStackState(sp=sp)
    executor = SymbolicExecutor([current], max_depth=5, use_reachability_check=False)
    return state, executor.execute(state, entry_pc=current.pc)


@pytest.mark.parametrize("minimum,maximum,sp,gas,static,tag,status,remaining", [
    (1, 1024, 0, 12, 9, True, S.STACK_UNDERFLOW, 3),
    (0, 2, 3, 12, 9, True, S.STACK_REACHED_LIMIT, 3),
    (1, 2, 1, 12, 9, True, S.STOPPED, 3),
    (1, 1024, 0, 8, 9, True, S.OUT_OF_GAS, 8),
    (0, 2, 3, 8, 9, True, S.OUT_OF_GAS, 8),
    (1, 1024, 0, 9, 9, True, S.STACK_UNDERFLOW, 0),
    (1, 2, 1, 9, 9, True, S.STOPPED, 0),
    (5, 3, 4, 12, 9, True, S.STACK_UNDERFLOW, 3),
    (1, 1024, 0, 12, 0, True, S.STACK_UNDERFLOW, 12),
    (1, 1024, 0, 12, 9, False, S.STOPPED, 3),
])
def test_tag_prepaid_depth_errors_and_unchanged_other_paths(minimum, maximum, sp, gas, static, tag, status, remaining):
    initial, finals = run(block(minimum, maximum, static, tag), BitVecVal(gas, 64), IntVal(sp))
    assert len(finals) == 1
    terminal = finals[0].mstate
    assert simplify(terminal.error_code).as_long() == int(status)
    assert simplify(terminal.evm_gas.Gas).as_long() == remaining
    assert simplify(initial.evm_gas.Gas).as_long() == gas  # Snapshot charging cannot mutate the caller.


def refute(formula):
    solver = Solver()
    solver.set(timeout=500)
    solver.add(formula)
    assert solver.check() == unsat


def test_symbolic_regions_are_exhaustive_disjoint_and_charge_once():
    gas, sp = BitVec("hb5_tag_gas", 64), Int("hb5_tag_sp")
    initial, finals = run(block(2, 4, 9), gas, sp)
    by_status = {simplify(f.mstate.error_code).as_long(): f for f in finals}
    oog = ULT(gas, BitVecVal(9, 64))
    expected = {int(S.OUT_OF_GAS):oog,
        int(S.STACK_UNDERFLOW):And(Not(oog), sp < 2),
        int(S.STACK_REACHED_LIMIT):And(Not(oog), sp >= 2, sp > 4),
        int(S.STOPPED):And(Not(oog), sp >= 2, sp <= 4)}
    assert set(by_status) == set(expected)
    conditions = []
    for code, final in by_status.items():
        condition = final.get_constraints().as_bool()
        refute(condition != expected[code])
        remaining = gas if code == int(S.OUT_OF_GAS) else gas-BitVecVal(9, 64)
        refute(And(condition, final.mstate.evm_gas.Gas != remaining))
        conditions.append(condition)
    refute(Not(Or(*conditions)))
    for i, condition in enumerate(conditions):
        for other in conditions[i+1:]:
            refute(And(condition, other))
    assert initial.evm_gas.Gas.eq(gas)


def test_real_ir_tag_matches_archived_native_go_and_raw_amd64_reference():
    """The oracle is an earlier native Go run, not a fresh Go compilation here."""
    reference_path = Path(os.environ.get("HB5_NATIVE_REFERENCE", "tests/data/hb5_tag_native_reference.json"))
    reference = json.loads(reference_path.read_text())
    fixture = Path("tests/data/jumpi_2block.json")
    assert hashlib.sha256(fixture.read_bytes()).hexdigest() == reference["fixture_json_sha256"]
    current = next(b for b in load_ir_from_json(str(fixture)).blocks if b.pc == reference["tag_pc"])
    assert current.static_gas == reference["tag_static_gas"] and current.min_depth == 1
    _, finals = run(current, BitVecVal(reference["tag_entry_gas"], 64), IntVal(0))
    assert len(finals) == 1
    terminal = finals[0].mstate
    assert simplify(terminal.error_code).as_long() == int(S.STACK_UNDERFLOW)
    assert simplify(terminal.evm_gas.Gas).as_long() == reference["native_go_remaining_gas"] == reference["raw_amd64_remaining_gas"] == 3
