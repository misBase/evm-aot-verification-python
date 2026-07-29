"""Unit tests: verify IR error_code matches x86 callEngine status_code after instruction execution.

Reuses test case parameters from test_single_ins_refinement, builds both
EVM IR and x86-64 final states, and cross-validates that the error/status
codes are consistent across both sides.
"""

from dataclasses import replace

import pytest

from common.uint256 import Uint256
from evm_ir.json_parser import CompilerEVMResult
from evm_ir.models import EVMBlock, EvmOperator
from evm_ir.program import EVMProgram
from evm_ir.semantics import evm_operator_to_z3
from evm_ir.status_code import EvmStatusCode
from state.smt_state import SMTState
from tests.integration.test_single_ins_refinement import (
    X86_CONTROL_FLOW_GAS_CONTEXT,
    X86_CORE_BASE_ADDR,
    X86_INVALID_CORE_HEX_SEQUENCE,
    X86_RETURN_CORE_HEX_SEQUENCE,
    X86_RETURNDATACOPY_CORE_HEX_SEQUENCE,
    X86_STOP_CORE_HEX_SEQUENCE,
    X86_REVERT_CORE_HEX_SEQUENCE,
    X86_STATUS_CODES,
)
from tests.support.instruction_refinement import (
    InstructionRefinementCase,
    _build_evm_final_state,
    _build_evm_initial_state,
    _build_x86_final_state,
    _operands,
    _symbolic_memory_words,
    _symbolic_readonly_words,
)
from z3 import And, BitVec, BitVecVal, Not, Solver, is_true, sat, simplify, unsat
# ---- Helper: construct concrete code words from bytecode hex ----
def _code_words_from_hex(code_hex: str, num_words: int = 1) -> list[Uint256]:
    """Parse a hex string into num_words Uint256 values (big-endian, zero-padded)."""
    raw = bytes.fromhex(code_hex)
    words = []
    for i in range(num_words):
        start = i * 32
        chunk = raw[start:start + 32] if start < len(raw) else b""
        if len(chunk) < 32:
            chunk = chunk + b"\x00" * (32 - len(chunk))
        words.append(Uint256.from_int(int.from_bytes(chunk, "big")))
    return words


# EVM bytecode matching the IR used to generate x86 hex.
# IR: Block 0 [PUSH1 0x00, PUSH1 0x0a, JUMP], Block 1 [JUMPDEST @ PC 6, STOP]
# Bytecode: 60 00 60 0a 56 00 5b 00
JUMP_INVALID_CODE_HEX = "606000600a56005b00"

# IR: Block 0 [PUSH1 0x01, PUSH1 0x0a, JUMPI], Block 1 [JUMPDEST @ PC 6, STOP]
# Bytecode: 60 01 60 0a 57 00 5b 00
JUMPI_INVALID_CODE_HEX = "606001600a57005b00"


# ---- x86 hex exported from go-hpc-evm (TestExportJumpErrorHex) ----
# Full-program hex for dynamic JUMP/JUMPI to invalid destination.
# 12-byte prologue stripped.
X86_JUMP_INVALID_CORE_HEX_SEQUENCE = (
    "498b45704883f86472234883e86449894570498b45304883f8007222"
    "483d01800000732b4d8b75384901c6eb3341c685e00000000c49c745"
    "2800000000c341c685e00000000e49c7452800000000c341c685e000"
    "00000f49c7452800000000c349c7060000000049c746080000000049"
    "c746100000000049c746180000000049c746200a00000049c7462800"
    "00000049c746300000000049c746380000000048c7c1200000004901"
    "4d3048c7c000000000490b4628490b4630490b46384885c0741141c6"
    "85e00000000849c7452804000000c3498b462049894548eb72498b45"
    "704883f86372244883e86349894570498b4530904883f8207222483d"
    "01800000732b4d8b75384901c6eb3341c685e00000000c49c7452800"
    "000000c341c685e00000000e49c7452800000000c341c685e0000000"
    "0f49c7452800000000c341c685e00000000249c7452800000000c349"
    "8b4548904883f8067483eb0041c685e00000000849c7452800000000c3"
)

X86_JUMPI_INVALID_CORE_HEX_SEQUENCE = (
    "498b45704883f86472234883e86449894570498b45304883f8007222"
    "483d01800000732b4d8b75384901c6eb3341c685e00000000c49c745"
    "2800000000c341c685e00000000e49c7452800000000c341c685e000"
    "00000f49c7452800000000c349c7060100000049c746080000000049"
    "c746100000000049c746180000000049c746200a00000049c7462800"
    "00000049c746300000000049c746380000000048c7c0200000004901"
    "453048c7c000000000490b06490b4608490b4610490b46184885c074"
    "2648c7c000000000490b4628490b4630490b46384885c00f859f0000"
    "00498b462049894548eb7e498b45700f1f4400004883f863722b4883"
    "e86349894570498b45304883f820722a0f1f840000000000483d0180"
    "0000732b4d8b75384901c6eb3341c685e00000000c49c74528000000"
    "00c341c685e00000000e49c7452800000000c341c685e00000000f49"
    "c7452800000000c341c685e00000000249c7452800000000c3498b45"
    "480f1f80000000004883f8060f846dffffffeb0041c685e000000008"
    "49c7452800000000c3"
)


def test_revert_error_code_matches_x86_status_code():
    """Verify REVERT: IR error_code = x86 callEngine status_code = REVERTED."""
    case = InstructionRefinementCase(
        name="REVERT",
        evm_kind="REVERT",
        arity=2,
        x86_core_hex=X86_REVERT_CORE_HEX_SEQUENCE,
        base_addr=X86_CORE_BASE_ADDR,
        operand_values=(32, 0),
        expected_stack_height=0,
        expected_status_code=X86_STATUS_CODES["reverted"],
        compare_return_metadata=True,
        x86_callengine_limb_values=X86_CONTROL_FLOW_GAS_CONTEXT,
        x86_execution_mode="cfg",
        x86_enable_go_bridge=True,
        x86_max_depth=200,
    )

    operands = _operands(case)
    memory_words = _symbolic_memory_words(case)
    readonly_words = _symbolic_readonly_words(case)

    evm_state = _build_evm_final_state(case, operands, memory_words, readonly_words)
    x86_state = _build_x86_final_state(case, operands, memory_words, readonly_words)

    solver = Solver()
    solver.add(evm_state.error_code != BitVecVal(EvmStatusCode.REVERTED, 8))
    result = solver.check()
    assert result == unsat, (
        f"EVM error_code should be REVERTED (1), "
        f"solver returned {result}"
    )

    solver = Solver()
    solver.add(
        x86_state.callengine_status_code != BitVecVal(EvmStatusCode.REVERTED, 8)
    )
    result = solver.check()
    assert result == unsat, (
        f"x86 callengine_status_code should always be REVERTED (1), "
        f"solver returned {result}"
    )

    assert EvmStatusCode.REVERTED == X86_STATUS_CODES["reverted"], (
        f"EVM REVERTED ({EvmStatusCode.REVERTED}) != "
        f"x86 reverted ({X86_STATUS_CODES['reverted']})"
    )


def test_return_error_code_matches_x86_status_code():
    """Verify RETURN: IR error_code = x86 callEngine status_code = RETURNED."""
    case = InstructionRefinementCase(
        name="RETURN",
        evm_kind="RETURN",
        arity=2,
        x86_core_hex=X86_RETURN_CORE_HEX_SEQUENCE,
        base_addr=X86_CORE_BASE_ADDR,
        operand_values=(32, 0),
        expected_stack_height=0,
        expected_status_code=X86_STATUS_CODES["returned"],
        compare_return_metadata=True,
        x86_callengine_limb_values=X86_CONTROL_FLOW_GAS_CONTEXT,
        x86_execution_mode="cfg",
        x86_enable_go_bridge=True,
        x86_max_depth=200,
    )

    operands = _operands(case)
    memory_words = _symbolic_memory_words(case)
    readonly_words = _symbolic_readonly_words(case)

    evm_state = _build_evm_final_state(case, operands, memory_words, readonly_words)
    x86_state = _build_x86_final_state(case, operands, memory_words, readonly_words)

    solver = Solver()
    solver.add(evm_state.error_code != BitVecVal(EvmStatusCode.RETURNED, 8))
    result = solver.check()
    assert result == unsat, (
        f"EVM error_code should be RETURNED (0), "
        f"solver returned {result}"
    )

    solver = Solver()
    solver.add(
        x86_state.callengine_status_code != BitVecVal(EvmStatusCode.RETURNED, 8)
    )
    result = solver.check()
    assert result == unsat, (
        f"x86 callengine_status_code should always be RETURNED (0), "
        f"solver returned {result}"
    )

    assert EvmStatusCode.RETURNED == X86_STATUS_CODES["returned"], (
        f"EVM RETURNED ({EvmStatusCode.RETURNED}) != "
        f"x86 returned ({X86_STATUS_CODES['returned']})"
    )


def test_invalid_error_code_matches_x86_status_code():
    """Verify INVALID: IR error_code = x86 callEngine status_code = INVALID."""
    case = InstructionRefinementCase(
        name="INVALID",
        evm_kind="INVALID",
        arity=0,
        x86_core_hex=X86_INVALID_CORE_HEX_SEQUENCE,
        base_addr=X86_CORE_BASE_ADDR,
        expected_stack_height=0,
        expected_status_code=X86_STATUS_CODES["invalid"],
        x86_callengine_limb_values=X86_CONTROL_FLOW_GAS_CONTEXT,
        x86_execution_mode="cfg",
        x86_enable_go_bridge=True,
    )

    operands = _operands(case)
    memory_words = _symbolic_memory_words(case)
    readonly_words = _symbolic_readonly_words(case)

    evm_state = _build_evm_final_state(case, operands, memory_words, readonly_words)
    x86_state = _build_x86_final_state(case, operands, memory_words, readonly_words)

    solver = Solver()
    solver.add(evm_state.error_code != BitVecVal(EvmStatusCode.INVALID, 8))
    result = solver.check()
    assert result == unsat, (
        f"EVM error_code should be INVALID (3), "
        f"solver returned {result}"
    )

    solver = Solver()
    solver.add(
        x86_state.callengine_status_code != BitVecVal(EvmStatusCode.INVALID, 8)
    )
    result = solver.check()
    assert result == unsat, (
        f"x86 callengine_status_code should always be INVALID (3), "
        f"solver returned {result}"
    )

    assert EvmStatusCode.INVALID == X86_STATUS_CODES["invalid"], (
        f"EVM INVALID ({EvmStatusCode.INVALID}) != "
        f"x86 invalid ({X86_STATUS_CODES['invalid']})"
    )


def test_stop_error_code_matches_x86_status_code():
    """Verify STOP: IR error_code = x86 callEngine status_code = STOPPED."""
    case = InstructionRefinementCase(
        name="STOP",
        evm_kind="STOP",
        arity=0,
        x86_core_hex=X86_STOP_CORE_HEX_SEQUENCE,
        base_addr=X86_CORE_BASE_ADDR,
        expected_stack_height=0,
        expected_status_code=X86_STATUS_CODES["stopped"],
        x86_callengine_limb_values=X86_CONTROL_FLOW_GAS_CONTEXT,
        x86_execution_mode="cfg",
        x86_enable_go_bridge=True,
    )

    operands = _operands(case)
    memory_words = _symbolic_memory_words(case)
    readonly_words = _symbolic_readonly_words(case)

    evm_state = _build_evm_final_state(case, operands, memory_words, readonly_words)
    x86_state = _build_x86_final_state(case, operands, memory_words, readonly_words)

    solver = Solver()
    solver.add(evm_state.error_code != BitVecVal(EvmStatusCode.STOPPED, 8))
    result = solver.check()
    assert result == unsat, (
        f"EVM error_code should be STOPPED (2), "
        f"solver returned {result}"
    )

    solver = Solver()
    solver.add(
        x86_state.callengine_status_code != BitVecVal(EvmStatusCode.STOPPED, 8)
    )
    result = solver.check()
    assert result == unsat, (
        f"x86 callengine_status_code should always be STOPPED (2), "
        f"solver returned {result}"
    )

    assert EvmStatusCode.STOPPED == X86_STATUS_CODES["stopped"], (
        f"EVM STOPPED ({EvmStatusCode.STOPPED}) != "
        f"x86 stopped ({X86_STATUS_CODES['stopped']})"
    )


def test_jump_to_invalid_dest_error_code():
    """Verify JUMP to invalid dest: IR error_code = x86 status_code = INVALID_JUMP.

    EVM code derived from the same IR that generated the x86 hex:
    IR: Block 0 [PUSH1 0x00, PUSH1 0x0a, JUMP], Block 1 [JUMPDEST @ PC 6, STOP]
    dest=10 is out of bounds (code_size=8) -> INVALID_JUMP.
    """
    code_words = _code_words_from_hex(JUMP_INVALID_CODE_HEX)

    case = InstructionRefinementCase(
        name="JUMP_INVALID",
        evm_kind="JUMP",
        arity=1,
        x86_core_hex=X86_JUMP_INVALID_CORE_HEX_SEQUENCE,
        base_addr=X86_CORE_BASE_ADDR,
        operand_values=(10,),
        initial_code_word_offsets=(0,),
        code_size_bytes=8,
        # IR Block 1 的 JUMPDEST 在 PC 6，是唯一合法目标；dest=10 落在集合外。
        evm_valid_jump_targets=(6,),
        expected_status_code=X86_STATUS_CODES["invalid_jump"],
        x86_callengine_limb_values=X86_CONTROL_FLOW_GAS_CONTEXT,
        x86_execution_mode="cfg",
        x86_enable_go_bridge=True,
        x86_max_depth=200,
    )

    operands = _operands(case)
    memory_words = _symbolic_memory_words(case)
    readonly_words = _symbolic_readonly_words(case)
    readonly_words["code"] = code_words

    evm_state = _build_evm_final_state(case, operands, memory_words, readonly_words)
    x86_state = _build_x86_final_state(case, operands, memory_words, readonly_words)

    solver = Solver()
    solver.add(evm_state.error_code != BitVecVal(EvmStatusCode.INVALID_JUMP, 8))
    result = solver.check()
    assert result == unsat, (
        f"EVM error_code should be INVALID_JUMP (8), "
        f"solver returned {result}"
    )

    solver = Solver()
    solver.add(
        x86_state.callengine_status_code != BitVecVal(EvmStatusCode.INVALID_JUMP, 8)
    )
    result = solver.check()
    assert result == unsat, (
        f"x86 callengine_status_code should always be INVALID_JUMP (8), "
        f"solver returned {result}"
    )

    assert EvmStatusCode.INVALID_JUMP == X86_STATUS_CODES["invalid_jump"], (
        f"EVM INVALID_JUMP ({EvmStatusCode.INVALID_JUMP}) != "
        f"x86 invalid_jump ({X86_STATUS_CODES['invalid_jump']})"
    )


def test_jumpi_to_invalid_dest_error_code():
    """Verify JUMPI to invalid dest: IR error_code = x86 status_code = INVALID_JUMP.

    EVM code derived from the same IR that generated the x86 hex:
    IR: Block 0 [PUSH1 0x01, PUSH1 0x0a, JUMPI], Block 1 [JUMPDEST @ PC 6, STOP]
    cond=1, dest=10 -> INVALID_JUMP.
    """
    code_words = _code_words_from_hex(JUMPI_INVALID_CODE_HEX)

    case = InstructionRefinementCase(
        name="JUMPI_INVALID",
        evm_kind="JUMPI",
        arity=2,
        x86_core_hex=X86_JUMPI_INVALID_CORE_HEX_SEQUENCE,
        base_addr=X86_CORE_BASE_ADDR,
        operand_values=(10, 1),
        initial_code_word_offsets=(0,),
        code_size_bytes=8,
        # IR Block 1 的 JUMPDEST 在 PC 6，是唯一合法目标；cond=1 且 dest=10 落在集合外。
        evm_valid_jump_targets=(6,),
        expected_status_code=X86_STATUS_CODES["invalid_jump"],
        x86_callengine_limb_values=X86_CONTROL_FLOW_GAS_CONTEXT,
        x86_execution_mode="cfg",
        x86_enable_go_bridge=True,
        x86_max_depth=200,
    )

    operands = _operands(case)
    memory_words = _symbolic_memory_words(case)
    readonly_words = _symbolic_readonly_words(case)
    readonly_words["code"] = code_words

    evm_state = _build_evm_final_state(case, operands, memory_words, readonly_words)
    x86_state = _build_x86_final_state(case, operands, memory_words, readonly_words)

    solver = Solver()
    solver.add(evm_state.error_code != BitVecVal(EvmStatusCode.INVALID_JUMP, 8))
    result = solver.check()
    assert result == unsat, (
        f"EVM error_code should be INVALID_JUMP (8), "
        f"solver returned {result}"
    )

    solver = Solver()
    solver.add(
        x86_state.callengine_status_code != BitVecVal(EvmStatusCode.INVALID_JUMP, 8)
    )
    result = solver.check()
    assert result == unsat, (
        f"x86 callengine_status_code should always be INVALID_JUMP (8), "
        f"solver returned {result}"
    )

    assert EvmStatusCode.INVALID_JUMP == X86_STATUS_CODES["invalid_jump"], (
        f"EVM INVALID_JUMP ({EvmStatusCode.INVALID_JUMP}) != "
        f"x86 invalid_jump ({X86_STATUS_CODES['invalid_jump']})"
    )


def test_jumpi_cond_zero_no_error():
    """Verify JUMPI with cond=0 does not set error_code.

    EVM code derived from the same IR that generated the x86 hex.
    """
    code_words = _code_words_from_hex(JUMPI_INVALID_CODE_HEX)

    case = InstructionRefinementCase(
        name="JUMPI_COND_ZERO",
        evm_kind="JUMPI",
        arity=2,
        x86_core_hex=X86_JUMPI_INVALID_CORE_HEX_SEQUENCE,
        base_addr=X86_CORE_BASE_ADDR,
        operand_values=(10, 0),
        initial_code_word_offsets=(0,),
        code_size_bytes=8,
        x86_callengine_limb_values=X86_CONTROL_FLOW_GAS_CONTEXT,
        x86_execution_mode="cfg",
        x86_enable_go_bridge=True,
    )

    operands = _operands(case)
    memory_words = _symbolic_memory_words(case)
    readonly_words = _symbolic_readonly_words(case)
    readonly_words["code"] = code_words

    evm_state = _build_evm_final_state(case, operands, memory_words, readonly_words)

    solver = Solver()
    solver.add(evm_state.error_code != BitVecVal(0, 8))
    result = solver.check()
    assert result == unsat, (
        f"JUMPI with cond=0 should not set error_code (expected 0=RETURNED), "
        f"solver returned {result}"
    )


def test_tag_stack_underflow_program_level():
    """Program-level: TAG with sp=0 < min_depth=2 -> STACK_UNDERFLOW (14)."""
    from evm_ir.models import EVMBlock, EvmOperator
    from evm_ir.program import EVMProgram
    from evm_ir.json_parser import CompilerEVMResult
    from state.smt_state import SMTState
    from state.evm_stack_state import EVMStackState
    from z3 import IntVal

    block = EVMBlock(
        pc=0, stack_depth=0, min_depth=2, max_depth=1024,
        static_gas=0, is_jump_target=False, is_inner_block=False,
        is_stop=False,
    )
    # 守卫只在块含 TAG 时施加。
    block.operations = [EvmOperator(kind="TAG", pc=0, block=block)]
    program = EVMProgram(CompilerEVMResult(blocks=[block]))

    state = SMTState()
    state.evm_stack = EVMStackState(sp=IntVal(0))

    merged_state, _ = program.to_z3(state)

    solver = Solver()
    solver.add(merged_state.error_code != BitVecVal(EvmStatusCode.STACK_UNDERFLOW, 8))
    result = solver.check()
    assert result == unsat, (
        f"TAG with sp=0 < min_depth=2 should be STACK_UNDERFLOW (14), "
        f"solver returned {result}"
    )


def test_tag_stack_reached_limit_program_level():
    """Program-level: TAG with sp=5 > max_depth=3 -> STACK_REACHED_LIMIT (15)."""
    from evm_ir.models import EVMBlock, EvmOperator
    from evm_ir.program import EVMProgram
    from evm_ir.json_parser import CompilerEVMResult
    from state.smt_state import SMTState
    from state.evm_stack_state import EVMStackState
    from z3 import IntVal

    block = EVMBlock(
        pc=0, stack_depth=5, min_depth=0, max_depth=3,
        static_gas=0, is_jump_target=False, is_inner_block=False,
        is_stop=False,
    )
    block.operations = [EvmOperator(kind="TAG", pc=0, block=block)]
    program = EVMProgram(CompilerEVMResult(blocks=[block]))

    state = SMTState()
    state.evm_stack = EVMStackState(sp=IntVal(5))

    merged_state, _ = program.to_z3(state)

    solver = Solver()
    solver.add(merged_state.error_code != BitVecVal(EvmStatusCode.STACK_REACHED_LIMIT, 8))
    result = solver.check()
    assert result == unsat, (
        f"TAG with sp=5 > max_depth=3 should be STACK_REACHED_LIMIT (15), "
        f"solver returned {result}"
    )


# ---- TAG 栈深度守卫：不可满足错误路径必须被剪掉，可满足的一条都不能少 ----

def _stop_block(*, min_depth: int, max_depth: int, with_tag: bool = True):
    """构造一个 `TAG; STOP` 块：正常路径也是终止路径，三个区域都可观察。"""
    from evm_ir.models import EVMBlock, EvmOperator

    block = EVMBlock(
        pc=0, stack_depth=0, min_depth=min_depth, max_depth=max_depth,
        static_gas=0, is_jump_target=False, is_inner_block=False,
        is_stop=True,
    )
    block.operations = [EvmOperator(kind="TAG", pc=0, block=block)] if with_tag else []
    block.operations.append(EvmOperator(kind="STOP", pc=1, block=block))
    return block


def _states_by_status(final_states):
    by_code = {}
    for gstate in final_states:
        by_code.setdefault(str(gstate.mstate.error_code), []).append(gstate)
    return by_code


def _status_key(code) -> str:
    return str(BitVecVal(code, 8))


def _run_executor(block, sp):
    from evm_ir.cfg_executor import SymbolicExecutor
    from state.evm_stack_state import EVMStackState
    from state.smt_state import SMTState

    state = SMTState()
    state.evm_stack = EVMStackState(sp=sp)
    executor = SymbolicExecutor([block], max_depth=50, use_reachability_check=False)
    return executor.execute(state, entry_pc=block.pc)


def test_tag_depth_guard_prunes_unsatisfiable_error_paths():
    """具体 SP 落在 [min_depth, max_depth] 内时，不应残留任何深度错误终态。"""
    from z3 import IntVal

    final_states = _run_executor(_stop_block(min_depth=0, max_depth=1022), IntVal(0))

    error_codes = [str(gstate.mstate.error_code) for gstate in final_states]
    assert error_codes == [str(BitVecVal(EvmStatusCode.STOPPED, 8))], (
        f"具体 SP=0 只应留下正常 STOP 终态，实际得到 {error_codes}"
    )


def test_tag_depth_guard_keeps_all_symbolic_regions():
    """符号 SP 时三个区域都可满足，剪枝不能删掉其中任何一条。"""
    from z3 import And, Int, Not, Solver, sat

    sp = Int("tag_guard_sp")
    final_states = _run_executor(_stop_block(min_depth=2, max_depth=1000), sp)

    by_code = _states_by_status(final_states)

    expected_regions = {
        _status_key(EvmStatusCode.STACK_UNDERFLOW): sp < 2,
        _status_key(EvmStatusCode.STACK_REACHED_LIMIT): sp > 1000,
        _status_key(EvmStatusCode.STOPPED): And(sp >= 2, sp <= 1000),
    }

    assert set(by_code) == set(expected_regions), (
        f"符号 SP 下三个区域都应保留，实际得到 {sorted(by_code)}"
    )

    for code, region in expected_regions.items():
        gstates = by_code[code]
        assert len(gstates) == 1
        condition = gstates[0].get_constraints().as_bool()

        # 路径条件必须蕴含它所属的区域（不会越界到别的区域）。
        solver = Solver()
        solver.add(And(condition, Not(region)))
        assert solver.check() != sat, f"status {code} 的路径条件超出了它的 SP 区域"

        # 且这条路径本身可满足（没有被误剪成空集）。
        solver = Solver()
        solver.add(condition)
        assert solver.check() == sat, f"status {code} 的路径条件不可满足"


def test_tag_depth_guard_drops_impossible_normal_terminal():
    """本块必然 underflow 时，不能残留一条条件恒 False 的正常终态。

    execute() 的终态判定只看块的控制流指令，所以以 STOP/RETURN 结尾的块即使
    正常路径已被证伪，仍会走到追加终态那一步。
    """
    from z3 import IntVal

    final_states = _run_executor(_stop_block(min_depth=2, max_depth=1024), IntVal(0))

    by_code = _states_by_status(final_states)
    assert set(by_code) == {_status_key(EvmStatusCode.STACK_UNDERFLOW)}, (
        f"SP=0 < min_depth=2 只应留下 underflow 终态，实际得到 {sorted(by_code)}"
    )


def test_no_final_state_has_literally_false_condition():
    """全局不变量：final_states 里不存在条件恒 False 的终态。"""
    from z3 import IntVal, is_false, simplify

    from evm_ir.cfg_executor import SymbolicExecutor
    from evm_ir.json_parser import load_ir_from_json
    from state.evm_stack_state import EVMStackState
    from state.smt_state import SMTState

    blocks = load_ir_from_json("tests/data/muti_block_08.json").blocks
    state = SMTState()
    state.evm_stack = EVMStackState(sp=IntVal(0))
    final_states = SymbolicExecutor(blocks, max_depth=400).execute(
        state, entry_pc=blocks[0].pc
    )

    impossible = [
        gstate for gstate in final_states
        if is_false(simplify(gstate.get_constraints().as_bool()))
    ]
    assert not impossible, f"{len(impossible)}/{len(final_states)} 条终态恒不可满足"


def test_tag_depth_guard_models_overflow_at_max_depth_1024():
    """max_depth==1024 的块 Go 照样发射 overflow 检查（tests/data 里有 26 个）。"""
    from z3 import And, Int, Not, Solver, sat

    sp = Int("tag_guard_sp_1024")
    final_states = _run_executor(_stop_block(min_depth=0, max_depth=1024), sp)
    by_code = _states_by_status(final_states)

    limit_key = _status_key(EvmStatusCode.STACK_REACHED_LIMIT)
    assert limit_key in by_code, (
        f"max_depth==1024 必须建模 overflow 路径，实际得到 {sorted(by_code)}"
    )
    # min_depth==0：Go 的无符号 sp < 0 恒假，不应产生 underflow 路径。
    assert _status_key(EvmStatusCode.STACK_UNDERFLOW) not in by_code

    condition = by_code[limit_key][0].get_constraints().as_bool()
    solver = Solver()
    solver.add(And(condition, Not(sp > 1024)))
    assert solver.check() != sat


def test_tag_depth_guard_underflow_takes_priority_over_overflow():
    """min_depth > max_depth 时 Go 先命中 underflow；两条错误路径不能重叠。"""
    from z3 import And, Int, Not, Or, Solver, sat

    sp = Int("tag_guard_sp_conflict")
    final_states = _run_executor(_stop_block(min_depth=5, max_depth=3), sp)
    by_code = _states_by_status(final_states)

    underflow_key = _status_key(EvmStatusCode.STACK_UNDERFLOW)
    limit_key = _status_key(EvmStatusCode.STACK_REACHED_LIMIT)
    assert {underflow_key, limit_key} <= set(by_code)

    underflow_cond = by_code[underflow_key][0].get_constraints().as_bool()
    limit_cond = by_code[limit_key][0].get_constraints().as_bool()

    # 正常路径条件 `sp>=5 且 sp<5` 是 UNSAT 但 simplify 折不成字面 False，
    # 状态可能仍在 final_states 里——只要恒不可满足就不影响任何判定。
    for key, gstates in by_code.items():
        if key in (underflow_key, limit_key):
            continue
        for gstate in gstates:
            solver = Solver()
            solver.add(gstate.get_constraints().as_bool())
            assert solver.check() != sat, f"min>max 的块不应存在可满足的 status {key} 路径"

    # 互斥：同一个输入不能既是 underflow 又是 stack-limit（否则两条终态状态码冲突）。
    solver = Solver()
    solver.add(And(underflow_cond, limit_cond))
    assert solver.check() != sat, "underflow 与 overflow 路径条件重叠"

    # 覆盖：两条错误路径合起来覆盖所有 SP（正常路径恒不可满足）。
    solver = Solver()
    solver.add(Not(Or(underflow_cond, limit_cond)))
    assert solver.check() != sat, "两条错误路径没有覆盖全部 SP"

    # 优先级：sp=4 落在 underflow（4<5），不能落在 overflow（虽然 4>3）。
    solver = Solver()
    solver.add(And(limit_cond, sp == 4))
    assert solver.check() != sat, "sp=4 应优先判 underflow，Go 的检查顺序丢了"


def test_block_without_tag_has_no_depth_guard():
    """Go 只在 TAG 算子处发射深度检查；无 TAG 的块不应凭空产生错误路径。"""
    from z3 import Int

    sp = Int("tag_guard_sp_no_tag")
    final_states = _run_executor(
        _stop_block(min_depth=2, max_depth=3, with_tag=False), sp
    )

    assert set(_states_by_status(final_states)) == {_status_key(EvmStatusCode.STOPPED)}


def test_missing_max_depth_defaults_to_go_initial_value():
    """max_depth 缺键对齐 Go 初值；退化成 0 会把任何非空栈判成 overflow。"""
    from evm_ir.models import GO_MAX_INT64, EVMBlock

    block = EVMBlock.from_json({
        'pc': 0,
        'min_depth': 0,
        'operations': [{'kind': 'TAG', 'pc': 0}, {'kind': 'STOP', 'pc': 1}],
    })

    assert block.max_depth == GO_MAX_INT64

    from z3 import IntVal

    final_states = _run_executor(block, IntVal(3))
    assert set(_states_by_status(final_states)) == {_status_key(EvmStatusCode.STOPPED)}



# ---------------------------------------------------------------------------
# 错误终态的端到端对齐
#
# 这些用例证明"错误终态机制本身正确"（两侧都真正产生同一状态码），而不只是
# "checker 能拒绝不一致"——后者已有覆盖：test_refinement_return_data.py 的
# merged 入口 + test_program_path_semantics.py 的串行/并行/aggregate fallback。
#
# gas-safe test domain：RETURNDATACOPY 的机器码在 OOB 检查之前先跑
# checkMemoryAndCalcDynamicGasReturnDataCopy，所以一律用具体小 length、具体安全
# memOffset、固定充足 gas，只让 dataOffset 变化，避免撞进本轮不建模的 gas 分支。
# ---------------------------------------------------------------------------

def _returndatacopy_oob_case(name: str, operand_values: tuple[int, int, int],
                             return_data_size_bytes: int) -> InstructionRefinementCase:
    """operand_values 按压栈顺序给出 (length, dataOffset, memOffset)。"""
    return InstructionRefinementCase(
        name=name,
        evm_kind="RETURNDATACOPY",
        arity=3,
        x86_core_hex=X86_RETURNDATACOPY_CORE_HEX_SEQUENCE,
        base_addr=X86_CORE_BASE_ADDR,
        operand_values=operand_values,
        return_data_size_bytes=return_data_size_bytes,
        expected_status_code=X86_STATUS_CODES["return_data_out_of_bounds"],
        x86_execution_mode="cfg",
        x86_max_depth=120,
    )


def _both_sides(case: InstructionRefinementCase):
    operands = _operands(case)
    memory_words = _symbolic_memory_words(case)
    readonly_words = _symbolic_readonly_words(case)
    return (
        _build_evm_final_state(case, operands, memory_words, readonly_words),
        _build_x86_final_state(case, operands, memory_words, readonly_words),
    )


def test_returndatacopy_out_of_bounds_status_matches_x86():
    """dataOffset+length 超出 returnDataSize：两侧都得 RETURN_DATA_OUT_OF_BOUNDS。"""
    evm_state, x86_state = _both_sides(
        _returndatacopy_oob_case("RETURNDATACOPY_OOB", (4, 10, 0), 8)
    )

    solver = Solver()
    solver.add(evm_state.error_code != BitVecVal(
        EvmStatusCode.RETURN_DATA_OUT_OF_BOUNDS, 8))
    assert solver.check() == unsat, "EVM 侧应恒为 RETURN_DATA_OUT_OF_BOUNDS"

    solver = Solver()
    solver.add(x86_state.callengine_status_code != BitVecVal(
        EvmStatusCode.RETURN_DATA_OUT_OF_BOUNDS, 8))
    assert solver.check() == unsat, "x86 侧应恒为 RETURN_DATA_OUT_OF_BOUNDS"

    # 真正的精化断言：两侧状态码对所有输入相等。
    solver = Solver()
    solver.add(evm_state.error_code != x86_state.callengine_status_code)
    assert solver.check() == unsat, "两侧终止状态码必须一致"


def test_returndatacopy_data_offset_overflow_status_matches_x86():
    """dataOffset 超出 uint64 —— compileLocIsUint64 那一支，两侧都得 7。"""
    evm_state, x86_state = _both_sides(
        _returndatacopy_oob_case("RETURNDATACOPY_HI", (0, 1 << 64, 0), 8)
    )

    solver = Solver()
    solver.add(evm_state.error_code != x86_state.callengine_status_code)
    assert solver.check() == unsat, "dataOffset 溢出时两侧状态码必须一致"

    solver = Solver()
    solver.add(evm_state.error_code != BitVecVal(
        EvmStatusCode.RETURN_DATA_OUT_OF_BOUNDS, 8))
    assert solver.check() == unsat


def test_returndatacopy_in_bounds_x86_reaches_stop_exit():
    """安全输入下 x86 绕过 OOB stub，走到 core 末尾的 STOP exit。

    只断言 x86 一侧：单指令桩的 EVM 只执行 RETURNDATACOPY，安全输入下停在
    RETURNED(0)，与 x86 的 STOPPED 本就不该相等。双边全输入证明见
    test_returndatacopy_symbolic_offset_status_matches_x86_end_to_end。
    """
    case = _returndatacopy_oob_case("RETURNDATACOPY_SAFE", (4, 1, 0), 8)
    case = replace(case, expected_status_code=X86_STATUS_CODES["stopped"])
    _, x86_state = _both_sides(case)

    solver = Solver()
    solver.add(x86_state.callengine_status_code != BitVecVal(
        EvmStatusCode.STOPPED, 8))
    assert solver.check() == unsat, "安全输入下 x86 应走到 STOP exit"


def test_returndatacopy_oob_then_stop_keeps_error_status():
    """同 block 短路：OOB 之后的 STOP 不得执行，状态码保持 7（旧实现给 STOPPED）。"""
    rdc = EvmOperator(kind="RETURNDATACOPY", pc=0)
    stop = EvmOperator(kind="STOP", pc=1)
    block = EVMBlock(
        pc=0, stack_depth=3, min_depth=0, max_depth=1024, static_gas=0,
        is_jump_target=False, is_inner_block=False, is_stop=True,
        operations=[rdc, stop],
    )
    rdc.block = block
    stop.block = block

    state = SMTState.create_initial_state()
    state.callengine_return_data_size_bytes = BitVecVal(8, 64)
    for value in (4, 10, 0):   # length, dataOffset, memOffset
        state.evm_stack = state.evm_stack.push(BitVecVal(value, 256))

    paths = EVMProgram(CompilerEVMResult(blocks=[block])).to_z3_paths(state)

    assert len(paths.observations) == 1
    assert is_true(simplify(
        paths.observations[0].status_code
        == BitVecVal(EvmStatusCode.RETURN_DATA_OUT_OF_BOUNDS, 8)
    )), "OOB 之后的 STOP 覆盖了错误码"


def test_returndatacopy_symbolic_offset_splits_exclusive_covering_paths():
    """符号 dataOffset：正常路径与 OOB 路径并存，条件互斥且覆盖全输入。"""
    rdc = EvmOperator(kind="RETURNDATACOPY", pc=0)
    stop = EvmOperator(kind="STOP", pc=1)
    block = EVMBlock(
        pc=0, stack_depth=3, min_depth=0, max_depth=1024, static_gas=0,
        is_jump_target=False, is_inner_block=False, is_stop=True,
        operations=[rdc, stop],
    )
    rdc.block = block
    stop.block = block

    data_offset = BitVec("e2e_data_offset", 256)
    state = SMTState.create_initial_state()
    state.callengine_return_data_size_bytes = BitVecVal(8, 64)
    state.evm_stack = state.evm_stack.push(BitVecVal(4, 256))    # length
    state.evm_stack = state.evm_stack.push(data_offset)          # dataOffset
    state.evm_stack = state.evm_stack.push(BitVecVal(0, 256))    # memOffset

    paths = EVMProgram(CompilerEVMResult(blocks=[block])).to_z3_paths(state)
    assert len(paths.observations) == 2, "应当分裂成正常路径与 OOB 路径"

    by_status = {}
    for obs in paths.observations:
        by_status[str(simplify(obs.status_code))] = obs.condition
    assert set(by_status) == {
        str(BitVecVal(EvmStatusCode.RETURN_DATA_OUT_OF_BOUNDS, 8)),
        str(BitVecVal(EvmStatusCode.STOPPED, 8)),
    }, f"意外的状态码集合: {set(by_status)}"

    conditions = list(by_status.values())
    overlap = Solver()
    overlap.add(And(*conditions))
    assert overlap.check() == unsat, "两条路径条件必须互斥"

    gap = Solver()
    gap.add(And(*[Not(c) for c in conditions]))
    assert gap.check() == unsat, "两条路径条件必须覆盖全部输入"


def test_static_invalid_jump_produces_terminal_status_not_exception():
    """全程序静态非法跳转得到 INVALID_JUMP 终态，而不是 LogicError（这类程序原本验不了）。"""
    jump = EvmOperator(kind="JUMP", pc=4, immediate=10, is_static=True)
    entry = EVMBlock(
        pc=0, stack_depth=0, min_depth=0, max_depth=1024, static_gas=0,
        is_jump_target=False, is_inner_block=False, is_stop=False,
        operations=[jump],
    )
    stop = EvmOperator(kind="STOP", pc=7)
    target = EVMBlock(
        pc=6, stack_depth=0, min_depth=0, max_depth=1024, static_gas=0,
        is_jump_target=True, is_inner_block=False, is_stop=True,
        operations=[stop],
    )
    jump.block = entry
    stop.block = target

    paths = EVMProgram(CompilerEVMResult(blocks=[entry, target])).to_z3_paths(
        SMTState.create_initial_state()
    )

    assert len(paths.observations) == 1
    assert is_true(simplify(
        paths.observations[0].status_code == BitVecVal(EvmStatusCode.INVALID_JUMP, 8)
    ))


def test_program_without_jumpdest_makes_every_jump_invalid():
    """一个 JUMPDEST 都没有的程序：任何跳转都是 INVALID_JUMP（对齐空 jumpTable）。"""
    jump = EvmOperator(kind="JUMP", pc=4, immediate=6, is_static=True)
    entry = EVMBlock(
        pc=0, stack_depth=0, min_depth=0, max_depth=1024, static_gas=0,
        is_jump_target=False, is_inner_block=False, is_stop=False,
        operations=[jump],
    )
    stop = EvmOperator(kind="STOP", pc=7)
    # 注意 is_jump_target=False：目标块存在，但不是 JUMPDEST。
    target = EVMBlock(
        pc=6, stack_depth=0, min_depth=0, max_depth=1024, static_gas=0,
        is_jump_target=False, is_inner_block=False, is_stop=True,
        operations=[stop],
    )
    jump.block = entry
    stop.block = target

    paths = EVMProgram(CompilerEVMResult(blocks=[entry, target])).to_z3_paths(
        SMTState.create_initial_state()
    )

    assert len(paths.observations) == 1
    assert is_true(simplify(
        paths.observations[0].status_code == BitVecVal(EvmStatusCode.INVALID_JUMP, 8)
    ))


def test_mutated_status_immediate_is_detected():
    """负向故障注入：只改 STOP core hex 里的 status 立即数，必须被抓到。

    比拿两个不同程序对比更精准：只改变 status 这一个 observable。
    """
    original = X86_STOP_CORE_HEX_SEQUENCE
    # compileExitFromNativeCode 的 `mov byte [r13+0xe0], 2`（STOPPED）
    marker = "41c685e000000002"
    assert original.count(marker) >= 1
    # 改**第一处**：它后面紧跟 RET，是执行真正到达的 exit。core 末尾还有一处
    # 同样的写入（块末尾的隐式 STOP），那里是到不了的死代码，改它不会有效果。
    head, _, tail = original.partition(marker)
    mutated = head + "41c685e000000000" + tail

    assert len(mutated) == len(original)
    assert sum(a != b for a, b in zip(mutated, original)) == 1, "只应有一个字符不同"

    def status_of(core_hex: str):
        case = InstructionRefinementCase(
            name="STOP_MUTATION",
            evm_kind="STOP",
            arity=0,
            x86_core_hex=core_hex,
            base_addr=X86_CORE_BASE_ADDR,
            expected_stack_height=0,
            x86_execution_mode="cfg",
            x86_callengine_limb_values=X86_CONTROL_FLOW_GAS_CONTEXT,
        )
        operands = _operands(case)
        return _build_x86_final_state(
            case, operands, _symbolic_memory_words(case), _symbolic_readonly_words(case)
        ).callengine_status_code

    evm_stopped = BitVecVal(EvmStatusCode.STOPPED, 8)

    clean = Solver()
    clean.add(status_of(original) != evm_stopped)
    assert clean.check() == unsat, "未篡改的 hex 应与 EVM 的 STOPPED 一致"

    tampered = Solver()
    tampered.add(status_of(mutated) != evm_stopped)
    assert tampered.check() == sat, "篡改后的 status 必须被检出与 EVM 不一致"


def test_returndatacopy_symbolic_offset_status_matches_x86_end_to_end():
    """符号 dataOffset 下两侧状态码对**所有输入**相等。

    EVM 侧必须跑 ``RETURNDATACOPY; STOP`` 而非单 opcode：x86 core 在 OOB 检查后
    还有 STOP exit，单 opcode 在安全输入下停在 RETURNED(0)，比较会得到假反例。
    """
    case = InstructionRefinementCase(
        name="RDC_SYMBOLIC",
        evm_kind="RETURNDATACOPY",
        arity=3,
        x86_core_hex=X86_RETURNDATACOPY_CORE_HEX_SEQUENCE,
        base_addr=X86_CORE_BASE_ADDR,
        # gas-safe：length / memOffset 固定，只让 dataOffset 符号化。
        operand_values=(4, None, 0),
        initial_return_data_word_offsets=(0,),
        return_data_size_bytes=8,
        x86_execution_mode="cfg",
        x86_max_depth=120,
    )
    operands = _operands(case)
    memory_words = _symbolic_memory_words(case)
    readonly_words = _symbolic_readonly_words(case)

    x86_state = _build_x86_final_state(case, operands, memory_words, readonly_words)

    rdc = EvmOperator(kind="RETURNDATACOPY", pc=0)
    stop = EvmOperator(kind="STOP", pc=1)
    block = EVMBlock(
        pc=0, stack_depth=3, min_depth=0, max_depth=1024, static_gas=0,
        is_jump_target=False, is_inner_block=False, is_stop=True,
        operations=[rdc, stop],
    )
    rdc.block = block
    stop.block = block
    paths = EVMProgram(CompilerEVMResult(blocks=[block])).to_z3_paths(
        _build_evm_initial_state(case, operands, memory_words, readonly_words)
    )

    statuses = {str(simplify(obs.status_code)) for obs in paths.observations}
    assert statuses == {
        str(BitVecVal(EvmStatusCode.RETURN_DATA_OUT_OF_BOUNDS, 8)),
        str(BitVecVal(EvmStatusCode.STOPPED, 8)),
    }, f"应当分裂出 OOB 与正常两条路径，实际: {statuses}"

    for index, obs in enumerate(paths.observations):
        solver = Solver()
        solver.add(obs.condition)
        solver.add(obs.status_code != x86_state.callengine_status_code)
        assert solver.check() == unsat, (
            f"EVM path[{index}] (status={simplify(obs.status_code)}) "
            f"与 x86 状态码存在反例"
        )


def test_symbolic_condition_invalid_jumpi_splits_instead_of_raising():
    """符号 condition 的非法 JUMPI：分裂成 INVALID_JUMP 与 fallthrough 两条终态。

    taken 的可行性必须结合路径约束判定：jump_condition 自身 simplify 不出 False，
    只看它会走进目标块查找并抛 missing_jump_target。
    """
    jumpi = EvmOperator(kind="JUMPI", pc=4, immediate=10, is_static=True)
    entry = EVMBlock(
        pc=0, stack_depth=1, min_depth=0, max_depth=1024, static_gas=0,
        is_jump_target=False, is_inner_block=False, is_stop=False,
        operations=[jumpi],
    )
    fallthrough_stop = EvmOperator(kind="STOP", pc=5)
    fallthrough = EVMBlock(
        pc=5, stack_depth=0, min_depth=0, max_depth=1024, static_gas=0,
        is_jump_target=False, is_inner_block=False, is_stop=True,
        operations=[fallthrough_stop],
    )
    # 另有合法 JUMPDEST，避免落进"空 jumpTable ⇒ 一切非法"的特例。
    legal_stop = EvmOperator(kind="STOP", pc=7)
    legal_target = EVMBlock(
        pc=6, stack_depth=0, min_depth=0, max_depth=1024, static_gas=0,
        is_jump_target=True, is_inner_block=False, is_stop=True,
        operations=[legal_stop],
    )
    for op, blk in ((jumpi, entry), (fallthrough_stop, fallthrough), (legal_stop, legal_target)):
        op.block = blk

    state = SMTState.create_initial_state()
    state.evm_stack = state.evm_stack.push(BitVec("jumpi_cond", 256))

    paths = EVMProgram(
        CompilerEVMResult(blocks=[entry, fallthrough, legal_target])
    ).to_z3_paths(state)

    by_status = {str(simplify(obs.status_code)): obs.condition
                 for obs in paths.observations}
    assert set(by_status) == {
        str(BitVecVal(EvmStatusCode.INVALID_JUMP, 8)),
        str(BitVecVal(EvmStatusCode.STOPPED, 8)),
    }, f"意外的状态码集合: {set(by_status)}"

    conditions = list(by_status.values())
    overlap = Solver()
    overlap.add(And(*conditions))
    assert overlap.check() == unsat, "taken 与 fallthrough 路径条件必须互斥"

    gap = Solver()
    gap.add(And(*[Not(c) for c in conditions]))
    assert gap.check() == unsat, "两条路径条件必须覆盖全部输入"


def test_copy_with_unconsumed_pending_error_fails_closed():
    """soundness guard：带未消费错误分支的 state 不得被复制（静默重置会让错误路径消失）。"""
    from utils.exceptions import LogicError

    state = SMTState()
    state.callengine_return_data_size_bytes = BitVecVal(8, 64)
    for value in (4, 10, 0):   # length, dataOffset, memOffset —— 必然越界
        state.evm_stack = state.evm_stack.push(BitVecVal(value, 256))
    state = evm_operator_to_z3(EvmOperator(kind="RETURNDATACOPY", pc=0), state)
    assert state.pending_errors, "前置条件：该输入应当产生错误分支"

    with pytest.raises(LogicError) as excinfo:
        state.copy()
    assert excinfo.value.error_code == "unconsumed_pending_errors"

    # 消费之后可以正常复制。
    state.pending_errors = []
    assert state.copy() is not None
