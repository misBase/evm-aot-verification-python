"""Unit tests: verify IR error_code matches x86 callEngine status_code after instruction execution.

Reuses test case parameters from test_single_ins_refinement, builds both
EVM IR and x86-64 final states, and cross-validates that the error/status
codes are consistent across both sides.
"""

from common.uint256 import Uint256
from evm_ir.status_code import EvmStatusCode
from tests.integration.test_single_ins_refinement import (
    X86_CONTROL_FLOW_GAS_CONTEXT,
    X86_CORE_BASE_ADDR,
    X86_INVALID_CORE_HEX_SEQUENCE,
    X86_RETURN_CORE_HEX_SEQUENCE,
    X86_STOP_CORE_HEX_SEQUENCE,
    X86_REVERT_CORE_HEX_SEQUENCE,
    X86_STATUS_CODES,
)
from tests.support.instruction_refinement import (
    InstructionRefinementCase,
    _build_evm_final_state,
    _build_x86_final_state,
    _operands,
    _symbolic_memory_words,
    _symbolic_readonly_words,
)
from z3 import BitVecVal, Solver, unsat
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

