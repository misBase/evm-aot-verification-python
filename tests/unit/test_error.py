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
    from evm_ir.models import EVMBlock
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
    from evm_ir.models import EVMBlock
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

