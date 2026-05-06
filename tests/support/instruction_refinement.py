"""Helpers for single-instruction EVM/x86 micro-refinement tests."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Literal

from z3 import (
    BitVecVal,
    Concat,
    Extract,
    If,
    IntVal,
    Or,
    Select,
    Solver,
    Store,
    Z3_OP_CONCAT,
    Z3_OP_EXTRACT,
    Z3_OP_ITE,
    is_bv_value,
    simplify,
    unsat,
)

from common.uint256 import Uint256
from evm_ir.models import EvmOperator
from evm_ir.semantics import EVMOperationSemantics, evm_operator_to_z3
from state.evm_stack_state import EVMStackState
from state.smt_state import MemoryDomain, PointerTag, SMTState
from x86_64.disassembler import disassemble_hex
from x86_64.models import Register
from x86_64.program import X86Program


_LIMB_STRIDE_BYTES = 8
_UINT256_SLOT_BYTES = 4 * _LIMB_STRIDE_BYTES
_MAX_SUPPORTED_ARITY = 17
_CALLENGINE_LIMB_ATTRS = {
    0x18: "callengine_memory_size_bytes",
    0x70: "callengine_gas_remaining",
    0x98: "callengine_input_size_bytes",
    0xA8: "callengine_code_size_bytes",
    0xB8: "callengine_return_data_size_bytes",
}


@dataclass(frozen=True)
class InstructionRefinementCase:
    """A single EVM opcode and its x86 core implementation.

    By default a case is a pure stack calculation with one 256-bit result in the
    first operand slot.  Cases with ``expected_stack_height`` compare the whole
    final stack window instead, which covers PUSH/DUP/SWAP/POP-style stack shape
    changes.
    """

    name: str
    evm_kind: str
    arity: int
    x86_core_hex: str
    base_addr: int
    evm_pc: int = 0
    evm_param: int | None = None
    evm_immediate: int | None = None
    operand_values: tuple[int | None, ...] | None = None
    evm_operand_indices: tuple[int, ...] | None = None
    expected_stack_height: int | None = None
    initial_memory_word_offsets: tuple[int, ...] = ()
    initial_calldata_word_offsets: tuple[int, ...] = ()
    initial_code_word_offsets: tuple[int, ...] = ()
    initial_return_data_word_offsets: tuple[int, ...] = ()
    calldata_size_bytes: int | None = None
    code_size_bytes: int | None = None
    return_data_size_bytes: int | None = None
    evm_context_values: tuple[tuple[str, int], ...] = ()
    x86_callengine_limb_values: tuple[tuple[int, int], ...] = ()
    x86_stack_byte_values: tuple[tuple[int, int], ...] = ()
    memory_check_offsets: tuple[int, ...] = ()
    storage_check_keys: tuple[int, ...] = ()
    transient_storage_check_keys: tuple[int, ...] = ()
    x86_execution_mode: Literal["linear", "cfg"] = "linear"
    x86_enable_go_bridge: bool = False
    x86_max_depth: int = 50
    solver_timeout_ms: int = 10_000


def assert_instruction_refines(case: InstructionRefinementCase) -> None:
    """Prove one EVM operation and its x86 core produce the same stack effect.

    The v1 result mode covers AOT cores for pure stack calculations: operands
    are 256-bit stack values, the result is one 256-bit value, and the x86
    snippet writes it in-place to the bottom/result operand slot.  Stack-window
    mode compares every final stack slot and covers PUSH/DUP/SWAP/POP.  Both
    modes support straight-line snippets and small CFG snippets without host
    calls.
    """
    operands = _operands(case)
    memory_words = _symbolic_memory_words(case)
    readonly_words = _symbolic_readonly_words(case)
    if case.expected_stack_height is None and not case.memory_check_offsets:
        evm_result = _normalize_refinement_bv(_build_evm_result(case, operands))
        x86_result = _normalize_refinement_bv(
            _build_x86_result(case, operands, memory_words, readonly_words)
        )
        mismatches = [evm_result != x86_result]
    else:
        evm_state = _build_evm_final_state(case, operands, memory_words, readonly_words)
        x86_state = _build_x86_final_state(case, operands, memory_words, readonly_words)
        mismatches = []
        if case.expected_stack_height is not None:
            evm_stack = _extract_evm_stack_outputs(evm_state, case.expected_stack_height)
            x86_stack = _extract_x86_stack_outputs(x86_state, case.arity, case.expected_stack_height)
            mismatches.extend(evm != x86 for evm, x86 in zip(evm_stack, x86_stack, strict=True))
        mismatches.extend(_memory_mismatches(case, evm_state, x86_state))
        mismatches.extend(_storage_mismatches(case, evm_state, x86_state))
        mismatches.extend(_transient_storage_mismatches(case, evm_state, x86_state))

    solver = Solver()
    solver.set(timeout=case.solver_timeout_ms)
    solver.add(Or(*mismatches))
    result = solver.check()

    assert result == unsat, (
        f"{case.name} micro-refinement failed: "
        f"opcode={case.evm_kind}, base_addr=0x{case.base_addr:x}, "
        f"execution_mode={case.x86_execution_mode}, "
        f"x86_core_hex={case.x86_core_hex}, solver_result={result}"
    )


def _normalize_refinement_bv(expr):
    """Fold byte-wise memory round trips back into one word-sized expression."""
    # x86 侧的 256-bit 值经 byte-array memory store/load 后，常会变成
    # Concat(If(c, 0, Extract(byte, x)), ...)。这里仅把这种严格连续、
    # 同条件、同来源的形状折回 If(c, 0, Extract(word, x))，避免让 Z3
    # 为纯粹的 byte 重组噪音做昂贵 bit-blast。
    return _fold_bytewise_ite_concat(simplify(expr))


def _fold_bytewise_ite_concat(expr):
    parts = _flatten_concat(expr)
    if len(parts) <= 1:
        return expr

    folded = _try_fold_bytewise_zero_ite_concat(parts)
    if folded is not None:
        return folded

    return expr


def _flatten_concat(expr):
    if expr.decl().kind() != Z3_OP_CONCAT:
        return [expr]

    parts = []
    for index in range(expr.num_args()):
        parts.extend(_flatten_concat(expr.arg(index)))
    return parts


def _try_fold_bytewise_zero_ite_concat(parts):
    # 只接受 If(cond, 0, Extract(..., source)) 且 Extract 范围从高到低连续
    # 的 concat；任何条件、来源、顺序或分支形状不一致都会放弃折叠。
    condition = None
    source = None
    high = None
    next_low = None
    total_size = 0

    for part in parts:
        if part.decl().kind() != Z3_OP_ITE or part.num_args() != 3:
            return None

        part_condition = part.arg(0)
        zero_branch = part.arg(1)
        value_branch = part.arg(2)
        if not is_bv_value(zero_branch) or zero_branch.as_long() != 0:
            return None
        if value_branch.decl().kind() != Z3_OP_EXTRACT:
            return None

        extract_high, extract_low = value_branch.decl().params()
        if extract_high - extract_low + 1 != zero_branch.size():
            return None

        value_source = value_branch.arg(0)
        if condition is None:
            condition = part_condition
            source = value_source
            high = extract_high
        elif not condition.eq(part_condition) or not source.eq(value_source):
            return None

        if next_low is not None and extract_high != next_low - 1:
            return None

        next_low = extract_low
        total_size += zero_branch.size()

    if condition is None or source is None or high is None or next_low is None:
        return None

    return If(condition, BitVecVal(0, total_size), Extract(high, next_low, source))


def _operands(case: InstructionRefinementCase) -> list[Uint256]:
    if not 0 <= case.arity <= _MAX_SUPPORTED_ARITY:
        raise ValueError(
            f"{case.name}: arity must be between 0 and "
            f"{_MAX_SUPPORTED_ARITY}, got {case.arity}"
        )
    values = case.operand_values or (None,) * case.arity
    if len(values) != case.arity:
        raise ValueError(
            f"{case.name}: operand_values length must match arity, "
            f"got {len(values)} for arity {case.arity}"
        )
    return [
        Uint256.symbolic(f"{case.name.lower()}_arg{i}") if value is None else Uint256.from_int(value)
        for i, value in enumerate(values)
    ]


def _symbolic_memory_words(case: InstructionRefinementCase) -> list[Uint256]:
    return [
        Uint256.symbolic(f"{case.name.lower()}_mem{i}")
        for i, _ in enumerate(case.initial_memory_word_offsets)
    ]


def _symbolic_readonly_words(case: InstructionRefinementCase) -> dict[str, list[Uint256]]:
    return {
        "calldata": [
            Uint256.symbolic(f"{case.name.lower()}_calldata{i}")
            for i, _ in enumerate(case.initial_calldata_word_offsets)
        ],
        "code": [
            Uint256.symbolic(f"{case.name.lower()}_code{i}")
            for i, _ in enumerate(case.initial_code_word_offsets)
        ],
        "return_data": [
            Uint256.symbolic(f"{case.name.lower()}_returndata{i}")
            for i, _ in enumerate(case.initial_return_data_word_offsets)
        ],
    }


def _build_evm_result(case: InstructionRefinementCase, operands: list[Uint256]):
    op = _evm_operator(case)
    indices = case.evm_operand_indices or tuple(range(case.arity))
    if len(indices) != case.arity:
        raise ValueError(
            f"{case.name}: evm_operand_indices length must match arity, "
            f"got {len(indices)} for arity {case.arity}"
        )
    if any(index < 0 or index >= case.arity for index in indices):
        raise ValueError(
            f"{case.name}: evm_operand_indices must refer to operands "
            f"0..{case.arity - 1}, got {indices}"
        )
    inputs = [operands[index].to_bv256() for index in indices]
    return EVMOperationSemantics().operation_semantics(op, inputs)


def _build_evm_final_state(
    case: InstructionRefinementCase,
    operands: list[Uint256],
    memory_words: list[Uint256],
    readonly_words: dict[str, list[Uint256]],
) -> SMTState:
    state = SMTState()
    state.evm_stack = EVMStackState(sp=IntVal(0))
    for operand in operands:
        state.evm_stack = state.evm_stack.push(operand.to_bv256())
    for offset, word in zip(case.initial_memory_word_offsets, memory_words, strict=True):
        state.evm_memory = state.evm_memory.store_256bit(
            BitVecVal(offset, 64),
            word.to_bv256(),
        )
    _initialize_evm_readonly_sources(state, case, readonly_words)
    _initialize_evm_context_values(state, case)

    return evm_operator_to_z3(_evm_operator(case), state)


def _extract_evm_stack_outputs(final_state: SMTState, expected_stack_height: int):
    return tuple(
        Select(final_state.evm_stack.Stack, IntVal(slot_index))
        for slot_index in range(expected_stack_height)
    )


def _build_x86_result(
    case: InstructionRefinementCase,
    operands: list[Uint256],
    memory_words: list[Uint256],
    readonly_words: dict[str, list[Uint256]],
):
    state = _build_x86_final_state(case, operands, memory_words, readonly_words)
    return _load_stack_slot(state, case.arity, 0)


def _build_x86_final_state(
    case: InstructionRefinementCase,
    operands: list[Uint256],
    memory_words: list[Uint256],
    readonly_words: dict[str, list[Uint256]],
) -> SMTState:
    initial_memory = _build_aot_stack_memory(operands)
    initial_evm_memory = _build_aot_evm_memory(case, memory_words)
    return _execute_x86_core(case, initial_memory, initial_evm_memory, readonly_words)


def _extract_x86_stack_outputs(state: SMTState, arity: int, expected_stack_height: int):
    return tuple(
        _load_stack_slot(state, arity, slot_index)
        for slot_index in range(expected_stack_height)
    )


def _build_aot_stack_memory(operands: list[Uint256]):
    memory = {}
    for operand, offsets in zip(operands, _operand_limb_offsets(len(operands)), strict=True):
        for offset, limb in zip(
            offsets,
            (operand.z0, operand.z1, operand.z2, operand.z3),
            strict=True,
        ):
            memory[offset] = limb
    return memory


def _build_aot_evm_memory(case: InstructionRefinementCase, memory_words: list[Uint256]):
    memory = {}
    for offset, word in zip(case.initial_memory_word_offsets, memory_words, strict=True):
        value = word.to_bv256()
        for byte_index in range(32):
            memory[offset + byte_index] = Extract(
                255 - 8 * byte_index,
                248 - 8 * byte_index,
                value,
            )
    return memory


def _execute_x86_core(
    case: InstructionRefinementCase,
    initial_memory,
    initial_evm_memory,
    readonly_words: dict[str, list[Uint256]],
):
    state = SMTState()
    state.x86_registers.set_register(Register.R13, BitVecVal(0, 64))
    state.x86_registers.set_register(Register.R14, BitVecVal(0, 64))
    state.x86_registers.set_register(Register.R15, BitVecVal(0, 64))
    state.x86_registers.set_pointer_tag(Register.R15, PointerTag.EVM_PTR)
    state.unrouted_memory_domain = MemoryDomain.STACK

    for offset, value in initial_memory.items():
        state.x86_memory = state.x86_memory.store_limb(
            BitVecVal(offset, 64),
            value,
            domain=MemoryDomain.STACK,
        )
    for offset, value in initial_evm_memory.items():
        state.x86_memory = state.x86_memory.store_byte(
            BitVecVal(offset, 64),
            value,
            domain=MemoryDomain.EVM,
        )
    _initialize_x86_readonly_sources(state, case, readonly_words)
    _initialize_x86_callengine_limb_values(state, case)
    _initialize_x86_stack_byte_values(state, case)

    if case.x86_execution_mode == "cfg":
        return _execute_x86_core_cfg(case, state)
    if case.x86_execution_mode != "linear":
        raise ValueError(
            f"{case.name}: x86_execution_mode must be 'linear' or 'cfg', "
            f"got {case.x86_execution_mode!r}"
        )
    return _execute_x86_core_linear(case, state)


def _initialize_evm_readonly_sources(
    state: SMTState,
    case: InstructionRefinementCase,
    readonly_words: dict[str, list[Uint256]],
) -> None:
    state.calldata = _store_words_in_byte_array(
        state.calldata,
        case.initial_calldata_word_offsets,
        readonly_words["calldata"],
    )
    state.code = _store_words_in_byte_array(
        state.code,
        case.initial_code_word_offsets,
        readonly_words["code"],
    )
    state.return_data = _store_words_in_byte_array(
        state.return_data,
        case.initial_return_data_word_offsets,
        readonly_words["return_data"],
    )
    if case.calldata_size_bytes is not None:
        state.calldatasize = BitVecVal(case.calldata_size_bytes, 64)
        state.callengine_input_size_bytes = BitVecVal(case.calldata_size_bytes, 64)
    if case.code_size_bytes is not None:
        state.callengine_code_size_bytes = BitVecVal(case.code_size_bytes, 64)
    if case.return_data_size_bytes is not None:
        state.callengine_return_data_size_bytes = BitVecVal(case.return_data_size_bytes, 64)


def _initialize_evm_context_values(state: SMTState, case: InstructionRefinementCase) -> None:
    for field_name, value in case.evm_context_values:
        if field_name == "gas":
            state.evm_gas.Gas = BitVecVal(value, 64)
        elif field_name in {"block_timestamp", "block_number", "gaslimit", "blobbasefee", "blobhash_count"}:
            setattr(state, field_name, BitVecVal(value, 64))
        else:
            setattr(state, field_name, BitVecVal(value, 256))


def _initialize_x86_readonly_sources(
    state: SMTState,
    case: InstructionRefinementCase,
    readonly_words: dict[str, list[Uint256]],
) -> None:
    state.calldata = _store_words_in_byte_array(
        state.calldata,
        case.initial_calldata_word_offsets,
        readonly_words["calldata"],
    )
    state.code = _store_words_in_byte_array(
        state.code,
        case.initial_code_word_offsets,
        readonly_words["code"],
    )
    state.return_data = _store_words_in_byte_array(
        state.return_data,
        case.initial_return_data_word_offsets,
        readonly_words["return_data"],
    )

    _store_callengine_limb(state, 0x90, BitVecVal(0, 64))
    _store_callengine_limb(state, 0xA0, BitVecVal(0, 64))
    _store_callengine_limb(state, 0xB0, BitVecVal(0, 64))
    if case.calldata_size_bytes is not None:
        size = BitVecVal(case.calldata_size_bytes, 64)
        state.callengine_input_size_bytes = size
        _store_callengine_limb(state, 0x98, size)
    if case.code_size_bytes is not None:
        size = BitVecVal(case.code_size_bytes, 64)
        state.callengine_code_size_bytes = size
        _store_callengine_limb(state, 0xA8, size)
    if case.return_data_size_bytes is not None:
        size = BitVecVal(case.return_data_size_bytes, 64)
        state.callengine_return_data_size_bytes = size
        _store_callengine_limb(state, 0xB8, size)


def _initialize_x86_callengine_limb_values(
    state: SMTState,
    case: InstructionRefinementCase,
) -> None:
    for offset, value in case.x86_callengine_limb_values:
        value_bv = BitVecVal(value, 64)
        _store_callengine_limb(state, offset, value_bv)
        attr = _CALLENGINE_LIMB_ATTRS.get(offset)
        if attr is not None:
            setattr(state, attr, value_bv)


def _initialize_x86_stack_byte_values(
    state: SMTState,
    case: InstructionRefinementCase,
) -> None:
    for offset, value in case.x86_stack_byte_values:
        state.x86_memory = state.x86_memory.store_byte(
            BitVecVal(offset, 64),
            BitVecVal(value, 8),
            domain=MemoryDomain.STACK,
        )


def _store_words_in_byte_array(array, offsets: tuple[int, ...], words: list[Uint256]):
    for offset, word in zip(offsets, words, strict=True):
        value = word.to_bv256()
        for byte_index in range(32):
            array = Store(
                array,
                BitVecVal(offset + byte_index, 64),
                Extract(255 - 8 * byte_index, 248 - 8 * byte_index, value),
            )
    return array


def _store_callengine_limb(state: SMTState, offset: int, value) -> None:
    state.x86_memory = state.x86_memory.store_limb(
        BitVecVal(offset, 64),
        value,
        domain=MemoryDomain.CALLENGINE,
    )


def _execute_x86_core_linear(case: InstructionRefinementCase, state: SMTState) -> SMTState:
    for instruction in disassemble_hex(case.x86_core_hex, base_addr=case.base_addr):
        state = instruction.to_z3(state)

    return state


def _execute_x86_core_cfg(case: InstructionRefinementCase, state: SMTState) -> SMTState:
    program = X86Program.from_hex(case.x86_core_hex, base_addr=case.base_addr)
    final_state, _ = program.to_z3(
        state,
        max_depth=case.x86_max_depth,
        enable_go_bridge=case.x86_enable_go_bridge,
        enable_merge=False,
    )
    return final_state


def _memory_mismatches(case: InstructionRefinementCase, evm_state: SMTState, x86_state: SMTState):
    return [
        Select(evm_state.evm_memory.Memory, BitVecVal(offset, 64))
        != x86_state.x86_memory.load_byte(BitVecVal(offset, 64), domain=MemoryDomain.EVM)
        for offset in case.memory_check_offsets
    ]


def _storage_mismatches(case: InstructionRefinementCase, evm_state: SMTState, x86_state: SMTState):
    return [
        evm_state.evm_storage.sload(BitVecVal(key, 256))
        != x86_state.evm_storage.sload(BitVecVal(key, 256))
        for key in case.storage_check_keys
    ]


def _transient_storage_mismatches(
    case: InstructionRefinementCase,
    evm_state: SMTState,
    x86_state: SMTState,
):
    return [
        evm_state.evm_transient_storage.tload(BitVecVal(key, 256))
        != x86_state.evm_transient_storage.tload(BitVecVal(key, 256))
        for key in case.transient_storage_check_keys
    ]


def _evm_operator(case: InstructionRefinementCase) -> EvmOperator:
    return EvmOperator(
        kind=case.evm_kind,
        pc=case.evm_pc,
        immediate=case.evm_immediate,
        param=case.evm_param,
    )


def _load_stack_slot(state: SMTState, arity: int, slot_index: int):
    offsets = _stack_limb_offsets(arity, slot_index)
    z0, z1, z2, z3 = (
        state.x86_memory.load_limb(BitVecVal(offset, 64), domain=MemoryDomain.STACK)
        for offset in offsets
    )
    return Concat(z3, z2, z1, z0)


def _operand_limb_offsets(arity: int) -> tuple[tuple[int, int, int, int], ...]:
    return tuple(
        _stack_limb_offsets(arity, slot_index)
        for slot_index in range(arity)
    )


def _stack_limb_offsets(arity: int, slot_index: int) -> tuple[int, int, int, int]:
    base_offset = -_UINT256_SLOT_BYTES * arity
    return tuple(
        base_offset + slot_index * _UINT256_SLOT_BYTES + limb_index * _LIMB_STRIDE_BYTES
        for limb_index in range(4)
    )
