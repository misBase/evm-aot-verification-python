"""AOT 编译器 amd64 输出中的 CALLDATALOAD slice 摘要。"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, Iterable, List, Optional, Sequence, Tuple, Union

from z3 import BitVec, BitVecVal, Concat, is_bv_value, simplify

from common.calldata import calldataload_no_overflow_assumption, calldataload_word
from state.smt_state import MemoryDomain, SMTState

from .base import (
    SummaryContinuation,
    SummaryDiscoveryContext,
    X86Summary,
)
from x86_64.disassembler import parse_operands
from x86_64.models import Register, X86Block, X86Instruction


CALLDATALOAD_SUMMARY_KIND = "calldataload"
_UINT64_MASK = (1 << 64) - 1
_MAX_NON_WRAPPING_CALLDATALOAD_OFFSET = _UINT64_MASK - 32


@dataclass(frozen=True)
class ConstLimbLocation:
    value: int


@dataclass(frozen=True)
class RegisterLimbLocation:
    reg: Register


@dataclass(frozen=True)
class StackLimbLocation:
    offset: int


LimbLocation = Union[ConstLimbLocation, RegisterLimbLocation, StackLimbLocation]


@dataclass(frozen=True)
class CallDataLoadSummary:
    entry_addr: int
    exit_addr: int
    zero_addr: int
    partial_addr: int
    entry_instruction_index: int
    result_stack_offset: int
    offset_limb_locs: Tuple[LimbLocation, LimbLocation, LimbLocation, LimbLocation]
    clobber_registers: Tuple[Register, ...]
    internal_block_addrs: Tuple[int, ...]
    require_concrete_offset: bool = False
    # True for the fixed codegen (``sub size, offset; cmp size, 32``), whose
    # fast/partial split cannot wrap; False for legacy ``add offset, 32``.
    wrap_free: bool = False


class CallDataLoadSummaryMatchError(ValueError):
    pass


class CallDataLoadSummarySpec:
    kind = CALLDATALOAD_SUMMARY_KIND

    def discover(
        self,
        ctx: SummaryDiscoveryContext,
        *,
        strict: bool = False,
    ) -> Iterable[X86Summary]:
        summaries = discover_calldataload_summaries(ctx.blocks, strict=strict)
        for summary in summaries.values():
            yield X86Summary(
                kind=self.kind,
                entry_addr=summary.entry_addr,
                start_block_addr=summary.entry_addr,
                start_instruction_index=summary.entry_instruction_index,
                continuation=SummaryContinuation(summary.exit_addr, 0),
                covered_block_addrs=summary.internal_block_addrs,
                clobber_registers=summary.clobber_registers,
                payload=summary,
            )

    def apply(
        self,
        summary: X86Summary,
        state: SMTState,
        *,
        fresh_prefix: str,
    ) -> SMTState:
        if not isinstance(summary.payload, CallDataLoadSummary):
            raise TypeError(
                "CALLDATALOAD summary payload must be CallDataLoadSummary, "
                f"got {type(summary.payload)!r}"
            )
        return apply_calldataload_summary(
            summary.payload,
            state,
            fresh_prefix=fresh_prefix,
        )


def offset_expr_from_locations(summary: CallDataLoadSummary, state: SMTState):
    limbs = [_limb_location_expr(loc, state) for loc in summary.offset_limb_locs]
    return Concat(limbs[3], limbs[2], limbs[1], limbs[0])


def apply_calldataload_summary(
    summary: CallDataLoadSummary,
    state: SMTState,
    *,
    fresh_prefix: str = "calldataload_summary",
) -> SMTState:
    """把可信的 CALLDATALOAD 摘要应用到 x86 机器状态。"""
    new_state = state.copy()
    offset_bv = offset_expr_from_locations(summary, state)
    if summary.require_concrete_offset:
        concrete_offset = simplify(offset_bv)
        if not is_bv_value(concrete_offset):
            raise CallDataLoadSummaryMatchError(
                "dynamic CALLDATALOAD summary offset did not simplify to a concrete value"
            )
        concrete_value = concrete_offset.as_long()
        if concrete_value > _MAX_NON_WRAPPING_CALLDATALOAD_OFFSET:
            raise CallDataLoadSummaryMatchError(
                "dynamic CALLDATALOAD summary offset can wrap in offset+32 check"
            )
        offset_bv = BitVecVal(concrete_value, 256)
    omit_overflow_guard = False
    if getattr(state, "assume_calldata_offset_no_overflow", True):
        no_overflow = calldataload_no_overflow_assumption(offset_bv)
        if no_overflow is not None:
            new_state.add_assumption(no_overflow)
            omit_overflow_guard = True
    result = calldataload_word(
        state.calldata,
        state.callengine_input_size_bytes,
        offset_bv,
        omit_overflow_guard=omit_overflow_guard,
        abstract=getattr(state, "abstract_calldataload_words", False),
    )

    r14 = state.x86_registers.get_register(Register.R14)
    base = r14 + BitVecVal(summary.result_stack_offset, 64)
    new_state.x86_memory = state.x86_memory.store_256bit(
        base,
        result,
        domain=MemoryDomain.STACK,
    )

    for reg in summary.clobber_registers:
        new_state.x86_registers.set_register(
            reg,
            BitVec(f"{fresh_prefix}_{summary.entry_addr:x}_{reg.value}", 64),
        )
    for flag in ("CF", "ZF", "SF", "OF"):
        new_state.x86_registers.set_flag(
            flag,
            BitVec(f"{fresh_prefix}_{summary.entry_addr:x}_{flag}", 1),
        )
    return new_state


def discover_calldataload_summaries(
    blocks: Sequence[X86Block],
    *,
    strict: bool = False,
) -> Dict[int, CallDataLoadSummary]:
    """按入口地址发现形如 compileEVMCALLDATALOAD 的 CFG slice。"""
    blocks_by_addr = {block.start_addr: block for block in blocks}
    block_index = {block.start_addr: i for i, block in enumerate(blocks)}
    summaries: Dict[int, CallDataLoadSummary] = {}
    failures: List[str] = []

    for idx, block in enumerate(blocks):
        if _looks_like_calldataload_entry(block, blocks, blocks_by_addr, idx):
            candidate = True
        elif strict:
            candidate = _is_potential_calldataload_entry(
                block,
                blocks,
                blocks_by_addr,
                idx,
            )
        else:
            candidate = False
        if not candidate:
            continue
        try:
            summary = _match_calldataload_at(blocks, blocks_by_addr, block_index, idx)
        except CallDataLoadSummaryMatchError as exc:
            failures.append(f"0x{block.start_addr:x}: {exc}")
            continue
        summaries[summary.entry_addr] = summary

    if strict and failures:
        joined = "; ".join(failures)
        raise CallDataLoadSummaryMatchError(
            f"unmatched CALLDATALOAD-like x86 slice(s): {joined}"
        )
    return summaries


def _limb_location_expr(loc: LimbLocation, state: SMTState):
    if isinstance(loc, ConstLimbLocation):
        return BitVecVal(loc.value & ((1 << 64) - 1), 64)
    if isinstance(loc, RegisterLimbLocation):
        return state.x86_registers.get_register(loc.reg)
    if isinstance(loc, StackLimbLocation):
        r14 = state.x86_registers.get_register(Register.R14)
        return state.x86_memory.load_limb(
            r14 + BitVecVal(loc.offset, 64),
            domain=MemoryDomain.STACK,
        )
    raise TypeError(f"unknown limb location: {loc!r}")


def _match_calldataload_at(
    blocks: Sequence[X86Block],
    blocks_by_addr: Dict[int, X86Block],
    block_index: Dict[int, int],
    entry_idx: int,
) -> CallDataLoadSummary:
    entry = blocks[entry_idx]

    # 1. 入口块末尾的 JNE 必须跳到清零路径：offset 高 192 位非零时，
    #    AOT 编译器 会把 CALLDATALOAD 结果直接清零。
    zero_addr = _jump_target(entry.instructions[-1])
    if zero_addr is None or zero_addr not in blocks_by_addr:
        raise CallDataLoadSummaryMatchError("entry JNE target is not a local zero block")

    # 2. 解析 offset 的四个 64-bit limb：entry 块负责汇总高三 limb，
    #    input-size 块负责拿到低 limb 并检查 offset 是否超过 calldata size。
    high_locs, entry_instruction_index = _parse_high_limb_locations(entry)
    size_block = _next_block(blocks, entry_idx, "missing input-size block")
    size_reg, low_loc = _parse_size_check_block(size_block, zero_addr)

    # 3. prep 块加载 calldata pointer，计算 input+offset，并分出
    #    fast path（完整 32 字节）和 partial path（需要补零）。
    prep_block = _next_block(blocks, entry_idx + 1, "missing calldata prep block")
    offset_reg, mem_begin_reg, partial_addr, wrap_free = _parse_prep_block(
        prep_block,
        size_reg,
        low_loc,
    )
    require_concrete_offset = (
        False if wrap_free else _requires_concrete_low_offset(low_loc)
    )
    if partial_addr not in blocks_by_addr:
        raise CallDataLoadSummaryMatchError("partial path target is not a local block")

    # 4. fast path 必须是四组 qword load + bswap + stack store，
    #    其跳转目标就是 summary 执行完后要继续的 exit block。
    fast_block = _next_block(blocks, entry_idx + 2, "missing fast path block")
    fast_base, exit_addr = _parse_fast_path_block(fast_block, mem_begin_reg)
    if exit_addr not in blocks_by_addr:
        raise CallDataLoadSummaryMatchError("summary exit is not a local block")

    # 5. zero path 必须写同一个 256-bit 结果槽，并且自然落到 exit。
    #    这样 overflow、offset 越界和 fast path 的后继才一致。
    zero_block = blocks_by_addr[zero_addr]
    zero_base = _parse_zero_block(zero_block)
    if zero_base != fast_base:
        raise CallDataLoadSummaryMatchError(
            f"fast/zero result bases differ: {fast_base} vs {zero_base}"
        )
    zero_idx = block_index[zero_addr]
    if zero_idx + 1 >= len(blocks) or blocks[zero_idx + 1].start_addr != exit_addr:
        raise CallDataLoadSummaryMatchError("zero block does not fall through to fast exit")

    # 6. partial path 要覆盖 32 个 byte load/store，并在完成后跳到同一个 exit。
    #    具体每个 byte 的补零行为由 shared calldata summary 统一建模。
    if not _validate_partial_path(
        blocks,
        block_index,
        partial_addr,
        zero_addr,
        exit_addr,
        fast_base,
        mem_begin_reg,
    ):
        raise CallDataLoadSummaryMatchError("partial byte-copy path is incomplete")

    exit_idx = block_index[exit_addr]
    internal_blocks = tuple(
        block.start_addr
        for block in blocks[entry_idx:exit_idx]
    )
    clobbers = _collect_summary_clobber_registers(
        blocks,
        entry_idx,
        exit_idx,
        entry_instruction_index,
    )

    # limb 顺序是 x1（低位）、x2、x3、x4。
    offset_locs = (low_loc, high_locs[0], high_locs[1], high_locs[2])
    _ = offset_reg  # 已作为结构守卫解析；摘要本身不需要它。
    return CallDataLoadSummary(
        entry_addr=entry.start_addr,
        exit_addr=exit_addr,
        zero_addr=zero_addr,
        partial_addr=partial_addr,
        entry_instruction_index=entry_instruction_index,
        result_stack_offset=fast_base,
        offset_limb_locs=offset_locs,
        clobber_registers=clobbers,
        internal_block_addrs=internal_blocks,
        require_concrete_offset=require_concrete_offset,
        wrap_free=wrap_free,
    )


def _looks_like_calldataload_entry(
    block: X86Block,
    blocks: Sequence[X86Block],
    blocks_by_addr: Dict[int, X86Block],
    idx: int,
) -> bool:
    insns = _meaningful(block.instructions)

    # 快速过滤第一层：CALLDATALOAD 的 entry 块以
    # "test overflow_tmp, overflow_tmp; jne zero_block" 收尾。
    if len(insns) < 3 or insns[-1].mnemonic.lower() != "jne":
        return False
    zero_addr = _jump_target(insns[-1])
    zero_block = blocks_by_addr.get(zero_addr) if zero_addr is not None else None
    if zero_block is None:
        return False

    # JNE 的目标必须已经长得像清零结果槽的 zero block；否则只是普通分支。
    try:
        _parse_zero_block(zero_block)
    except CallDataLoadSummaryMatchError:
        return False

    # 倒数第二条 test 必须自测同一个临时寄存器，并且该寄存器前面由立即数
    # 初始化；这对应 compileLocIsUint64 生成的高 limb overflow 汇总值。
    test_insn = insns[-2]
    if test_insn.mnemonic.lower() != "test":
        return False
    ops = parse_operands(test_insn)
    target_reg = ops.get("dest_reg")
    if target_reg is None or target_reg != ops.get("src_reg"):
        return False
    if not _has_overflow_initializer(block, target_reg, test_insn):
        return False

    # 快速过滤最后一层：entry 后继块必须从 callEngine 读取 calldata size
    # ([r13+0x98])，这是 CALLDATALOAD 后续 size check 的固定形状。
    if idx + 1 >= len(blocks):
        return False
    next_insns = _meaningful(blocks[idx + 1].instructions)
    if not next_insns:
        return False
    load_ops = parse_operands(next_insns[0])
    return (
        next_insns[0].mnemonic.lower() == "mov"
        and load_ops.get("dest_reg") is not None
        and load_ops.get("base_reg") == Register.R13
        and load_ops.get("offset") == 0x98
        and load_ops.get("memory_size") == 8
    )


def _is_potential_calldataload_entry(
    block: X86Block,
    blocks: Sequence[X86Block],
    blocks_by_addr: Dict[int, X86Block],
    idx: int,
) -> bool:
    """strict 模式下的宽松候选检查。

    这里故意不做 ``_parse_zero_block`` 这类完整校验。
    strict 模式需要报告“像 CALLDATALOAD 但模板细节不匹配”的 slice；
    fallback 模式则继续使用更窄的快速过滤。
    """
    insns = _meaningful(block.instructions)
    if len(insns) < 3 or insns[-1].mnemonic.lower() != "jne":
        return False

    zero_addr = _jump_target(insns[-1])
    zero_block = blocks_by_addr.get(zero_addr) if zero_addr is not None else None
    if zero_block is None:
        return False

    test_insn = insns[-2]
    if test_insn.mnemonic.lower() != "test":
        return False
    ops = parse_operands(test_insn)
    target_reg = ops.get("dest_reg")
    if target_reg is None or target_reg != ops.get("src_reg"):
        return False
    if not _mentions_overflow_temp(block, target_reg, test_insn):
        return False

    next_block = blocks[idx + 1] if idx + 1 < len(blocks) else None
    return (
        _looks_like_zero_result_block(zero_block)
        or (next_block is not None and _mentions_callengine_input_size(next_block))
    )


def _mentions_overflow_temp(
    block: X86Block,
    target_reg: Register,
    test_insn: X86Instruction,
) -> bool:
    test_idx = block.instructions.index(test_insn)
    for insn in block.instructions[:test_idx]:
        ops = parse_operands(insn)
        if ops.get("dest_reg") == target_reg and insn.mnemonic.lower() in {"mov", "or"}:
            return True
    return False


def _looks_like_zero_result_block(block: X86Block) -> bool:
    zero_stack_stores = 0
    for insn in block.instructions:
        ops = parse_operands(insn)
        if (
            insn.mnemonic.lower() == "mov"
            and ops.get("base_reg") == Register.R14
            and ops.get("memory_size") == 8
            and ops.get("immediate") == 0
        ):
            zero_stack_stores += 1
    return zero_stack_stores >= 2


def _mentions_callengine_input_size(block: X86Block) -> bool:
    for insn in block.instructions:
        ops = parse_operands(insn)
        if (
            ops.get("base_reg") == Register.R13
            and ops.get("offset") == 0x98
            and ops.get("memory_size") == 8
        ):
            return True
    return False


def _has_overflow_initializer(
    block: X86Block,
    target_reg: Register,
    test_insn: X86Instruction,
) -> bool:
    test_idx = block.instructions.index(test_insn)
    for idx in range(test_idx - 1, -1, -1):
        insn = block.instructions[idx]
        ops = parse_operands(insn)
        if insn.mnemonic.lower() == "mov" and ops.get("dest_reg") == target_reg:
            return ops.get("immediate") is not None
    return False


def _parse_high_limb_locations(
    block: X86Block,
) -> Tuple[Tuple[LimbLocation, LimbLocation, LimbLocation], int]:
    insns = _meaningful(block.instructions)
    test_insn = insns[-2]
    test_ops = parse_operands(test_insn)
    target_reg = test_ops.get("dest_reg")
    if target_reg is None or target_reg != test_ops.get("src_reg"):
        raise CallDataLoadSummaryMatchError("entry does not test one temp register")

    test_idx = block.instructions.index(test_insn)
    init_idx = None
    for idx in range(test_idx - 1, -1, -1):
        insn = block.instructions[idx]
        ops = parse_operands(insn)
        if insn.mnemonic.lower() == "mov" and ops.get("dest_reg") == target_reg:
            init_idx = idx
            break
    if init_idx is None:
        raise CallDataLoadSummaryMatchError("entry does not initialize overflow temp")

    init = block.instructions[init_idx]
    init_ops = parse_operands(init)
    if init.mnemonic.lower() != "mov" or init_ops.get("dest_reg") != target_reg:
        raise CallDataLoadSummaryMatchError("entry does not initialize overflow temp")
    init_imm = init_ops.get("immediate")
    if init_imm is None:
        raise CallDataLoadSummaryMatchError("overflow temp initializer is not immediate")
    if init_imm != 0:
        return (
            (
                ConstLimbLocation(init_imm),
                ConstLimbLocation(0),
                ConstLimbLocation(0),
            ),
            init_idx,
        )

    locs: List[LimbLocation] = []
    for insn in block.instructions[init_idx + 1:test_idx]:
        if insn.mnemonic.lower() == "nop":
            continue
        if insn.mnemonic.lower() != "or":
            raise CallDataLoadSummaryMatchError(
                f"unexpected overflow-check instruction: {insn.mnemonic} {insn.op_str}"
            )
        ops = parse_operands(insn)
        if ops.get("dest_reg") != target_reg:
            raise CallDataLoadSummaryMatchError("overflow OR writes a different register")
        loc = _second_operand_location(insn)
        if loc is None:
            raise CallDataLoadSummaryMatchError("unsupported high-limb location")
        locs.append(loc)

    if len(locs) > 3:
        raise CallDataLoadSummaryMatchError("too many high-limb operands")
    while len(locs) < 3:
        locs.append(ConstLimbLocation(0))
    return tuple(locs), init_idx  # type: ignore[return-value]


def _parse_size_check_block(
    block: X86Block,
    zero_addr: int,
) -> Tuple[Register, LimbLocation]:
    insns = _meaningful(block.instructions)
    if len(insns) != 3:
        raise CallDataLoadSummaryMatchError("input-size block is not canonical")

    load_ops = parse_operands(insns[0])
    if (
        insns[0].mnemonic.lower() != "mov"
        or load_ops.get("dest_reg") is None
        or load_ops.get("base_reg") != Register.R13
        or load_ops.get("offset") != 0x98
        or load_ops.get("memory_size") != 8
    ):
        raise CallDataLoadSummaryMatchError("input-size block does not read [r13+0x98]")
    size_reg = load_ops["dest_reg"]

    cmp_insn = next((insn for insn in insns[1:-1] if insn.mnemonic.lower() == "cmp"), None)
    if cmp_insn is None:
        raise CallDataLoadSummaryMatchError("input-size block has no cmp")
    cmp_ops = parse_operands(cmp_insn)
    if cmp_ops.get("dest_reg") != size_reg:
        raise CallDataLoadSummaryMatchError("input-size cmp does not use size register")
    low_loc = _second_operand_location(cmp_insn)
    if low_loc is None:
        raise CallDataLoadSummaryMatchError("unsupported low-limb location")

    if insns[-1].mnemonic.lower() != "jb" or _jump_target(insns[-1]) != zero_addr:
        raise CallDataLoadSummaryMatchError("input-size block does not jump to zero block")
    return size_reg, low_loc


def _requires_concrete_low_offset(low_loc: LimbLocation) -> bool:
    """只接受 x64 ``offset+32`` 不会回绕的可信摘要。

    编译后的 x64 slice 会先执行 64-bit ``add offset, 32``，再选择 fast/partial
    path。共享 helper 建模的是 Go/EVM 中不会回绕的 ``getData(input, offset, 32)``
    语义。常量 offset 可以静态检查；形如 ``4+32`` 的链式编译器 offset 在从 block
    中间开始摘要时可能表现为寄存器，这种情况只有在运行时状态能把完整 256-bit
    offset 化简成安全的具体值时才接受。
    """
    if not isinstance(low_loc, ConstLimbLocation):
        return True
    value = low_loc.value & _UINT64_MASK
    if value > _MAX_NON_WRAPPING_CALLDATALOAD_OFFSET:
        raise CallDataLoadSummaryMatchError(
            "low offset can wrap in x64 offset+32 check"
        )
    return False


def _parse_prep_block(
    block: X86Block,
    size_reg: Register,
    low_loc: LimbLocation,
) -> Tuple[Register, Register, int, bool]:
    insns = _meaningful(block.instructions)
    if len(insns) != 7:
        raise CallDataLoadSummaryMatchError("prep block is not canonical")

    load_offset = insns[0]
    load_ops = parse_operands(load_offset)
    offset_reg = load_ops.get("dest_reg")
    if load_offset.mnemonic.lower() != "mov" or offset_reg is None:
        raise CallDataLoadSummaryMatchError("prep block does not load offset")
    if not _same_location(_second_operand_location(load_offset), low_loc):
        raise CallDataLoadSummaryMatchError("prep offset source disagrees with size check")

    copy_ops = parse_operands(insns[1])
    if (
        insns[1].mnemonic.lower() != "mov"
        or copy_ops.get("dest_reg") is None
        or copy_ops.get("src_reg") != offset_reg
    ):
        raise CallDataLoadSummaryMatchError("prep block does not copy offset")
    offset_copy_reg = copy_ops["dest_reg"]

    ptr_ops = parse_operands(insns[2])
    mem_begin_reg = ptr_ops.get("dest_reg")
    if (
        insns[2].mnemonic.lower() != "mov"
        or mem_begin_reg is None
        or ptr_ops.get("base_reg") != Register.R13
        or ptr_ops.get("offset") != 0x90
        or ptr_ops.get("memory_size") != 8
    ):
        raise CallDataLoadSummaryMatchError("prep block does not read [r13+0x90]")

    add_ptr_ops = parse_operands(insns[3])
    if (
        insns[3].mnemonic.lower() != "add"
        or add_ptr_ops.get("dest_reg") != mem_begin_reg
        or add_ptr_ops.get("src_reg") != offset_copy_reg
    ):
        raise CallDataLoadSummaryMatchError("prep block does not add offset to calldata pointer")

    # Legacy: ``add offset, 32; cmp size, offset`` (wraps near 2^64).
    # Fixed:  ``sub size, offset; cmp size, 32`` (size >= offset already checked).
    size_ops = parse_operands(insns[4])
    cmp_ops = parse_operands(insns[5])
    legacy = (
        insns[4].mnemonic.lower() == "add"
        and size_ops.get("dest_reg") == offset_reg
        and size_ops.get("immediate") == 0x20
        and insns[5].mnemonic.lower() == "cmp"
        and cmp_ops.get("dest_reg") == size_reg
        and cmp_ops.get("src_reg") == offset_reg
    )
    fixed = (
        insns[4].mnemonic.lower() == "sub"
        and size_ops.get("dest_reg") == size_reg
        and size_ops.get("src_reg") == offset_reg
        and insns[5].mnemonic.lower() == "cmp"
        and cmp_ops.get("dest_reg") == size_reg
        and cmp_ops.get("src_reg") is None
        and cmp_ops.get("immediate") == 0x20
    )
    if not (legacy or fixed):
        raise CallDataLoadSummaryMatchError("prep block does not compare remaining size with 32")

    if insns[-1].mnemonic.lower() != "jb":
        raise CallDataLoadSummaryMatchError("prep block does not branch to partial path")
    partial_addr = _jump_target(insns[-1])
    if partial_addr is None:
        raise CallDataLoadSummaryMatchError("partial path target is missing")
    return offset_reg, mem_begin_reg, partial_addr, fixed


def _parse_fast_path_block(block: X86Block, mem_begin_reg: Register) -> Tuple[int, int]:
    insns = _meaningful(block.instructions)
    if len(insns) != 13 or insns[-1].mnemonic.lower() != "jmp":
        raise CallDataLoadSummaryMatchError("fast path shape is incomplete")
    exit_addr = _jump_target(insns[-1])
    if exit_addr is None:
        raise CallDataLoadSummaryMatchError("fast path exit target is missing")

    expected_mem_offsets = [24, 16, 8, 0]
    store_offsets: List[int] = []
    cursor = 0
    for mem_offset in expected_mem_offsets:
        load = insns[cursor]
        bswap = insns[cursor + 1]
        store = insns[cursor + 2]
        cursor += 3

        load_ops = parse_operands(load)
        tmp_reg = load_ops.get("dest_reg")
        if (
            load.mnemonic.lower() != "mov"
            or tmp_reg is None
            or load_ops.get("base_reg") != mem_begin_reg
            or load_ops.get("offset") != mem_offset
            or load_ops.get("memory_size") != 8
        ):
            raise CallDataLoadSummaryMatchError("fast path load sequence is not canonical")

        bswap_ops = parse_operands(bswap)
        if bswap.mnemonic.lower() != "bswap" or bswap_ops.get("dest_reg") != tmp_reg:
            raise CallDataLoadSummaryMatchError("fast path missing bswap")

        store_ops = parse_operands(store)
        if (
            store.mnemonic.lower() != "mov"
            or store_ops.get("base_reg") != Register.R14
            or store_ops.get("src_reg") != tmp_reg
            or store_ops.get("memory_size") != 8
        ):
            raise CallDataLoadSummaryMatchError("fast path store sequence is not canonical")
        store_offsets.append(store_ops.get("offset"))

    base = store_offsets[0]
    if store_offsets != [base, base + 8, base + 16, base + 24]:
        raise CallDataLoadSummaryMatchError("fast path result stack offsets are not contiguous")
    return base, exit_addr


def _parse_zero_block(block: X86Block) -> int:
    insns = [insn for insn in _meaningful(block.instructions) if insn.mnemonic.lower() != "nop"]
    if len(insns) != 4:
        raise CallDataLoadSummaryMatchError("zero block does not have four stores")

    offsets: List[int] = []
    for insn in insns:
        ops = parse_operands(insn)
        if (
            insn.mnemonic.lower() != "mov"
            or ops.get("base_reg") != Register.R14
            or ops.get("memory_size") != 8
            or ops.get("immediate") != 0
        ):
            raise CallDataLoadSummaryMatchError("zero block store is not qword zero")
        offsets.append(ops.get("offset"))
    base = offsets[0]
    if offsets != [base, base + 8, base + 16, base + 24]:
        raise CallDataLoadSummaryMatchError("zero block result stack offsets are not contiguous")
    return base


def _validate_partial_path(
    blocks: Sequence[X86Block],
    block_index: Dict[int, int],
    partial_addr: int,
    zero_addr: int,
    exit_addr: int,
    result_base: int,
    mem_begin_reg: Register,
) -> bool:
    if partial_addr not in block_index or zero_addr not in block_index:
        return False
    partial_idx = block_index[partial_addr]
    zero_idx = block_index[zero_addr]
    if partial_idx >= zero_idx:
        return False

    store_offsets = set()
    load_offsets = set()
    has_exit_jump = False
    for block in blocks[partial_idx:zero_idx]:
        for insn in block.instructions:
            ops = parse_operands(insn)
            mnemonic = insn.mnemonic.lower()
            if (
                mnemonic == "movzx"
                and ops.get("base_reg") == mem_begin_reg
                and ops.get("memory_size") == 1
            ):
                load_offsets.add(ops.get("offset"))
            if (
                mnemonic == "mov"
                and ops.get("base_reg") == Register.R14
                and ops.get("memory_size") == 1
            ):
                store_offsets.add(ops.get("offset"))
            if mnemonic == "jmp" and _jump_target(insn) == exit_addr:
                has_exit_jump = True

    expected_stores = set(range(result_base, result_base + 32))
    expected_loads = set(range(32))
    return (
        has_exit_jump
        and store_offsets == expected_stores
        and load_offsets == expected_loads
    )


def _collect_clobber_registers(blocks: Sequence[X86Block]) -> Tuple[Register, ...]:
    ignored_mnemonics = {"cmp", "test", "jmp", "jb", "jne", "nop"}
    reserved = {Register.R13, Register.R14, Register.R15}
    clobbers = set()
    for block in blocks:
        for insn in block.instructions:
            if insn.mnemonic.lower() in ignored_mnemonics:
                continue
            reg = parse_operands(insn).get("dest_reg")
            if reg is not None and reg not in reserved:
                clobbers.add(reg)
    return tuple(sorted(clobbers, key=lambda reg: reg.value))


def _collect_summary_clobber_registers(
    blocks: Sequence[X86Block],
    entry_idx: int,
    exit_idx: int,
    entry_instruction_index: int,
) -> Tuple[Register, ...]:
    entry = blocks[entry_idx]
    entry_suffix = X86Block(
        start_addr=entry.start_addr,
        end_addr=entry.end_addr,
        instructions=entry.instructions[entry_instruction_index:],
        tag_marker=entry.tag_marker,
        is_jump_target=entry.is_jump_target,
        corresponding_evm_block=entry.corresponding_evm_block,
    )
    return _collect_clobber_registers(
        [entry_suffix, *blocks[entry_idx + 1:exit_idx]]
    )


_RESERVED_REGISTERS = {Register.R13, Register.R14, Register.R15}

_GO_CALLER_SAVED = {
    Register.RAX, Register.RCX, Register.RDX, Register.RSI, Register.RDI,
    Register.R8, Register.R9, Register.R10, Register.R11,
}


def _reg_names(reg: Register) -> Tuple[set, set]:
    """(all alias names, alias names whose write defines the full register)."""
    name = reg.value
    if name.startswith("r") and name[1:].isdigit():
        full = {name, name + "d"}
        return full | {name + "w", name + "b"}, full
    base = name[1:]  # ax, cx, si, ...
    full = {name, "e" + base}
    low8 = {"ax": "al", "cx": "cl", "dx": "dl", "bx": "bl"}.get(base, base + "l")
    return full | {base, low8}, full


# Mnemonic prefix -> 64-bit registers it reads/writes without naming them.
_IMPLICIT_REGS = (
    (("rep", "movs", "stos", "lods", "cmps", "scas"), {"rax", "rcx", "rsi", "rdi"}),
    (("div", "idiv", "cqo", "cdq", "cwd", "cbw", "cwde"), {"rax", "rdx"}),
    (("loop", "jrcxz", "jecxz"), {"rcx"}),
    (("xlat", "xchg", "cmpxchg"), {"rax", "rbx"}),
    (("cpuid", "rdtsc", "syscall"), {"rax", "rbx", "rcx", "rdx", "r11"}),
    (("push", "pop", "leave", "enter"), {"rsp", "rbp"}),
)


def _implicitly_uses(mnemonic, op_str, reg):
    if mnemonic in ("mul", "imul") and "," not in op_str:
        return reg.value in ("rax", "rdx")
    return any(mnemonic.startswith(prefixes) and reg.value in regs
               for prefixes, regs in _IMPLICIT_REGS)


def pointer_tag_dead_at(
    blocks: Sequence[X86Block],
    addr: int,
    reg: Register,
    *,
    max_blocks: int = 512,
    kill_at: Set[int] = frozenset(),
) -> bool:
    """Conservatively prove ``reg``'s pointer tag is never observed from ``addr``.

    Every static path must fully redefine ``reg`` (``mov reg, src`` with ``src``
    not mentioning it) or reach a Go-bridge ``ret`` (which clears caller-saved
    tags) before any other instruction mentions it. Anything else is "live".

    ``kill_at``: block-lockstep cutpoints. Their entry state havocs every
    non-reserved register with tag NONE, so the tag is dead once reached.
    """
    import re

    names, full = _reg_names(reg)
    starts = {}
    for i, b in enumerate(blocks):
        for j, insn in enumerate(b.instructions):
            starts[insn.addr] = (i, j)
    work, seen = [addr], set()
    while work:
        at = work.pop()
        if at in seen:
            continue
        seen.add(at)
        if at in kill_at and reg not in _RESERVED_REGISTERS:
            continue
        if len(seen) > max_blocks or at not in starts:
            return False
        bi, j = starts[at]
        block = blocks[bi]
        killed = False
        for insn in block.instructions[j:]:
            mnemonic = insn.mnemonic.lower()
            if mnemonic.startswith("nop"):
                continue
            # Implicit register operands never appear in op_str; treat as live.
            if _implicitly_uses(mnemonic, insn.op_str, reg):
                return False
            dest, _, src = insn.op_str.partition(",")
            if set(re.findall(r"[a-z0-9]+", insn.op_str)) & names:
                if (mnemonic == "mov" and dest.strip() in full
                        and not set(re.findall(r"[a-z0-9]+", src)) & names):
                    killed = True
                    break
                return False
            if mnemonic == "ret":
                if reg not in _GO_CALLER_SAVED:
                    return False
                killed = True
                break
            if mnemonic == "call":
                return False
        if killed:
            continue
        last = block.instructions[-1]
        mnemonic = last.mnemonic.lower()
        if mnemonic.startswith("j"):
            target = _jump_target(last)
            if target is None:
                return False
            work.append(target)
            if mnemonic == "jmp":
                continue
        if bi + 1 >= len(blocks):
            return False
        work.append(blocks[bi + 1].start_addr)
    return True


def _second_operand_location(insn: X86Instruction) -> Optional[LimbLocation]:
    ops = parse_operands(insn)
    src_reg = ops.get("src_reg")
    if src_reg is not None:
        return RegisterLimbLocation(src_reg)
    immediate = ops.get("immediate")
    if immediate is not None:
        return ConstLimbLocation(immediate)
    if (
        ops.get("is_memory")
        and ops.get("base_reg") == Register.R14
        and ops.get("memory_size") == 8
    ):
        return StackLimbLocation(ops.get("offset"))
    return None


def _same_location(left: Optional[LimbLocation], right: LimbLocation) -> bool:
    return left == right


def _meaningful(insns: Sequence[X86Instruction]) -> List[X86Instruction]:
    return [insn for insn in insns if insn.mnemonic.lower() != "nop"]


def _next_block(blocks: Sequence[X86Block], idx: int, error: str) -> X86Block:
    next_idx = idx + 1
    if next_idx >= len(blocks):
        raise CallDataLoadSummaryMatchError(error)
    return blocks[next_idx]


def _jump_target(insn: X86Instruction) -> Optional[int]:
    return parse_operands(insn).get("jump_target")
