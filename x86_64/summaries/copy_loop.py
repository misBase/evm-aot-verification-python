"""Trusted Tier-2 summaries for proven codegen copy loops."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

from z3 import (
    And,
    BitVec,
    BitVecVal,
    BoolVal,
    Lambda,
    Not,
    Or,
    Select,
    SolverFor,
    ULE,
    ULT,
    is_and,
    is_select,
    simplify,
    unknown,
    unsat,
)

from common.memory_copy import (
    relational_getdata_copy_memory,
    relational_mcopy_memory,
)
from common.store_forwarding import forward_selects
from state.smt_state import PointerTag, SMTState
from x86_64.loop_analysis import analyze_x86_blocks, build_x86_cfg, is_evm_tag_header
from x86_64.loop_templates import (
    MCOPY_HIGH_BLOCK_TEMPLATES,
    MCOPY_LOW_GLUE_TEMPLATE,
    TEMPLATES,
    match_body_blocks_exact,
    match_straightline_exact,
)
from x86_64.models import Register, X86Block
from x86_64.tier2_semantics import (
    byte_copy_region,
    copy_region_byte,
    mcopy_no_wrap_premises,
)

from .base import (
    SummaryContinuation,
    SummaryDiscoveryContext,
    SummaryMatchError,
    X86Summary,
    SummaryPreconditionError,
    X86SummarySpec,
    require_single_entry,
)


COPY_LOOP_SUMMARY_KIND = "copy_loop"


@dataclass(frozen=True)
class CopyLoopPayload:
    template: str
    binding: Dict[str, object]
    tail_binding: Optional[Dict[str, object]] = None
    shr_binding: Optional[Dict[str, object]] = None


class CopyLoopSummarySpec(X86SummarySpec):
    kind = COPY_LOOP_SUMMARY_KIND

    def discover(
        self,
        ctx: SummaryDiscoveryContext,
        *,
        strict: bool = False,
    ) -> Iterable[X86Summary]:
        yield from discover_copy_loop_summaries(ctx, strict=strict)

    def apply(
        self,
        summary: X86Summary,
        state: SMTState,
        *,
        fresh_prefix: str,
        path_condition=None,
        precondition_timeout_ms: int = 5000,
    ) -> SMTState:
        if not isinstance(summary.payload, CopyLoopPayload):
            raise TypeError(
                "copy_loop summary payload must be CopyLoopPayload, "
                f"got {type(summary.payload)!r}"
            )
        payload = summary.payload
        if payload.template in ("returndata-byte-copy", "makedata-byte-copy"):
            return _apply_byte_copy(
                payload,
                state,
                fresh_prefix=fresh_prefix,
                path_condition=path_condition,
                summary_location=summary.start_key,
                precondition_timeout_ms=precondition_timeout_ms,
            )
        if payload.template == "mcopy-low-word":
            return _apply_mcopy_low(
                payload,
                state,
                fresh_prefix=fresh_prefix,
                path_condition=path_condition,
                summary_location=summary.start_key,
                precondition_timeout_ms=precondition_timeout_ms,
            )
        if payload.template == "mcopy-high-word":
            return _apply_mcopy_high(
                payload,
                state,
                fresh_prefix=fresh_prefix,
                path_condition=path_condition,
                summary_location=summary.start_key,
                precondition_timeout_ms=precondition_timeout_ms,
            )
        raise NotImplementedError(
            f"copy_loop summary apply not implemented for {payload.template}"
        )


def _loop_body_blocks(loop, blocks_by_addr: Dict[int, X86Block]) -> List[X86Block]:
    return [
        blocks_by_addr[addr]
        for addr in sorted(loop.body)
        if addr in blocks_by_addr
    ]


def _reg_tuple(*bindings: Dict[str, object]) -> Tuple[Register, ...]:
    regs = []
    seen = set()
    for binding in bindings:
        for value in binding.values():
            if not isinstance(value, str):
                continue
            try:
                reg = Register(value)
            except ValueError:
                continue
            if reg not in seen:
                regs.append(reg)
                seen.add(reg)
    return tuple(regs)


def _build_preds(succs: Dict[int, Sequence[int]]) -> Dict[int, List[int]]:
    preds: Dict[int, List[int]] = {}
    for src, outs in succs.items():
        for dst in outs:
            preds.setdefault(dst, []).append(src)
    return preds


def discover_copy_loop_summaries(
    ctx: SummaryDiscoveryContext,
    *,
    strict: bool = False,
) -> Iterable[X86Summary]:
    blocks_by_addr = ctx.blocks_by_addr
    analysis, _ = analyze_x86_blocks(ctx.blocks)
    # unresolved_sites 不能再丢掉：§5.4 的单入口检查要靠它判断「有没有目标未知
    # 的跳转可能落进 covered 区」，静态解析不出目标时必须拒绝而不是当作没有边。
    succs, unresolved_sites = build_x86_cfg(ctx.blocks)
    preds = _build_preds(succs)
    loop_by_header = {loop.header: loop for loop in analysis.loops}
    consumed: set[int] = set()
    # strict 模式下"看着像 copy loop 但模板细节对不上"的候选必须**报告**，
    # 而不是静默跳过——静默跳过会让 strict 退化成普通 fallback（该循环照常
    # 逐指令执行，结论仍然健全，但调用方以为折叠生效了）。与 mul summary 的
    # strict 语义保持一致。
    failures: List[str] = []

    for loop in analysis.loops:
        if loop.header in consumed:
            continue
        header_block = blocks_by_addr.get(loop.header)
        if header_block is None or is_evm_tag_header(header_block, blocks_by_addr):
            continue
        matched = match_body_blocks_exact(_loop_body_blocks(loop, blocks_by_addr), loop.header)
        if matched is None:
            if strict and _looks_like_copy_loop(loop, blocks_by_addr):
                failures.append(
                    f"0x{loop.header:x}: copy-loop-shaped body matches no template"
                )
            continue
        name, binding = matched
        if name not in TEMPLATES:
            if strict:
                failures.append(
                    f"0x{loop.header:x}: matched '{name}' which is not a proven template"
                )
            continue
        if name in ("returndata-byte-copy", "makedata-byte-copy"):
            exit_addr = binding.get("@EXIT")
            if not isinstance(exit_addr, int) or exit_addr not in blocks_by_addr:
                if strict:
                    failures.append(
                        f"0x{loop.header:x}: '{name}' has no resolvable @EXIT"
                    )
                continue
            summary = X86Summary(
                kind=COPY_LOOP_SUMMARY_KIND,
                entry_addr=loop.header,
                start_block_addr=loop.header,
                start_instruction_index=0,
                continuation=SummaryContinuation(exit_addr, 0),
                covered_block_addrs=tuple(sorted(loop.body)),
                clobber_registers=_reg_tuple(binding),
                payload=CopyLoopPayload(template=name, binding=dict(binding)),
            )
            # 单入口检查放在 yield **之前**：一条会被绕过的 summary 连注册都不该
            # 发生，拖到执行期才发现就已经晚了（那时部分路径已按折叠语义走完）。
            require_single_entry(summary, succs, unresolved_sites)
            consumed.add(loop.header)
            yield summary
            continue

        if name == "mcopy-low-word":
            summary = _discover_mcopy_low(
                loop, binding, loop_by_header, blocks_by_addr, succs
            )
            if summary is not None:
                # cluster 的 covered 区是**拼**出来的（word 循环 + glue + tail
                # 循环），不像单个 natural loop 那样天然前驱闭合，这里是单入口
                # 检查真正有牙齿的地方。
                require_single_entry(summary, succs, unresolved_sites)
                consumed.update(summary.covered_block_addrs)
                yield summary
            elif strict:
                failures.append(
                    f"0x{loop.header:x}: 'mcopy-low-word' cluster discovery failed"
                )
            continue

        if name == "mcopy-high-word":
            summary = _discover_mcopy_high(
                loop, binding, loop_by_header, blocks_by_addr, succs, preds
            )
            if summary is not None:
                # 同 FromLow：三段复合 cluster 的 covered 区靠 preds 反走拼成，
                # 其中 shr/tail 循环头与 glue 块的外部前驱没有任何结构性保证。
                require_single_entry(summary, succs, unresolved_sites)
                consumed.update(summary.covered_block_addrs)
                yield summary
            elif strict:
                failures.append(
                    f"0x{loop.header:x}: 'mcopy-high-word' cluster discovery failed"
                )

    if strict and failures:
        # generator：调用方遍历完才会看到这个异常，与 mul summary 的 strict
        # 语义一致（那边是普通函数，末尾直接 raise）。
        raise SummaryMatchError(
            "unmatched copy-loop-shaped x86 loop(s): " + "; ".join(failures)
        )


def _looks_like_copy_loop(loop, blocks_by_addr: Dict[int, X86Block]) -> bool:
    """粗判「这个循环看着像 memcpy」——只用于 strict 模式的**报告**。

    保守取向：宁可漏报（不报告一个真的畸形候选）也不误报（把普通循环当成
    copy loop 报出来）。判据是循环体里同时有**内存读**与**内存写**，这正是
    codegen 拷贝循环的形状；不满足的循环连候选都算不上，静默跳过没有信息量。

    这个函数**不参与任何证明**，只决定 strict 模式下是否发出一条诊断。
    """
    reads = writes = False
    for addr in loop.body:
        block = blocks_by_addr.get(addr)
        if block is None:
            continue
        for insn in block.instructions:
            if insn.mnemonic != "mov":
                continue
            operands = insn.op_str
            if "ptr [" not in operands:
                continue
            if operands.strip().startswith(("qword ptr [", "byte ptr [",
                                            "dword ptr [", "word ptr [")):
                writes = True
            else:
                reads = True
    return reads and writes


def _discover_mcopy_low(
    loop,
    binding: Dict[str, object],
    loop_by_header,
    blocks_by_addr: Dict[int, X86Block],
    succs: Dict[int, Sequence[int]],
) -> Optional[X86Summary]:
    tail_addr = binding.get("@TAIL")
    exit_addr = binding.get("@EXIT")
    if not isinstance(tail_addr, int) or not isinstance(exit_addr, int):
        return None
    tail_loop = None
    tail_binding = None
    glue_blocks: Tuple[int, ...] = ()
    for candidate in loop_by_header.values():
        tail_match = match_body_blocks_exact(
            _loop_body_blocks(candidate, blocks_by_addr),
            candidate.header,
        )
        if tail_match is None:
            continue
        tail_name, candidate_binding = tail_match
        if tail_name != "mcopy-byte-tail":
            continue
        if candidate_binding.get("@EXIT") != exit_addr:
            continue
        if (
            candidate_binding.get("DST"),
            candidate_binding.get("T"),
            candidate_binding.get("S"),
        ) != (binding.get("DST"), binding.get("T"), binding.get("S")):
            continue
        chain = _single_chain(tail_addr, candidate.header, succs)
        # glue 恰一块：跨界 qword 载入（连通性之外还要指令级精确匹配）
        if chain is None or len(chain) != 1 or chain[0] not in blocks_by_addr:
            continue
        if match_straightline_exact(
            blocks_by_addr[chain[0]].instructions,
            MCOPY_LOW_GLUE_TEMPLATE,
            binding,
        ) is None:
            continue
        tail_loop = candidate
        tail_binding = candidate_binding
        glue_blocks = chain
        break
    if tail_loop is None or tail_binding is None:
        return None
    if exit_addr not in blocks_by_addr:
        return None
    covered = tuple(sorted(set(loop.body) | set(glue_blocks) | set(tail_loop.body)))
    return X86Summary(
        kind=COPY_LOOP_SUMMARY_KIND,
        entry_addr=loop.header,
        start_block_addr=loop.header,
        start_instruction_index=0,
        continuation=SummaryContinuation(exit_addr, 0),
        covered_block_addrs=covered,
        clobber_registers=_reg_tuple(binding, tail_binding),
        payload=CopyLoopPayload(
            template="mcopy-low-word",
            binding=dict(binding),
            tail_binding=dict(tail_binding),
        ),
    )


def _discover_mcopy_high(
    loop,
    binding: Dict[str, object],
    loop_by_header,
    blocks_by_addr: Dict[int, X86Block],
    succs: Dict[int, Sequence[int]],
    preds: Dict[int, List[int]],
) -> Optional[X86Summary]:
    """FromHigh 三段复合：preamble/align + word 循环 + glue×2 + shr + tail。

    入口取 preamble 块（与 prove_mcopy_high_composition 的证明锚点一致，
    寄存器干净：DST=r15+d0, SRC=r15+s0, S=size0），防御分支 preamble→glue2
    被整体吞进替换。所有结构/指令校验 fail-closed，配不上返回 None。
    """

    exit_addr = binding.get("@EXIT")
    exit2_addr = binding.get("@EXIT2")
    if not isinstance(exit_addr, int) or exit_addr not in blocks_by_addr:
        return None
    if not isinstance(exit2_addr, int) or exit2_addr not in blocks_by_addr:
        return None

    # shr 段：word 的 jl 出口经恰两块 glue（DST 回退 + 跨界载入/计数装载）
    # 到 shr 头；glue 把 word 的 SRC 寄存器改写为移位计数（shr.C==word.SRC）
    shr_loop = None
    shr_binding = None
    glue_binding: Optional[Dict[str, object]] = None
    glue_blocks: Tuple[int, ...] = ()
    for candidate in loop_by_header.values():
        cand_match = match_body_blocks_exact(
            _loop_body_blocks(candidate, blocks_by_addr),
            candidate.header,
        )
        if cand_match is None:
            continue
        cand_name, cand_binding = cand_match
        if cand_name != "mcopy-shr-align":
            continue
        if cand_binding.get("T") != binding.get("T"):
            continue
        if cand_binding.get("C") != binding.get("SRC"):
            continue
        chain = _single_chain(exit2_addr, candidate.header, succs)
        if chain is None or len(chain) != 2:
            continue
        if any(addr not in blocks_by_addr for addr in chain):
            continue
        merged = match_straightline_exact(
            blocks_by_addr[chain[0]].instructions,
            MCOPY_HIGH_BLOCK_TEMPLATES["mcopy-high-glue1"],
            binding,
        )
        if merged is None:
            continue
        merged = match_straightline_exact(
            blocks_by_addr[chain[1]].instructions,
            MCOPY_HIGH_BLOCK_TEMPLATES["mcopy-high-glue2"],
            merged,
        )
        if merged is None:
            continue
        shr_loop = candidate
        shr_binding = cand_binding
        glue_binding = merged
        glue_blocks = chain
        break
    if shr_loop is None or shr_binding is None or glue_binding is None:
        return None

    # tail 段：shr 出口即 tail 头；tail 与 word 共出口、共寄存器角色
    tail_header = shr_binding.get("@EXIT")
    tail_loop = loop_by_header.get(tail_header)
    if tail_loop is None:
        return None
    tail_match = match_body_blocks_exact(
        _loop_body_blocks(tail_loop, blocks_by_addr),
        tail_loop.header,
    )
    if tail_match is None:
        return None
    tail_name, tail_binding = tail_match
    if tail_name != "mcopy-byte-tail":
        return None
    if (
        tail_binding.get("DST"),
        tail_binding.get("T"),
        tail_binding.get("S"),
    ) != (binding.get("DST"), binding.get("T"), binding.get("S")):
        return None
    if tail_binding.get("@EXIT") != exit_addr:
        return None

    # preds 反走：word 头的环外前驱唯一 = align 块（单后继直落 word 头），
    # align 的前驱唯一 = preamble（防御分支落点必须是 glue2）
    align_candidates = [
        p for p in preds.get(loop.header, []) if p not in loop.body
    ]
    if len(align_candidates) != 1:
        return None
    align_addr = align_candidates[0]
    if align_addr not in blocks_by_addr:
        return None
    if list(succs.get(align_addr, ())) != [loop.header]:
        return None
    merged = match_straightline_exact(
        blocks_by_addr[align_addr].instructions,
        MCOPY_HIGH_BLOCK_TEMPLATES["mcopy-high-align"],
        glue_binding,
    )
    if merged is None:
        return None
    preamble_candidates = preds.get(align_addr, [])
    if len(preamble_candidates) != 1:
        return None
    preamble_addr = preamble_candidates[0]
    if preamble_addr not in blocks_by_addr:
        return None
    merged = match_straightline_exact(
        blocks_by_addr[preamble_addr].instructions,
        MCOPY_HIGH_BLOCK_TEMPLATES["mcopy-high-preamble"],
        merged,
    )
    if merged is None:
        return None
    if merged.get("@GLUE") != glue_blocks[1]:
        return None
    if set(succs.get(preamble_addr, ())) != {align_addr, glue_blocks[1]}:
        return None

    covered = tuple(sorted(
        set(loop.body)
        | {preamble_addr, align_addr}
        | set(glue_blocks)
        | set(shr_loop.body)
        | set(tail_loop.body)
    ))
    return X86Summary(
        kind=COPY_LOOP_SUMMARY_KIND,
        entry_addr=preamble_addr,
        start_block_addr=preamble_addr,
        start_instruction_index=0,
        continuation=SummaryContinuation(exit_addr, 0),
        covered_block_addrs=covered,
        clobber_registers=_reg_tuple(binding, shr_binding, tail_binding),
        payload=CopyLoopPayload(
            template="mcopy-high-word",
            binding=dict(binding),
            tail_binding=dict(tail_binding),
            shr_binding=dict(shr_binding),
        ),
    )


def _single_chain(
    start: int,
    target: int,
    succs: Dict[int, Sequence[int]],
) -> Optional[Tuple[int, ...]]:
    """Return glue blocks on a no-branch chain from ``start`` to ``target``."""

    if start == target:
        return ()
    chain: List[int] = []
    current = start
    seen = set()
    while current != target:
        if current in seen:
            return None
        seen.add(current)
        outs = list(succs.get(current, ()))
        if len(outs) != 1:
            return None
        chain.append(current)
        current = outs[0]
    return tuple(chain)


def _reg(state: SMTState, reg_name: str):
    return state.x86_registers.get_register(Register(reg_name))


def _set_reg(state: SMTState, reg_name: str, value, tag: PointerTag = PointerTag.NONE):
    reg = Register(reg_name)
    state.x86_registers.set_register(reg, value)
    if tag != PointerTag.NONE:
        state.x86_registers.set_pointer_tag(reg, tag)


def _clobber(state: SMTState, regs: Sequence[Register], flags: Sequence[str], prefix: str):
    for reg in regs:
        state.x86_registers.set_register(reg, BitVec(f"{prefix}_{reg.value}", 64))
    for flag in flags:
        state.x86_registers.set_flag(flag, BitVec(f"{prefix}_{flag}", 1))


def _offset_memory_snapshot(state: SMTState, prefix: str):
    r15 = state.x86_registers.get_register(Register.R15)
    old_abs = state.x86_memory.evm_mem
    normalized_r15 = simplify(r15)
    if normalized_r15.eq(BitVecVal(0, 64)):
        return r15, old_abs, old_abs
    w = BitVec(f"{prefix}_offset", 64)
    return r15, old_abs, Lambda([w], Select(old_abs, r15 + w))


def _replace_evm_mem_from_offset(state: SMTState, r15, new_offset_byte, prefix: str):
    addr = BitVec(f"{prefix}_addr", 64)
    state.x86_memory.evm_mem = Lambda([addr], new_offset_byte(addr - r15))


def _replace_evm_mem_from_offset_array(state: SMTState, r15, new_offset_memory):
    if simplify(r15).eq(BitVecVal(0, 64)):
        state.x86_memory.evm_mem = new_offset_memory
        return
    addr = BitVec("copy_loop_summary_offset_array_addr", 64)
    state.x86_memory.evm_mem = Lambda(
        [addr],
        Select(new_offset_memory, addr - r15),
    )


def _reads_array(term) -> bool:
    seen, work = set(), [term]
    while work:
        t = work.pop()
        if t.get_id() in seen:
            continue
        seen.add(t.get_id())
        if is_select(t):
            return True
        work.extend(t.children())
    return False


def _implication_result(
    path_condition,
    assumptions,
    premise,
    timeout_ms: int = 5000,
    *,
    _forward_cache=None,
):
    if isinstance(path_condition, bool):
        path_condition = BoolVal(path_condition)
    path_condition = path_condition if path_condition is not None else BoolVal(True)
    path_terms = (
        list(path_condition.children()) if is_and(path_condition) else [path_condition]
    )
    assumption_terms = [simplify(term) for term in assumptions]
    # Forwarding a premise that itself reads a long Store chain (copy operands
    # loaded from the EVM stack) measured ~10 s per Safe copy hit, while the
    # plain query was decided in 0.2 s. Try that first, bounded: UNSAT proves
    # the implication; any other answer falls through to the exact path below.
    if _reads_array(premise):
        solver = SolverFor("QF_AUFBV")
        solver.set("timeout", min(timeout_ms, 2000))
        solver.add(simplify(And(*assumptions, path_condition, Not(premise)),
                            expand_select_store=True))
        if solver.check() == unsat:
            return unsat
    # Copy operands are commonly loaded through a long call-engine Store chain.
    # Resolve only syntactically provable Select-over-Store hits before asking
    # Z3; ``forward_selects`` never assumes non-aliasing when it cannot prove
    # it, so this is an exact rewrite rather than an applicability shortcut.
    normalized_premise = simplify(
        forward_selects(premise, _cache=_forward_cache)
    )
    # Dispatch/no-wrap guards are frequently carried verbatim in the local
    # path condition.  Consume only an exact structural antecedent fact before
    # building a solver: conjunctions may be flattened, while Or/Not and all
    # other Boolean structure remain opaque.  ``forward_selects`` and
    # ``simplify`` are exact rewrites, and ``eq`` is Z3 AST equality, so a miss
    # merely falls through to the existing fail-closed solver path.
    antecedent_stack = [*assumptions, path_condition]
    while antecedent_stack:
        antecedent = antecedent_stack.pop()
        if isinstance(antecedent, bool):
            antecedent = BoolVal(antecedent)
        if is_and(antecedent):
            antecedent_stack.extend(antecedent.children())
            continue
        if antecedent.eq(normalized_premise):
            return unsat
        normalized_antecedent = simplify(
            forward_selects(antecedent, _cache=_forward_cache)
        )
        if normalized_antecedent.eq(normalized_premise):
            return unsat
        # An exact simplification can expose a conjunction that was not
        # syntactically visible in the original antecedent atom.
        if is_and(normalized_antecedent):
            antecedent_stack.extend(normalized_antecedent.children())
            continue
    negated_premise = simplify(Not(normalized_premise))

    def check(terms, budget_ms, blast=False):
        solver = SolverFor("QF_AUFBV")
        solver.set("timeout", budget_ms)
        if blast:
            solver.add(*(simplify(term, blast_select_store=True)
                         for term in (*assumption_terms, *terms, negated_premise)))
        else:
            solver.add(*assumption_terms)
            solver.add(*(simplify(term) for term in terms))
            solver.add(negated_premise)
        return solver.check()

    # Local memory-grow/dispatch constraints sit near the tail.  Proving the
    # implication from a suffix is sound because it weakens the antecedent.
    slice_budget = min(timeout_ms, 10_000)
    for size in (4, 16, 64, 256):
        if size >= len(path_terms):
            break
        result = check(path_terms[-size:], slice_budget)
        if result == unsat:
            return result
    result = check(path_terms, timeout_ms)
    if result == unknown:
        # Copy operands read through store chains over lambda arrays (earlier copy
        # results): blasted into ites (an exact rewrite, so its UNSAT is exact) the
        # query is decided where this one is not (Aave 7200 x86 0x72fc8 no-wrap: unknown).
        result = check(path_terms, timeout_ms, blast=True)
    return result


def _prove_implied(path_condition, assumptions, premise, timeout_ms: int = 5000) -> bool:
    return _implication_result(
        path_condition, assumptions, premise, timeout_ms=timeout_ms
    ) == unsat


def _require_implied(
    *,
    path_condition,
    assumptions,
    premise,
    label: str,
    summary_location=None,
    timeout_ms: int = 5000,
) -> None:
    result = _implication_result(
        path_condition, assumptions, premise, timeout_ms=timeout_ms
    )
    if result != unsat:
        raise SummaryPreconditionError(
            kind=COPY_LOOP_SUMMARY_KIND,
            label=label,
            premise=premise,
            result=result,
            location=summary_location,
        )


def _require_all_implied(
    *,
    path_condition,
    assumptions,
    labelled_premises: Sequence[Tuple[str, object]],
    summary_location=None,
    timeout_ms: int = 5000,
) -> None:
    """Prove all premises, falling back to equivalent component obligations.

    The combined implication is only a fast path.  A solver ``unknown`` for
    the conjunction does not imply that any individual premise is unknown:
    proving every ``antecedent => premise_i`` separately is logically
    equivalent to proving ``antecedent => And(premise_i)`` and is often much
    easier for the bit-vector solver.  We therefore accept the summary only
    when every component query is UNSAT; SAT and unknown remain fail-closed.
    """

    combined = And(*(premise for _, premise in labelled_premises))
    # Keep forwarding local to one summary hit.  The combined expression and
    # its component premises share almost all Store/Select subterms, while a
    # process-wide cache would unnecessarily retain large path ASTs.
    forward_cache = {}
    result = _implication_result(
        path_condition,
        assumptions,
        combined,
        timeout_ms=timeout_ms,
        _forward_cache=forward_cache,
    )
    if result == unsat:
        return
    for label, premise in labelled_premises:
        item_result = _implication_result(
            path_condition,
            assumptions,
            premise,
            timeout_ms=timeout_ms,
            _forward_cache=forward_cache,
        )
        if item_result != unsat:
            raise SummaryPreconditionError(
                kind=COPY_LOOP_SUMMARY_KIND,
                label=label,
                premise=premise,
                result=item_result,
                location=summary_location,
            )
    # The conjunction follows from the individually proved components.  This
    # is the expected recovery path when the larger combined query timed out.
    if result == unknown:
        return
    raise SummaryPreconditionError(
        kind=COPY_LOOP_SUMMARY_KIND,
        label="combined summary premises",
        premise=combined,
        result=result,
        location=summary_location,
    )


def _require_pointer_tag(
    state: SMTState,
    reg: Register,
    expected: PointerTag,
    label: str,
    summary_location=None,
) -> None:
    actual = state.x86_registers.get_pointer_tag(reg)
    if actual != expected:
        raise SummaryPreconditionError(
            kind=COPY_LOOP_SUMMARY_KIND,
            label=(
                f"{label} requires {reg.value} to carry {expected.value}, "
                f"got {actual.value}"
            ),
            premise=f"pointer-tag({reg.value}) == {expected.value}",
            result="tag-mismatch",
            location=summary_location,
        )


def _require_implied_pointer_value(
    *,
    path_condition,
    assumptions,
    actual,
    expected,
    label: str,
    summary_location=None,
    timeout_ms: int = 5000,
) -> None:
    _require_implied(
        path_condition=path_condition,
        assumptions=assumptions,
        premise=actual == expected,
        label=f"{label} pointer value",
        summary_location=summary_location,
        timeout_ms=timeout_ms,
    )


def _apply_byte_copy(
    payload: CopyLoopPayload,
    state: SMTState,
    *,
    fresh_prefix: str,
    path_condition=None,
    summary_location=None,
    precondition_timeout_ms: int = 5000,
) -> SMTState:
    binding = payload.binding
    result = state.copy()
    r15, _old_abs, m0 = _offset_memory_snapshot(result, fresh_prefix)

    size = _reg(result, binding["S"])
    dst = _reg(result, binding["DST"])
    off = _reg(result, binding["OFF"])
    inp_reg = Register(binding["INP"])
    inp = _reg(result, binding["INP"])
    tag = result.x86_registers.get_pointer_tag(inp_reg)
    assumptions = list(getattr(result, "assumptions", None) or [])

    if payload.template == "returndata-byte-copy":
        _require_pointer_tag(
            result,
            inp_reg,
            PointerTag.RETURNDATA_PTR,
            "returndata-byte-copy source",
            summary_location,
        )
        _require_implied_pointer_value(
            path_condition=path_condition,
            assumptions=assumptions,
            actual=inp,
            expected=result.callengine_return_data_pointer,
            label="returndata-byte-copy source",
            summary_location=summary_location,
            timeout_ms=precondition_timeout_ms,
        )
        source = result.return_data
        length = None
    elif tag == PointerTag.CALLDATA_PTR:
        _require_implied_pointer_value(
            path_condition=path_condition,
            assumptions=assumptions,
            actual=inp,
            expected=result.callengine_input_pointer,
            label="makedata-byte-copy calldata source",
            summary_location=summary_location,
            timeout_ms=precondition_timeout_ms,
        )
        source = result.calldata
        length = _reg(result, binding["LEN"])
    elif tag == PointerTag.CODE_PTR:
        _require_implied_pointer_value(
            path_condition=path_condition,
            assumptions=assumptions,
            actual=inp,
            expected=result.callengine_code_pointer,
            label="makedata-byte-copy code source",
            summary_location=summary_location,
            timeout_ms=precondition_timeout_ms,
        )
        source = result.code
        length = _reg(result, binding["LEN"])
    else:
        raise SummaryPreconditionError(
            kind=COPY_LOOP_SUMMARY_KIND,
            label=(
                "makedata-byte-copy source pointer must be CALLDATA_PTR or "
                f"CODE_PTR, got {tag}"
            ),
            premise="source pointer tag is calldata_ptr or code_ptr",
            result="tag-mismatch",
            location=summary_location,
        )

    premises = [
        ULT(size, BitVecVal(1 << 63, 64)),
        ULE(dst, dst + size),
        ULE(off, off + size),
    ]
    _require_all_implied(
        path_condition=path_condition,
        assumptions=assumptions,
        labelled_premises=[
            (f"{payload.template} no-wrap#{idx}", premise)
            for idx, premise in enumerate(premises)
        ],
        summary_location=summary_location,
        timeout_ms=precondition_timeout_ms,
    )

    if (
        length is not None
        and getattr(result, "abstract_getdata_copy_memory", False)
    ):
        _replace_evm_mem_from_offset_array(
            result,
            r15,
            relational_getdata_copy_memory(
                m0,
                source,
                dst,
                off,
                size,
                length,
            ),
        )
    else:
        def new_offset_byte(w):
            return byte_copy_region(
                source,
                m0,
                dst,
                off,
                size,
                BitVecVal(0, 64),
                w,
                length=length,
            )

        _replace_evm_mem_from_offset(
            result, r15, new_offset_byte, fresh_prefix
        )
    _set_reg(result, binding["S"], BitVecVal(0, 64))
    _clobber(
        result,
        (Register(binding["T"]), Register(binding["B"])),
        ("CF", "ZF", "SF", "OF"),
        fresh_prefix,
    )
    return result


def _apply_mcopy_low(
    payload: CopyLoopPayload,
    state: SMTState,
    *,
    fresh_prefix: str,
    path_condition=None,
    summary_location=None,
    precondition_timeout_ms: int = 5000,
) -> SMTState:
    binding = payload.binding
    result = state.copy()
    r15, _old_abs, m0 = _offset_memory_snapshot(result, fresh_prefix)

    dst_abs = _reg(result, binding["DST"])
    src_abs = _reg(result, binding["SRC"])
    size = _reg(result, binding["S"])
    _require_pointer_tag(
        result,
        Register(binding["DST"]),
        PointerTag.EVM_PTR,
        "mcopy-low-word destination",
        summary_location,
    )
    _require_pointer_tag(
        result,
        Register(binding["SRC"]),
        PointerTag.EVM_PTR,
        "mcopy-low-word source",
        summary_location,
    )
    d0 = dst_abs - r15
    s0 = src_abs - r15

    assumptions = list(getattr(result, "assumptions", None) or [])
    # FromLow has two dispatch reasons:
    #
    #   dst <= src  ||  size <= 8
    #
    # The second case is safe even for a reversed overlap.  The generated
    # code loads the only qword before performing any tail stores, so no
    # source byte can be destroyed before it is read.  Requiring d0 <= s0
    # unconditionally would reject valid small MCOPY paths.
    low_half_limit = BitVecVal(1 << 63, 64)
    direction_or_small = Or(
        ULE(d0, s0),
        ULE(size, BitVecVal(8, 64)),
        And(
            r15 == BitVecVal(0, 64),
            ULT(d0, low_half_limit),
            ULT(s0, low_half_limit),
            dst_abs <= src_abs,
        ),
    )
    low_premises = [
        (
            "mcopy-low dispatch premise with normalized layout",
            direction_or_small,
        ),
        *(
            (f"mcopy-low no-wrap#{idx}", premise)
            for idx, premise in enumerate(mcopy_no_wrap_premises(d0, s0, size))
        ),
    ]
    _require_all_implied(
        path_condition=path_condition,
        assumptions=assumptions,
        labelled_premises=low_premises,
        summary_location=summary_location,
        timeout_ms=precondition_timeout_ms,
    )

    if getattr(result, "abstract_mcopy_memory", False):
        _replace_evm_mem_from_offset_array(
            result,
            r15,
            relational_mcopy_memory(m0, d0, s0, size),
        )
    else:
        def new_offset_byte(w):
            return copy_region_byte(m0, d0, s0, size, w)

        _replace_evm_mem_from_offset(result, r15, new_offset_byte, fresh_prefix)
    _set_reg(result, binding["DST"], dst_abs + size, PointerTag.EVM_PTR)
    _set_reg(result, binding["S"], BitVecVal(0, 64))
    # SRC **必须 clobber，不能设成 src_abs + size**。
    #
    # `compileEVMMCOPYFromLow` 的两段循环对 SRC 的处理不对称：word 循环每轮
    # `ADDQ 8, srcReg`，而尾字节循环只有 `SUBQ 1, sizeReg` + `ADDQ 1, dstReg`
    # ——**不动 srcReg**（尾循环开始前已 `MOVQ [srcReg], tmp` 把最后那个 qword
    # 整个载入，之后不再访存）。因此真实终值是 `s0 + 8*⌊size/8⌋`：
    #   - size=9  ⇒ 真实 s0+8，写成 s0+9 就错了；
    #   - size=1..7 ⇒ word 循环一轮不跑，SRC 完全不变。
    #
    # 而且复合引理 `prove_mcopy_low_composition` 只证了 tmp / mem / DST / S，
    # **没有**证 SRC 的终值——summary 断言一个没有引理支撑、事实上还错误的值，
    # 后续机器码若读 SRC 就会拿到错误状态并可能掩盖不等价（假绿）。
    #
    # 保守 clobber 与 FromHigh 一致：读到自由符号只会伪 SAT（降级）。要恢复
    # 精确值，得先在引理里把 `SRC = s0 + 8*⌊size/8⌋` 证出来。
    _clobber(
        result,
        (Register(binding["SRC"]), Register(binding["T"])),
        ("CF", "ZF", "SF", "OF"),
        fresh_prefix,
    )
    return result


def _apply_mcopy_high(
    payload: CopyLoopPayload,
    state: SMTState,
    *,
    fresh_prefix: str,
    path_condition=None,
    summary_location=None,
    precondition_timeout_ms: int = 5000,
) -> SMTState:
    binding = payload.binding
    result = state.copy()
    r15, _old_abs, m0 = _offset_memory_snapshot(result, fresh_prefix)

    dst_abs = _reg(result, binding["DST"])
    src_abs = _reg(result, binding["SRC"])
    size = _reg(result, binding["S"])
    _require_pointer_tag(
        result,
        Register(binding["DST"]),
        PointerTag.EVM_PTR,
        "mcopy-high-word destination",
        summary_location,
    )
    _require_pointer_tag(
        result,
        Register(binding["SRC"]),
        PointerTag.EVM_PTR,
        "mcopy-high-word source",
        summary_location,
    )
    d0 = dst_abs - r15
    s0 = src_abs - r15

    assumptions = list(getattr(result, "assumptions", None) or [])
    # 方向与 size 是 FromHigh 分派分支自身保证的硬前提，证不出即拒绝。
    low_half_limit = BitVecVal(1 << 63, 64)
    high_premises = [
        (
            "mcopy-high direction premise s0<d0 or normalized signed dispatch",
            Or(
                ULT(s0, d0),
                And(
                    r15 == BitVecVal(0, 64),
                    ULT(d0, low_half_limit),
                    ULT(s0, low_half_limit),
                    src_abs < dst_abs,
                ),
            ),
        ),
        ("mcopy-high size premise 8<size", ULT(BitVecVal(8, 64), size)),
        *(
            (f"mcopy-high no-wrap#{idx}", premise)
            for idx, premise in enumerate(mcopy_no_wrap_premises(d0, s0, size))
        ),
    ]
    _require_all_implied(
        path_condition=path_condition,
        assumptions=assumptions,
        labelled_premises=high_premises,
        summary_location=summary_location,
        timeout_ms=precondition_timeout_ms,
    )

    # 复合定理：FromHigh 三段净内存效果坍缩为与 FromLow 相同的闭式。
    if getattr(result, "abstract_mcopy_memory", False):
        _replace_evm_mem_from_offset_array(
            result,
            r15,
            relational_mcopy_memory(m0, d0, s0, size),
        )
    else:
        def new_offset_byte(w):
            return copy_region_byte(m0, d0, s0, size, w)

        _replace_evm_mem_from_offset(result, r15, new_offset_byte, fresh_prefix)
    # 两个真实出口（word 全拷 je / byte-tail 排空）的 DST/SRC/T 终值发散，
    # 只有 S=0 一致；DST/SRC 设精确值不健全，必须 clobber（tag 随之清空）
    _set_reg(result, binding["S"], BitVecVal(0, 64))
    _clobber(
        result,
        (
            Register(binding["DST"]),
            Register(binding["SRC"]),
            Register(binding["T"]),
        ),
        ("CF", "ZF", "SF", "OF"),
        fresh_prefix,
    )
    return result
