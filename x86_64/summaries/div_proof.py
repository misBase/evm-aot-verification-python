"""Per-slice lemma for compileEVMDivWithReg summaries (fail-closed, cached).

Proved ONCE per slice shape on a fully generic state (every field a fresh
constant, via generalize_state), with only the stack geometry the RESUME block
re-establishes built in (R14 = stack_base + byte_offset, R15 = memory_base):

  * the raw slice -- the builtin bridge through GoFunctionSemantics included,
    no summaries -- runs to the join on every path (finite, complete CFG);
  * the raw path conditions cover the whole input space ("coverage");
  * every assumption a raw path adds is implied by its own path condition;
  * on each path the ENTIRE raw state equals apply_div_summary's state
    ("effect_i": every leaf of SMTState, metadata included), where the
    summary's fresh clobber registers/flags are witnessed by the raw values and
    its builtin choice bit by builtin_taken_condition.

A hit state satisfying the geometry is an instance of the generic state
(substitute each generic constant by the hit's field value), so the raw slice
and the summary agree on it. Failure or unknown raises DivProofError.
"""

from __future__ import annotations

from dataclasses import dataclass
from hashlib import sha256
from time import monotonic
from typing import Sequence, Tuple

from z3 import And, BitVecVal, Not, Or, substitute

from common.uint256 import Uint256
from state.smt_state import MemoryDomain, SMTState
from x86_64.aot_profile import GO_HPC_EVM_PROFILE, X86AOTProfile
from x86_64.models import Register, X86Block

from .base import X86Summary
from .div import (
    DIV_FLAGS,
    DivSummary,
    apply_div_summary,
    builtin_taken_condition,
)


class DivProofError(ValueError):
    def __init__(self, entry_addr: int, label: str, reason: str, *, from_cache: bool = False):
        super().__init__(f"entry=0x{entry_addr:x}, label={label}, reason={reason}")
        self.entry_addr, self.label, self.reason, self.from_cache = entry_addr, label, reason, from_cache


@dataclass(frozen=True)
class DivLemma:
    key: str
    path_count: int
    obligations: tuple          # verification.block_equivalence.Obligation records
    initial_pointer_tags: tuple  # (R14 tag, R15 tag) the generic state was proved with

    @property
    def complete(self):
        names = [o.name for o in self.obligations]
        return (self.path_count > 0 and "coverage" in names and len(set(names)) == len(names)
                and all(f"effect_{i}" in names for i in range(self.path_count))
                and all(o.proved for o in self.obligations))


def generic_div_state(summary: DivSummary) -> SMTState:
    from state.x86_state import PointerTag
    from verification.block_summaries import generalize_state

    base = SMTState()
    for reg in Register:
        base.x86_registers.set_register(reg, base.x86_registers.get_register(reg))
    for flag in (*DIV_FLAGS, "DF"):
        base.x86_registers.set_flag(flag, base.x86_registers.get_flag(flag))
    state = generalize_state(base)
    regs = state.x86_registers
    regs.set_register(Register.R14, state.callengine_stack_base + state.callengine_stack_byte_offset)
    regs.set_pointer_tag(Register.R14, PointerTag.STACK_PTR)
    regs.set_register(Register.R15, state.callengine_memory_base)
    regs.set_pointer_tag(Register.R15, PointerTag.EVM_PTR)
    return state


def _slice_blocks(summary: X86Summary, blocks: Sequence[X86Block]):
    from verification.block_partition import split_at_cutpoints

    payload: DivSummary = summary.payload
    keep = set(summary.covered_block_addrs) | {payload.continuation_addr}
    local = [b for b in blocks if b.start_addr in keep]
    if {b.start_addr for b in local} != keep:
        raise DivProofError(payload.entry_addr, "structure", "slice block missing")
    return split_at_cutpoints(local, {payload.entry_addr, payload.continuation_addr})


_EFFECT_RETRY_FACTOR = 4  # ponytail: budget of the one retry of an unknown effect, in query timeouts


def prove_div_slice(summary: X86Summary, blocks: Sequence[X86Block], *,
                    profile: X86AOTProfile = GO_HPC_EVM_PROFILE, timeout_ms: int = 30_000,
                    max_depth: int = 200) -> DivLemma:
    from verification.block_equivalence import Obligation, solve_query
    from verification.block_summaries import _equal_state, refute_goal
    from verification.loop_induction import run_x86_segment

    payload: DivSummary = summary.payload
    entry, join = payload.entry_addr, payload.continuation_addr

    def fail(label, reason):
        raise DivProofError(entry, label, reason)

    records = []

    def check(name, formula):
        started = monotonic()
        answer = solve_query(formula, timeout_ms)
        records.append(Obligation(name, formula.sexpr(), answer, "unsat", monotonic() - started))
        if answer != "unsat":
            fail(name, f"solver={answer}")

    before = generic_div_state(payload)
    raw, defects, _ = run_x86_segment(_slice_blocks(summary, blocks), before.copy(), entry, {join},
                                      max_depth=max_depth, aot_profile=profile,
                                      use_reachability_check=True)
    if defects or not raw:
        fail("raw", "incomplete raw execution: " + "; ".join(defects))
    if any(p.kind == "terminal" or p.location != join for p in raw):
        fail("raw", "a raw path does not reach the join")
    check("coverage", Not(Or(*(p.condition for p in raw))))

    candidate, took = apply_div_summary(payload, before.copy(), fresh_prefix="div_lemma", profile=profile)
    if candidate.assumptions or candidate.pending_errors or candidate.pending_constraints:
        fail("summary", "summary introduced assumptions/effects")
    r14 = before.x86_registers.get_register(Register.R14)

    def limbs(offsets):
        return Uint256(*(before.x86_memory.load_limb(r14 + BitVecVal(o, 64), domain=MemoryDomain.STACK)
                         for o in offsets))
    took_witness = builtin_taken_condition(limbs(payload.dividend_offsets), limbs(payload.divisor_offsets))
    for i, path in enumerate(raw):
        for k, assumption in enumerate(path.state.assumptions or []):
            check(f"assumption_{i}_{k}", And(path.condition, Not(assumption)))
        witnesses = [(took, took_witness)]
        for reg in payload.clobber_registers:
            witnesses.append((candidate.x86_registers.get_register(reg), path.state.x86_registers.get_register(reg)))
        for flag in DIV_FLAGS:
            witnesses.append((candidate.x86_registers.get_flag(flag), path.state.x86_registers.get_flag(flag)))
        try:
            goal = substitute(_equal_state(path.state, candidate), *witnesses)
        except ValueError as exc:
            fail(f"effect_{i}", str(exc))
        started = monotonic()
        answer, split = refute_goal(path.condition, goal, timeout_ms)
        if answer == "unknown":
            # One retry with a larger budget: the lemma is proved once per slice shape and serves
            # every node of the process, while a failure fails each node that reaches the slice
            # (PoolManager 22747, slice 0xe5f62: effect_1 needs ~38s alone, unknown under load).
            answer, split = refute_goal(path.condition, goal, _EFFECT_RETRY_FACTOR * timeout_ms)
        records.append(Obligation(f"effect_{i}", And(path.condition, Not(goal)).sexpr(), answer, "unsat",
                                  monotonic() - started, split))
        if answer != "unsat":
            fail(f"effect_{i}", f"raw path state differs from the summary (solver={answer})")
    tags = tuple(before.x86_registers.get_pointer_tag(r) for r in (Register.R14, Register.R15))
    lemma = DivLemma(semantic_key(summary, blocks, profile), len(raw), tuple(records), tags)
    if not lemma.complete:
        fail("certificate", "incomplete lemma")
    return lemma


def semantic_key(summary: X86Summary, blocks: Sequence[X86Block], profile: X86AOTProfile) -> str:
    """Position-independent slice fingerprint: code bytes (relative jumps and
    the rip-relative lea encode the same shape anywhere), the matched offsets
    and the profile tables the raw bridge consults."""
    payload: DivSummary = summary.payload
    code = b"".join(bytes(i.bytes) for b in _slice_blocks(summary, blocks)
                    for i in b.instructions if payload.entry_addr <= i.addr < payload.continuation_addr)
    rest = (payload.dividend_offsets, payload.divisor_offsets, payload.builtin_index,
            payload.builtin_stack_pointer, payload.resume_addr - payload.entry_addr,
            payload.continuation_addr - payload.entry_addr, tuple(r.value for r in payload.clobber_registers),
            sorted(profile.offsets.items()), sorted(profile.status_codes.items()),
            sorted(profile.builtin_functions.items()), profile.stack_sp_bias_limbs)
    return sha256(code + repr(rest).encode()).hexdigest()


# Successes are semantic facts; failures may be budget-dependent, so their key includes the timeout.
_SUCCESS: dict = {}
_FAILURE: dict = {}


def clear_proof_cache() -> None:
    _SUCCESS.clear()
    _FAILURE.clear()


def prove_div_slice_cached(summary: X86Summary, blocks: Sequence[X86Block], *,
                           profile: X86AOTProfile = GO_HPC_EVM_PROFILE,
                           timeout_ms: int = 30_000) -> Tuple[DivLemma, str]:
    key = semantic_key(summary, blocks, profile)
    if key in _SUCCESS:
        return _SUCCESS[key], "cache_hits"
    cached = _FAILURE.get((key, timeout_ms))
    if cached is not None:
        raise DivProofError(cached.entry_addr, cached.label, cached.reason, from_cache=True)
    try:
        lemma = prove_div_slice(summary, blocks, profile=profile, timeout_ms=timeout_ms)
    except DivProofError as exc:
        _FAILURE[(key, timeout_ms)] = exc
        raise
    _SUCCESS[key] = lemma
    return lemma, "proven"
