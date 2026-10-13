"""Per-shape lemma for memoryGasCost summaries (fail-closed, cached).

Proved ONCE per template shape on a fully generic state (every field a fresh
constant, via generalize_state; template registers untagged), with the single
premise not G (G = memgas.exit_guard):

  * the raw slice (no summaries) runs to END on every path -- the OOG exit is
    unreachable under not G (finite, complete CFG);
  * the raw path conditions cover not G ("coverage");
  * every assumption a raw path adds is implied by its own path condition;
  * on each path the ENTIRE raw state (side-channel fields and callEngine
    bytes alike) equals apply_memgas_summary's state ("effect_i"), the
    summary's fresh clobber registers/flags witnessed by the raw values.

A hit state is an instance of the generic state (substitute each generic
constant by the hit's field value); its path condition implies not G (the
executor splits on G), so raw slice and summary agree on it. Failure or
unknown raises MemGasProofError.
"""

from __future__ import annotations

from dataclasses import dataclass
from hashlib import sha256
from time import monotonic
from typing import Sequence, Tuple

from z3 import And, Not, Or, substitute

from state.smt_state import SMTState
from x86_64.aot_profile import GO_HPC_EVM_PROFILE, X86AOTProfile
from x86_64.models import Register, X86Block

from .base import X86Summary
from .div_proof import DivProofError
from .memgas import MEMGAS_FLAGS, MemGasSummary, apply_memgas_summary, exit_guard


class MemGasProofError(DivProofError):
    """A DivProofError so every existing fail-closed handler re-raises it."""


@dataclass(frozen=True)
class MemGasLemma:
    key: str
    path_count: int
    obligations: tuple

    @property
    def complete(self):
        names = [o.name for o in self.obligations]
        return (self.path_count > 0 and "coverage" in names and len(set(names)) == len(names)
                and all(f"effect_{i}" in names for i in range(self.path_count))
                and all(o.proved for o in self.obligations))


def generic_memgas_state() -> SMTState:
    from verification.block_summaries import generalize_state

    base = SMTState()
    for reg in Register:
        base.x86_registers.set_register(reg, base.x86_registers.get_register(reg))
    for flag in (*MEMGAS_FLAGS, "DF"):
        base.x86_registers.set_flag(flag, base.x86_registers.get_flag(flag))
    return generalize_state(base)


def _slice_blocks(summary: X86Summary, blocks: Sequence[X86Block]):
    from verification.block_partition import split_at_cutpoints

    p: MemGasSummary = summary.payload
    keep = set(summary.covered_block_addrs) | {p.continuation_addr}
    local = [b for b in blocks if b.start_addr in keep]
    if {b.start_addr for b in local} != keep:
        raise MemGasProofError(p.entry_addr, "structure", "slice block missing")
    return split_at_cutpoints(local, {p.entry_addr, p.continuation_addr})


def prove_memgas_slice(summary: X86Summary, blocks: Sequence[X86Block], *,
                       profile: X86AOTProfile = GO_HPC_EVM_PROFILE, timeout_ms: int = 30_000,
                       max_depth: int = 100) -> MemGasLemma:
    from verification.block_equivalence import Obligation, solve_query
    from verification.block_summaries import _equal_state, refute_goal
    from verification.loop_induction import run_x86_segment

    p: MemGasSummary = summary.payload

    def fail(label, reason):
        raise MemGasProofError(p.entry_addr, label, reason)

    records = []

    def check(name, formula):
        started = monotonic()
        answer = solve_query(formula, timeout_ms)
        records.append(Obligation(name, formula.sexpr(), answer, "unsat", monotonic() - started))
        if answer != "unsat":
            fail(name, f"solver={answer}")

    before = generic_memgas_state()
    premise = Not(exit_guard(p, before))
    initial = before.copy()
    initial.add_assumption(premise)
    raw, defects, _ = run_x86_segment(_slice_blocks(summary, blocks), initial, p.entry_addr,
                                      {p.continuation_addr}, max_depth=max_depth, aot_profile=profile,
                                      use_reachability_check=True)
    if defects or not raw:
        fail("raw", "incomplete raw execution: " + "; ".join(defects))
    if any(q.kind == "terminal" or q.location != p.continuation_addr for q in raw):
        fail("raw", "a raw path does not reach END under the excluded exit guard")
    check("coverage", And(premise, Not(Or(*(q.condition for q in raw)))))

    candidate = apply_memgas_summary(p, before.copy(), fresh_prefix="memgas_lemma", profile=profile)
    if candidate.assumptions or candidate.pending_errors or candidate.pending_constraints:
        fail("summary", "summary introduced assumptions/effects")
    for i, path in enumerate(raw):
        for k, assumption in enumerate(path.state.assumptions or []):
            check(f"assumption_{i}_{k}", And(path.condition, Not(assumption)))
        witnesses = [(candidate.x86_registers.get_register(r), path.state.x86_registers.get_register(r))
                     for r in p.clobber_registers]
        witnesses += [(candidate.x86_registers.get_flag(f), path.state.x86_registers.get_flag(f))
                      for f in MEMGAS_FLAGS]
        try:
            goal = substitute(_equal_state(path.state, candidate), *witnesses)
        except ValueError as exc:
            fail(f"effect_{i}", str(exc))
        started = monotonic()
        answer, split = refute_goal(path.condition, goal, timeout_ms)
        records.append(Obligation(f"effect_{i}", And(path.condition, Not(goal)).sexpr(), answer, "unsat",
                                  monotonic() - started, split))
        if answer != "unsat":
            fail(f"effect_{i}", f"raw path state differs from the summary (solver={answer})")
    lemma = MemGasLemma(semantic_key(summary, blocks, profile), len(raw), tuple(records))
    if not lemma.complete:
        fail("certificate", "incomplete lemma")
    return lemma


def semantic_key(summary: X86Summary, blocks: Sequence[X86Block], profile: X86AOTProfile) -> str:
    """Position-independent fingerprint: the code bytes (relative jumps encode
    the same shape anywhere) minus the OOG exit's bytes -- never executed under
    not G, so its stack-pointer immediate need not split the cache -- plus the
    matched registers and the profile tables the raw slice consults."""
    p: MemGasSummary = summary.payload
    code = b"".join(bytes(i.bytes) for b in _slice_blocks(summary, blocks) for i in b.instructions
                    if p.entry_addr <= i.addr < p.continuation_addr and not p.oog_addr <= i.addr < p.zero_addr)
    rest = (p.oog_addr - p.entry_addr, p.zero_addr - p.entry_addr, p.continuation_addr - p.entry_addr,
            p.size_reg.value, p.fee_reg.value, p.tmp_reg.value, tuple(r.value for r in p.clobber_registers),
            sorted(profile.offsets.items()), sorted(profile.status_codes.items()))
    return sha256(code + repr(rest).encode()).hexdigest()


# Successes are semantic facts; failures may be budget-dependent, so their key includes the timeout.
_SUCCESS: dict = {}
_FAILURE: dict = {}


def clear_proof_cache() -> None:
    _SUCCESS.clear()
    _FAILURE.clear()


def prove_memgas_slice_cached(summary: X86Summary, blocks: Sequence[X86Block], *,
                              profile: X86AOTProfile = GO_HPC_EVM_PROFILE,
                              timeout_ms: int = 30_000) -> Tuple[MemGasLemma, str]:
    key = semantic_key(summary, blocks, profile)
    if key in _SUCCESS:
        return _SUCCESS[key], "cache_hits"
    cached = _FAILURE.get((key, timeout_ms))
    if cached is not None:
        raise MemGasProofError(cached.entry_addr, cached.label, cached.reason, from_cache=True)
    try:
        lemma = prove_memgas_slice(summary, blocks, profile=profile, timeout_ms=timeout_ms)
    except MemGasProofError as exc:
        _FAILURE[(key, timeout_ms)] = exc
        raise
    _SUCCESS[key] = lemma
    return lemma, "proven"
