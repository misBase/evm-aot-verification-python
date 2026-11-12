"""Full-state raw replay gate for 256-bit shift dispatch summaries."""
from hashlib import sha256
from time import monotonic

from z3 import And, Not, Or, substitute

from .div import DIV_FLAGS
from .div_proof import DivLemma, DivProofError, generic_div_state
from .shift import apply_shift_summary


class ShiftProofError(DivProofError):
    """Preserve the existing fail-closed summary proof error handlers."""


def _slice_blocks(summary, blocks):
    from verification.block_partition import split_at_cutpoints
    p = summary.payload
    keep = set(summary.covered_block_addrs) | {p.continuation_addr}
    local = [b for b in blocks if b.start_addr in keep]
    if {b.start_addr for b in local} != keep:
        raise ShiftProofError(p.entry_addr, "structure", "slice block missing")
    return split_at_cutpoints(local, {p.entry_addr, p.continuation_addr})


def semantic_key(summary, blocks):
    p = summary.payload
    code = b"".join(bytes(i.bytes) for b in _slice_blocks(summary, blocks) for i in b.instructions
                    if p.entry_addr <= i.addr < p.continuation_addr)
    rest = (p.high_reg, p.count, p.value_offsets, p.direction, p.clobber_registers,
            p.continuation_addr - p.entry_addr)
    return sha256(code + repr(rest).encode()).hexdigest()


def prove_shift_slice(summary, blocks, *, timeout_ms=30_000, max_depth=100):
    from verification.block_equivalence import Obligation, solve_query
    from verification.block_summaries import _equal_state, refute_goal
    from verification.loop_induction import run_x86_segment

    p, records = summary.payload, []
    def fail(label, reason):
        raise ShiftProofError(p.entry_addr, label, reason)
    def check(name, formula):
        started = monotonic()
        answer = solve_query(formula, timeout_ms)
        records.append(Obligation(name, formula.sexpr(), answer, "unsat", monotonic() - started))
        if answer != "unsat":
            fail(name, f"solver={answer}")

    before = generic_div_state(p)
    raw, defects, _ = run_x86_segment(_slice_blocks(summary, blocks), before.copy(), p.entry_addr,
                                     {p.continuation_addr}, max_depth=max_depth,
                                     use_reachability_check=True)
    if defects or not raw:
        fail("raw", "incomplete raw execution: " + "; ".join(defects))
    if any(path.kind == "terminal" or path.location != p.continuation_addr for path in raw):
        fail("raw", "a raw path does not reach the join")
    check("coverage", Not(Or(*(path.condition for path in raw))))
    candidate = apply_shift_summary(p, before.copy(), fresh_prefix="shift_lemma")
    if candidate.assumptions or candidate.pending_errors or candidate.pending_constraints:
        fail("summary", "summary introduced assumptions/effects")
    for i, path in enumerate(raw):
        for k, assumption in enumerate(path.state.assumptions or []):
            check(f"assumption_{i}_{k}", And(path.condition, Not(assumption)))
        witnesses = [(candidate.x86_registers.get_register(r), path.state.x86_registers.get_register(r))
                     for r in p.clobber_registers]
        witnesses += [(candidate.x86_registers.get_flag(f), path.state.x86_registers.get_flag(f))
                      for f in DIV_FLAGS]
        try:
            goal = substitute(_equal_state(path.state, candidate), *witnesses)
        except ValueError as exc:
            fail(f"effect_{i}", str(exc))
        started = monotonic()
        answer, split = refute_goal(path.condition, goal, timeout_ms)
        records.append(Obligation(f"effect_{i}", And(path.condition, Not(goal)).sexpr(), answer,
                                  "unsat", monotonic() - started, split))
        if answer != "unsat":
            fail(f"effect_{i}", f"raw path state differs from the summary (solver={answer})")
    lemma = DivLemma(semantic_key(summary, blocks), len(raw), tuple(records), ())
    if not lemma.complete:
        fail("certificate", "incomplete lemma")
    return lemma


_SUCCESS, _FAILURE = {}, {}


def clear_proof_cache():
    _SUCCESS.clear()
    _FAILURE.clear()


def prove_shift_slice_cached(summary, blocks, *, timeout_ms=30_000):
    key = semantic_key(summary, blocks)
    if key in _SUCCESS:
        return _SUCCESS[key], "cache_hits"
    if (key, timeout_ms) in _FAILURE:
        exc = _FAILURE[(key, timeout_ms)]
        raise ShiftProofError(exc.entry_addr, exc.label, exc.reason, from_cache=True)
    try:
        lemma = prove_shift_slice(summary, blocks, timeout_ms=timeout_ms)
    except ShiftProofError as exc:
        # Keep error data, not the traceback's solvers and execution states.
        _FAILURE[(key, timeout_ms)] = type(exc)(exc.entry_addr, exc.label, exc.reason, from_cache=exc.from_cache)
        raise
    _SUCCESS[key] = lemma
    return lemma, "proven"
