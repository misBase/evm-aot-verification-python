"""Free-input coverage and full-state replay gates for signed arithmetic slices."""
from hashlib import sha256
from time import monotonic

from z3 import And, Concat, Not, Or, Select, is_array, is_bv, is_const, is_eq, is_quantifier, is_select, is_store, is_true, simplify, substitute

from common.arithmetic import _abs256
from common.uint256 import Uint256
from .div import DIV_FLAGS
from .div_proof import DivLemma, DivProofError, generic_div_state


class SignedProofError(DivProofError):
    pass


def _slice_blocks(summary, blocks):
    from verification.block_partition import split_at_cutpoints
    p = summary.payload
    keep = set(summary.covered_block_addrs) | {p.continuation_addr}
    local = [block for block in blocks if block.start_addr in keep]
    if {block.start_addr for block in local} != keep:
        raise SignedProofError(p.entry_addr, "structure", "slice block missing")
    return split_at_cutpoints(local, {p.entry_addr, p.continuation_addr})


def semantic_key(summary, blocks, profile):
    p = summary.payload
    code = b"".join(bytes(insn.bytes) for block in _slice_blocks(summary, blocks)
                    for insn in block.instructions if p.entry_addr <= insn.addr < p.continuation_addr)
    return sha256(code + repr((summary.kind, p, profile)).encode()).hexdigest()


def _effect_parts(goal):
    """Same-root finite Store arrays agree iff their reads agree at every written address."""
    from verification.block_equivalence import _conjuncts
    parts, scalars = [], []
    for field in _conjuncts(goal):
        if is_true(simplify(field)):
            continue
        if not (is_eq(field) and is_array(field.arg(0))):
            scalars.append(field)
            continue
        a, b = field.children()
        addresses = {}
        def root(array):
            while is_store(array):
                addresses.setdefault(array.arg(1).get_id(), array.arg(1))
                array = array.arg(0)
            return array
        if not root(a).eq(root(b)):
            parts.append(field)
            continue
        keys = list(addresses.values())
        for start in range(0, len(keys), 8):
            chunk = keys[start:start + 8]
            left, right = [Concat(*(Select(array, at) for at in chunk)) if len(chunk) > 1
                           else Select(array, chunk[0]) for array in (a, b)]
            parts.append(left == right)
    if scalars:
        parts.append(And(*scalars))
    return parts


def _abstract_input_bytes(query):
    """UNSAT-only abstraction; the original formula is a syntactic instance."""
    from common.fresh_symbols import FreshSymbols
    seen, work, reads = set(), [query], []
    while work:
        node = work.pop()
        if node.get_id() in seen:
            continue
        seen.add(node.get_id())
        if is_quantifier(node):
            return query
        work.extend(node.children())
        if is_select(node) and is_const(node.arg(0)) and is_bv(node) and node.size() == 8:
            reads.append(node)
    fresh = FreshSymbols(query)
    pairs = [(read, fresh.const(read.sort(), "signed_byte")) for read in reads]
    abstract = substitute(query, *pairs) if pairs else query
    return abstract if substitute(abstract, *((b, a) for a, b in pairs)).eq(query) else query


def refute_signed_effect(pre, goal, timeout_ms):
    from common.store_forwarding import forward_selects, join_extracts
    from verification.block_equivalence import (Obligation, _pure_bv,
        abstract_divrem_congruence, normalize_word_arith, refute_divrem_congruence, solve_pure_bv, solve_query)
    from .div_identity import with_division_identities
    records = []

    def congruence(query):
        arithmetic, _ = abstract_divrem_congruence(query)
        answer = solve_pure_bv(arithmetic, min(3000, timeout_ms)) if _pure_bv(arithmetic) else "unknown"
        proof = Obligation("arithmetic_congruence", arithmetic.sexpr(), answer,
                           required_lemmas=(), provenance="arithmetic_congruence_overapproximation")
        return answer, (proof,) if proof.proved else ()

    for i, part in enumerate(_effect_parts(goal)):
        original = And(pre, Not(part))
        started = monotonic()
        query = simplify(join_extracts(forward_selects(original, {}), {}), bv_sort_ac=True)
        query = _abstract_input_bytes(query)
        query, normalization = normalize_word_arith(query, deadline=monotonic() + timeout_ms / 1000)
        answer, extra = congruence(query)
        identities = ()
        if answer != "unsat":
            query, identities = with_division_identities(query, timeout_ms=timeout_ms)
            if identities:
                answer, extra = congruence(query)
            if answer != "unsat":
                answer = solve_query(query, timeout_ms)
            extra = (*identities, *extra)
        if answer == "unknown":
            _, answer, fallback = refute_divrem_congruence(query, timeout_ms)
            extra = (*identities, *fallback)
        if answer != "unsat":
            return "unknown", ()  # Abstract SAT has no validated original counterexample.
        dependencies = (*normalization, *extra)
        records.append(Obligation(f"part_{i}", original.sexpr(), answer, "unsat", monotonic()-started,
                                  dependencies, tuple(o.name for o in dependencies)))
    return "unsat", tuple(records)


def prove_signed_slice(summary, blocks, *, profile, timeout_ms=30_000, max_depth=400):
    from state.smt_state import MemoryDomain
    from x86_64.models import Register
    from z3 import BitVecVal
    from verification.block_equivalence import Obligation, solve_query
    from verification.block_summaries import _equal_state
    from verification.loop_induction import run_x86_segment
    from .registry import X86SummaryConfig
    if summary.kind == "sdiv":
        from .sdiv import apply_sdiv_summary as apply
        from .div import builtin_taken_condition
    elif summary.kind == "smod":
        from .smod import apply_smod_summary as apply, builtin_taken_condition
    else:
        raise ValueError(f"not a signed summary: {summary.kind}")
    p, records = summary.payload, []

    def fail(label, reason):
        raise SignedProofError(p.entry_addr, label, reason)

    def check(name, formula):
        started = monotonic()
        answer = solve_query(formula, timeout_ms)
        records.append(Obligation(name, formula.sexpr(), answer, "unsat", monotonic()-started))
        if answer != "unsat":
            fail(name, f"solver={answer}")
        return records[-1]

    before = generic_div_state(p)
    raw, defects, _ = run_x86_segment(_slice_blocks(summary, blocks), before.copy(), p.entry_addr,
                                     {p.continuation_addr}, max_depth=max_depth, aot_profile=profile,
                                     summary_config=X86SummaryConfig.disabled(), use_reachability_check=True)
    if defects or not raw:
        fail("raw", "incomplete raw execution: " + "; ".join(defects))
    if any(path.kind == "terminal" or path.location != p.continuation_addr for path in raw):
        fail("raw", "a raw path does not reach the join")
    check("coverage", Not(Or(*(path.condition for path in raw))))
    candidate, took = apply(p, before.copy(), fresh_prefix="signed_lemma", profile=profile)
    if (candidate.assumptions or candidate.pending_errors or candidate.pending_constraints
            or getattr(candidate, "summary_assumed_premises", [])):
        fail("summary", "summary introduced assumptions/effects")
    r14 = before.x86_registers.get_register(Register.R14)

    def absolute(offsets):
        value = Uint256(*(before.x86_memory.load_limb(r14 + BitVecVal(offset, 64), domain=MemoryDomain.STACK)
                          for offset in offsets)).to_bv256()
        return Uint256.from_bv256(_abs256(value))

    actual_took = builtin_taken_condition(absolute(p.dividend_offsets), absolute(p.divisor_offsets))
    for i, path in enumerate(raw):
        justified = []
        for k, assumption in enumerate(path.state.assumptions or []):
            justified.append(check(f"assumption_{i}_{k}", And(path.condition, Not(assumption))))
        witnesses = [(took, actual_took)]
        witnesses += [(candidate.x86_registers.get_register(reg), path.state.x86_registers.get_register(reg))
                      for reg in p.clobber_registers]
        witnesses += [(candidate.x86_registers.get_flag(flag), path.state.x86_registers.get_flag(flag))
                      for flag in DIV_FLAGS]
        try:
            goal = substitute(_equal_state(path.state, candidate), *witnesses)
        except ValueError as exc:
            fail(f"effect_{i}", str(exc))
        started = monotonic()
        pre = And(path.condition, *(path.state.assumptions or []))
        answer, children = refute_signed_effect(pre, goal, timeout_ms)
        if answer == "unknown":
            answer, children = refute_signed_effect(pre, goal, 4 * timeout_ms)
        children = (*justified, *children)
        records.append(Obligation(f"effect_{i}", And(path.condition, Not(goal)).sexpr(), answer, "unsat",
                                  monotonic()-started, children, tuple(o.name for o in children), "signed_full_state"))
        if answer != "unsat":
            fail(f"effect_{i}", f"full-state equality not proved (solver={answer})")
    tags = tuple(before.x86_registers.get_pointer_tag(r) for r in (Register.R14, Register.R15))
    lemma = DivLemma(semantic_key(summary, blocks, profile), len(raw), tuple(records), tags)
    if not lemma.complete:
        fail("certificate", "incomplete signed slice lemma")
    return lemma


_SUCCESS, _FAILURE = {}, {}


def clear_proof_cache():
    _SUCCESS.clear()
    _FAILURE.clear()


def prove_signed_slice_cached(summary, blocks, *, profile, timeout_ms=30_000):
    key = semantic_key(summary, blocks, profile)
    if key in _SUCCESS:
        return _SUCCESS[key], "cache_hits"
    if (key, timeout_ms) in _FAILURE:
        old = _FAILURE[key, timeout_ms]
        raise SignedProofError(old.entry_addr, old.label, old.reason, from_cache=True)
    try:
        lemma = prove_signed_slice(summary, blocks, profile=profile, timeout_ms=timeout_ms)
    except SignedProofError as exc:
        _FAILURE[key, timeout_ms] = SignedProofError(exc.entry_addr, exc.label, exc.reason)
        raise
    _SUCCESS[key] = lemma
    return lemma, "proven"
