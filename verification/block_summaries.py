"""Per-hit, raw-code-checked summaries for block proofs.

Replay is deliberately bounded and uses NO summaries. It establishes finite
execution, exact continuation and full frame/effect inclusion on the current
input domain. This first implementation is a correctness gate, not a claim of
constant-time proof for arbitrary-length symbolic copy loops. The two byte-copy
templates additionally support a checked one-cycle induction certificate.
"""
from contextlib import contextmanager
from copy import copy
import os
from dataclasses import dataclass, replace
from enum import Enum
from hashlib import sha256
from time import monotonic

from z3 import (And, Not, Or, BoolVal, Extract, ULE, UGT, is_expr, is_const, Z3_OP_UNINTERPRETED, substitute,
                is_bv_value, simplify, is_store, Store, FreshConst, Select, is_eq, is_array, Const, is_and, is_true)

from verification.block_equivalence import (Obligation, ProofBudgetExceeded, solve_query, digest,
                                             state_digest, abstract_nonlinear_mul, _conjuncts)
from verification.block_partition import split_at_cutpoints
from verification.loop_induction import run_x86_segment
from x86_64.disassembler import parse_operands
from x86_64.models import Register
from x86_64.summaries import build_x86_summary_runtime
from x86_64.summaries.base import SummaryPreconditionError, refuted_by_complement
from x86_64.summaries.div_proof import DivProofError


@dataclass(frozen=True)
class SummaryHitCertificate:
    identity: str
    obligations: tuple[Obligation, ...]
    raw_path_count: int
    finite: bool
    required: tuple = ()

    @property
    def complete(self):
        names = tuple(o.name for o in self.obligations)
        return (self.finite and self.raw_path_count > 0 and self.identity
                and names == self.required and len(set(names)) == len(names)
                and {"entry", "coverage"} <= set(names)
                and all(f"effect_{i}" in names for i in range(self.raw_path_count))
                and all(o.proved for o in self.obligations))


def hit_identity(summary, before, premise, code, *extra):
    """Per-process label of one summary hit: the summary, the exact hit state
    and premise (by live Z3 AST ids, not sexpr) and the program code.

    Certificates only require it to be non-empty; it is never compared across
    processes. state_digest/sexpr of a large hit state cost ~6 s per hit
    (CErc20 8186: 219 s of a 274 s x86 segment) for the same labelling.
    """
    from verification.block_equivalence import digest
    leaves = tuple(sorted((path, value.get_id() if is_expr(value) else repr(value))
                          for path, value in _leaves(before).items()))
    return digest((summary, leaves, premise.get_id(), code, *extra))


def _leaves(obj, prefix=""):
    if is_expr(obj) or obj is None or isinstance(obj, (str, int, bool, bytes, Enum)):
        return {prefix: obj}
    if isinstance(obj, dict):
        items = ((str(k), v) for k, v in obj.items())
    elif isinstance(obj, (list, tuple)):
        items = ((str(k), v) for k, v in enumerate(obj))
    elif isinstance(obj, (set, frozenset)):
        return {prefix: tuple(sorted(obj))}
    elif hasattr(obj, "__dict__"):
        items = vars(obj).items()
    else:
        items = ((k, getattr(obj, k)) for k in getattr(type(obj), "__slots__", ()))
    result = {}
    for key, value in items:
        # Assumptions are separately audited against the original domain.
        if prefix == "" and key in ("assumptions", "summary_assumed_premises"):
            continue
        result.update(_leaves(value, f"{prefix}.{key}"))
    return result


def _input_var_ids(state, premise):
    # Walk the expression DAG once. z3util.get_vars expands shared arithmetic
    # as a tree, which can take minutes on a single real-contract copy entry.
    work = [premise, *(v for v in _leaves(state).values() if is_expr(v))]
    seen, variables = set(), set()
    while work:
        term = work.pop()
        key = term.get_id()
        if key in seen:
            continue
        seen.add(key)
        if is_const(term) and term.decl().kind() == Z3_OP_UNINTERPRETED:
            variables.add(key)
        work.extend(term.children())
    return variables


def _equal_state(left, right):
    a, b = _leaves(left), _leaves(right)
    if set(a) != set(b):
        raise ValueError("summary changed the state representation/field set")
    conditions = []
    for key in a:
        av, bv = a[key], b[key]
        if is_expr(av) and is_expr(bv):
            conditions.append(av == bv)
        elif is_expr(av) or is_expr(bv) or av != bv:
            raise ValueError(f"summary frame mismatch: {key}")
    return And(*conditions)


def generalize_state(obj, prefix=""):
    """Copy of a state whose every expression field is a fresh constant.

    Names derive from the field path only, so two states with the same field
    structure and metadata (pointer tags, domains, flags) generalize to the
    SAME state: a lemma proved on it is keyed by that structure. Any concrete
    state of that structure is an instance (substitute each constant by the
    state's field value). Assumptions are dropped: the lemma has no premise.
    """
    if is_expr(obj):
        return Const("g!" + sha256(prefix.encode()).hexdigest()[:16], obj.sort())
    if obj is None or isinstance(obj, (str, int, bool, bytes, Enum, set, frozenset)):
        return obj
    if isinstance(obj, dict):
        return {k: generalize_state(v, f"{prefix}.{k}") for k, v in obj.items()}
    if isinstance(obj, list):
        return [generalize_state(v, f"{prefix}.{k}") for k, v in enumerate(obj)]
    if isinstance(obj, tuple):
        return tuple(generalize_state(v, f"{prefix}.{k}") for k, v in enumerate(obj))
    new = copy(obj)
    fields = vars(obj).items() if hasattr(obj, "__dict__") else (
        (k, getattr(obj, k)) for k in getattr(type(obj), "__slots__", ()))
    for key, value in list(fields):
        if prefix == "" and key in ("assumptions", "summary_assumed_premises"):
            setattr(new, key, [])
        else:
            setattr(new, key, generalize_state(value, f"{prefix}.{key}"))
    return new


def structure_key(summary, state, program):
    """Everything generalize_state keeps: field paths, sorts and metadata."""
    shape = tuple(sorted((path, value.sort().sexpr()) if is_expr(value) else (path, repr(value))
                         for path, value in _leaves(state).items()))
    return digest((repr(summary), program, shape))


_UNMOVABLE = ("call", "ret", "sys", "int", "iret", "loop", "jrcxz", "jecxz", "jcxz", "enter", "leave")


def movable_slice(blocks, owned, entry, continuation):
    """Position-independent fingerprint of an owned slice, or None.

    Raw execution of a slice moved by d differs only through what reads an
    instruction's address: x86_instruction_to_z3 reads ``insn.addr`` solely
    for rip-relative operands; the executor reads addresses for control flow
    (branch targets = addr + size + rel, fallthrough = next block), stop sets
    and CFG node identity, and for bridges/summaries/call-site maps (all
    ``ret``-based or disabled in a summary-free replay). Hence, if

      * no operand mentions rip, no instruction is call/ret/syscall/int/loop/
        enter/leave (return addresses, bridges), no memory operand is absolute
        (identical bytes would read the same address -- excluded anyway);
      * every branch has a static, relative-encoded target (rel8/rel32; x86-64
        has no absolute near branch) inside the slice or at the continuation;
      * every non-jmp falls through inside the slice or to the continuation,
        and at a block end the next block in ``blocks`` starts right there
        (the executor falls through to the next listed block);

    then execution from entry + d is execution from entry with every location
    shifted by d: identical path conditions and states, the continuation
    shifted by d. Two slices with the same fingerprint (relative offset,
    bytes, block start of every owned instruction, relative continuation)
    therefore have the same raw paths up to that shift. Checked per slice:
    the caller must evaluate it at the slice it instantiates.
    """
    import capstone

    exits = set(owned) | {continuation}
    insn_at, next_start, starts = {}, {}, set()
    for k, block in enumerate(blocks):
        starts.add(block.start_addr)
        for insn in block.instructions:
            insn_at[insn.addr] = insn
        if block.instructions:
            last = block.instructions[-1]
            next_start[last.addr] = blocks[k + 1].start_addr if k + 1 < len(blocks) else None
    code = []
    for addr in sorted(owned):
        insn = insn_at.get(addr)
        if insn is None or insn._cs_insn is None:
            return None
        mnemonic = insn.mnemonic.lower()
        if "rip" in insn.op_str or mnemonic.startswith(_UNMOVABLE):
            return None
        if any(op.type == capstone.x86.X86_OP_MEM and op.mem.base == 0 and op.mem.index == 0
               for op in insn._cs_insn.operands):
            return None
        after = addr + insn.size
        if mnemonic.startswith("j"):
            ops = insn._cs_insn.operands
            if (len(ops) != 1 or ops[0].type != capstone.x86.X86_OP_IMM
                    or parse_operands(insn).get("jump_target") not in exits):
                return None
        if mnemonic != "jmp" and (after not in exits or next_start.get(addr, after) != after):
            return None
        code.append((addr - entry, bytes(insn.bytes), addr in starts or addr == entry))
    return continuation - entry, tuple(code)


def _relocated(summary, entry):
    """The summary with its code addresses relative to ``entry`` (CALLDATALOAD only)."""
    from x86_64.summaries.calldataload import CallDataLoadSummary
    payload = summary.payload
    if not isinstance(payload, CallDataLoadSummary):
        return None
    rel = lambda a: a - entry
    payload = replace(payload, entry_addr=rel(payload.entry_addr), exit_addr=rel(payload.exit_addr),
                      zero_addr=rel(payload.zero_addr), partial_addr=rel(payload.partial_addr),
                      internal_block_addrs=tuple(map(rel, payload.internal_block_addrs)))
    return replace(summary, entry_addr=rel(summary.entry_addr), start_block_addr=rel(summary.start_block_addr),
                   continuation=replace(summary.continuation, block_addr=rel(summary.continuation.block_addr)),
                   covered_block_addrs=tuple(map(rel, summary.covered_block_addrs)), payload=payload)


def same_step_semantics(origin, moved, state):
    """Proof of the translation argument on this slice pair: each instruction
    pair (same bytes, different address) yields the same state transformer on
    a generic state threaded in address order (a raise must be the same raise).
    Returns the number of compared transformers, or None on a difference."""
    from x86_64.semantics import x86_instruction_to_z3
    compared = 0
    for a, b in zip(origin, moved):
        results = []
        for insn in (a, b):
            try:
                results.append(x86_instruction_to_z3(insn, state.copy()))
            except Exception as exc:  # noqa: BLE001 - compared below
                results.append(type(exc))
        ra, rb = results
        if isinstance(ra, type) or isinstance(rb, type):
            if ra is not rb:
                return None
            continue
        la, lb = _leaves(ra), _leaves(rb)
        if set(la) != set(lb) or len(ra.assumptions or []) != len(rb.assumptions or []):
            return None
        pairs = [*((la[k], lb[k]) for k in la), *zip(ra.assumptions or [], rb.assumptions or [])]
        if not all(x.eq(y) if is_expr(x) and is_expr(y) else (not is_expr(x) and not is_expr(y) and x == y)
                   for x, y in pairs):
            return None
        state, compared = ra, compared + 1
    return compared


def _nop(insn):
    return insn.mnemonic.lower().startswith("nop")


def shifted_slice(blocks, owned, entry, continuation, anchor):
    """Layout- and stack-depth-independent fingerprint of an owned slice, or None.

    Generalizes movable_slice. The codegen emits the same CALLDATALOAD slice at
    many stack depths: only the displacements of ``[r14 + d]`` differ, and with
    them the encoding lengths (disp0/disp8/disp32) and hence the alignment nops
    and every relative branch offset. The fingerprint therefore compares
    capstone operands, not bytes, of the non-nop owned instructions in address
    order: mnemonic, prefixes, registers, immediates, memory operands with each
    r14 displacement taken relative to ``anchor``, and control flow as indices
    into that order ("cont" = the continuation): the static jump target and the
    fall-through successor (reached through nops). movable_slice's conditions
    stay (no rip/absolute operand, no call/ret/..., static targets inside the
    slice, fall-through inside it and onto the next listed block); in addition
    r14 may occur only as a memory base (never written, never a register or
    index operand), jump targets and the entry are not nops. Returns
    (fingerprint, non-nop instructions, nop instructions). Equal fingerprints
    are only a candidate pairing; shifted_step_semantics proves it.
    """
    import capstone
    x86 = capstone.x86
    r14 = {x86.X86_REG_R14, x86.X86_REG_R14D, x86.X86_REG_R14W, x86.X86_REG_R14B}
    exits = set(owned) | {continuation}
    insn_at, next_start = {}, {}
    for k, block in enumerate(blocks):
        for insn in block.instructions:
            insn_at[insn.addr] = insn
        if block.instructions:
            next_start[block.instructions[-1].addr] = blocks[k + 1].start_addr if k + 1 < len(blocks) else None
    insns = [insn_at.get(a) for a in sorted(owned)]
    if any(i is None or i._cs_insn is None for i in insns) or entry not in insn_at or _nop(insn_at[entry]):
        return None
    order = [i for i in insns if not _nop(i)]
    index = {i.addr: n for n, i in enumerate(order)}
    index[continuation] = "cont"

    def successor(addr):
        while addr in owned and _nop(insn_at[addr]):
            addr += insn_at[addr].size
        return index.get(addr)

    code = []
    for insn in insns:
        mnemonic, cs, after = insn.mnemonic.lower(), insn._cs_insn, insn.addr + insn.size
        if "rip" in insn.op_str or mnemonic.startswith(_UNMOVABLE):
            return None
        if mnemonic != "jmp" and (after not in exits or next_start.get(insn.addr, after) != after):
            return None
        if r14 & set(cs.regs_access()[1]):
            return None
        ops = []
        for op in cs.operands:
            if op.type == x86.X86_OP_REG and op.reg not in r14:
                ops.append(("r", op.reg, op.size))
            elif op.type == x86.X86_OP_IMM and mnemonic.startswith("j"):
                target = parse_operands(insn).get("jump_target")
                if len(cs.operands) != 1 or target not in exits or index.get(target) is None:
                    return None
                ops.append(("t", index[target]))
            elif op.type == x86.X86_OP_IMM:
                ops.append(("i", op.imm, op.size))
            elif op.type == x86.X86_OP_MEM:
                m = op.mem
                if (m.base == 0 and m.index == 0) or m.index in r14 or m.base in r14 - {x86.X86_REG_R14}:
                    return None
                ops.append(("m", m.segment, m.base, m.index, m.scale,
                            m.disp - anchor if m.base == x86.X86_REG_R14 else m.disp, op.size))
            else:
                return None
        if mnemonic.startswith("j") and not any(o[0] == "t" for o in ops):
            return None  # indirect jump
        if not _nop(insn):
            code.append((mnemonic, bytes(cs.prefix), tuple(ops), None if mnemonic == "jmp" else successor(after)))
    if any(c[3] is None and c[0] != "jmp" for c in code):
        return None
    return tuple(code), order, [i for i in insns if _nop(i)]


def _shift_r14(state, delta):
    """``state`` with the stack base moved by delta; memory, tags and all else unchanged."""
    shifted = state.copy()
    tag = shifted.x86_registers.get_pointer_tag(Register.R14)
    shifted.x86_registers.set_register(Register.R14, shifted.x86_registers.get_register(Register.R14) + delta)
    shifted.x86_registers.set_pointer_tag(Register.R14, tag)
    return shifted


def _same_result(left, right, timeout_ms=5000):
    """Both states have the same field set/metadata and provably equal fields."""
    la, lb = _leaves(left), _leaves(right)
    pa, pb = list(left.assumptions or []), list(right.assumptions or [])
    if set(la) != set(lb) or len(pa) != len(pb):
        return False
    from z3 import Solver, unsat
    for x, y in (*((la[k], lb[k]) for k in la), *zip(pa, pb)):
        if not (is_expr(x) and is_expr(y)):
            if is_expr(x) or is_expr(y) or x != y:
                return False
            continue
        if x.eq(y) or simplify(x).eq(simplify(y)):
            continue
        solver = Solver()
        solver.set(timeout=timeout_ms)
        solver.add(x != y)
        if solver.check() != unsat:
            return False
    return True


def shifted_step_semantics(origin, moved, nops, delta, state):
    """Proof of the stack-shift argument on a slice pair (see _lemma).

    ``origin``/``moved`` are the paired non-nop instructions of slices A/B
    (shifted_slice order). With shift(s) = s with R14 := R14 + delta, each pair
    must satisfy A_i(shift(t)) = shift(B_i(t)) on a generic state t threaded
    through B in order (fields compared syntactically, else proved equal by
    Z3; a raise must be the same raise), and every nop must be the identity.
    Returns the number of compared transformers, or None on a difference."""
    from x86_64.semantics import x86_instruction_to_z3

    def run(insn, s):
        try:
            return x86_instruction_to_z3(insn, s)
        except Exception as exc:  # noqa: BLE001 - compared below
            return type(exc)

    for insn in nops:
        out = run(insn, state.copy())
        if isinstance(out, type) or not _same_result(out, state, timeout_ms=1):
            return None
    if len(origin) != len(moved):
        return None
    compared = 0
    for a, b in zip(origin, moved):
        ra, rb = run(a, _shift_r14(state, delta)), run(b, state.copy())
        if isinstance(ra, type) or isinstance(rb, type):
            if ra is not rb:
                return None
            continue
        if not _same_result(ra, _shift_r14(rb, delta)):
            return None
        state, compared = rb, compared + 1
    return compared


def _normalized(summary):
    """(address- and depth-free CALLDATALOAD summary, its anchor), or None.

    Code addresses are dropped (shifted_slice pairs the code); stack offsets
    are taken relative to the result slot, the anchor of shifted_slice."""
    from x86_64.summaries.calldataload import CallDataLoadSummary, StackLimbLocation
    p = summary.payload
    if not isinstance(p, CallDataLoadSummary):
        return None
    res = p.result_stack_offset
    locs = tuple(StackLimbLocation(l.offset - res) if isinstance(l, StackLimbLocation) else l
                 for l in p.offset_limb_locs)
    return (summary.kind, summary.clobber_registers, summary.clobber_flags, locs, p.clobber_registers,
            p.require_concrete_offset, p.wrap_free), res


def shifted_summary_semantics(origin, moved, delta, state):
    """Instance obligation for the summaries: sum_A(shift(s)) = shift(sum_B(s)) on
    a generic s (result slot, stack offset limbs, register limbs, clobbers)."""
    from x86_64.summaries.calldataload import apply_calldataload_summary
    try:
        ra = apply_calldataload_summary(replace(origin.payload, entry_addr=0), _shift_r14(state, delta),
                                        fresh_prefix="shift_check")
        rb = apply_calldataload_summary(replace(moved.payload, entry_addr=0), state.copy(),
                                        fresh_prefix="shift_check")
    except Exception:  # noqa: BLE001 - no morphism
        return False
    return _same_result(ra, _shift_r14(rb, delta))


@dataclass(frozen=True)
class SummaryLemma:
    """A per-hit certificate proved once on generalize_state (no premise)."""
    key: str
    certificate: object
    clobber_tags: tuple
    origin: int = None  # entry the lemma was proved at (movable/shifted keys only)
    origin_summary: object = None  # the summary proved (shifted keys only)
    joined: tuple = ()  # clobbers whose path-dependent tag was joined (dead-after-continuation facts)

    @property
    def complete(self):
        return bool(self.key) and self.certificate.complete


@dataclass(frozen=True)
class LemmaInstanceCertificate:
    identity: str
    lemma: SummaryLemma
    key: str

    @property
    def complete(self):
        return bool(self.identity) and self.key == self.lemma.key and self.lemma.complete


def _store_addresses(array, limit=64):
    found = {}
    while is_store(array) and len(found) < limit:
        found.setdefault(array.arg(1).get_id(), array.arg(1))
        array = array.arg(0)
    return list(found.values())


def _blank_stores(array):
    # Stored values become fresh constants: only adds models.
    if is_store(array):
        return Store(_blank_stores(array.arg(0)), array.arg(1), FreshConst(array.arg(2).sort(), "blank"))
    return array


def refute_goal(pre, goal, timeout_ms, deadline=None):
    """Refute pre ∧ ¬goal, splitting when the whole query is not decided.

    ¬(g1 ∧ … ∧ gn) is refuted conjunct by conjunct; an array equality A = B by
    extensionality at a fresh k, cased over the addresses either Store chain
    writes plus their complement (where Store values are abstracted to fresh
    constants if needed — only adds models). The cases are exhaustive, so all
    sub-queries UNSAT is exactly the original UNSAT. Returns (answer, lemmas).
    """
    def solve(query, cap=None):
        budget = timeout_ms if cap is None else min(timeout_ms, cap)
        budget = budget if deadline is None else min(budget, int((deadline - monotonic()) * 1000))
        if budget <= 0:
            raise ProofBudgetExceeded("summary proof deadline exhausted")
        started = monotonic()
        answer = solve_query(simplify(query, expand_select_store=True), budget)
        if answer == "unknown":
            relaxed, changed = abstract_nonlinear_mul(query)  # only adds models
            if changed and solve_query(relaxed, budget) == "unsat":
                query, answer = relaxed, "unsat"
        return answer, Obligation("split", query.sexpr(), answer, "unsat", monotonic() - started)

    # ponytail: 3s whole-goal probe; the split below is exact and usually faster than a long wait here.
    answer, _ = solve(And(pre, Not(goal)), cap=3000)
    if answer != "unknown":
        return answer, ()
    lemmas = []
    parts = [g for g in _conjuncts(goal) if not (is_eq(g) and g.arg(0).eq(g.arg(1)))]  # A = A holds
    arrays = [g for g in parts if is_eq(g) and is_array(g.arg(0))]
    scalars = [g for g in parts if not (is_eq(g) and is_array(g.arg(0)))]
    if scalars:
        # Non-array fields are easy together; split them only if that fails.
        answer, record = solve(And(pre, Not(And(*scalars))))
        if answer == "unsat":
            lemmas.append(record)
            parts = arrays
    for g in parts:
        if is_eq(g) and is_array(g.arg(0)):
            answer, record = solve(And(pre, Not(g)), cap=3000)
            if answer == "unsat":
                lemmas.append(record)
                continue
            a, b = g.arg(0), g.arg(1)
            k = FreshConst(a.domain(), "ext")
            addrs = _store_addresses(a) + _store_addresses(b)
            window = [k == addr for addr in {x.get_id(): x for x in addrs}.values()]
            cases = [(w, Select(a, k) != Select(b, k)) for w in window]
            outside = And(*(Not(w) for w in window))
            cases.append((outside, Select(a, k) != Select(b, k)))
            for n, (case, diff) in enumerate(cases):
                answer, record = solve(And(pre, case, diff))
                if answer == "unknown" and n == len(cases) - 1 and window:
                    answer, record = solve(And(pre, case, Select(_blank_stores(a), k) != Select(_blank_stores(b), k)))
                if answer != "unsat":
                    return answer, ()
                lemmas.append(record)
        else:
            answer, record = solve(And(pre, Not(g)))
            if answer != "unsat":
                return answer, ()
            lemmas.append(record)
    return "unsat", tuple(lemmas)


_LEMMA_SECONDS = 1200  # ponytail: fixed; first CALLDATALOAD lemma measured ~333s
_LEMMA_SPENT = [0.0]  # seconds this process spent in fresh shared-lemma proofs


def lemma_seconds():
    return _LEMMA_SPENT[0]


@contextmanager
def lemma_budget(runtime):
    """A shared lemma gets its own budget instead of the node's: under a short
    node budget it would otherwise time out on every node and never be cached.
    The node deadline is restored after; the time is counted (lemma_seconds)
    so a scheduler can give the node a budget that excludes it."""
    started, node_deadline = monotonic(), runtime.deadline
    runtime.deadline = started + _LEMMA_SECONDS
    try:
        yield
    finally:
        runtime.deadline = node_deadline
        _LEMMA_SPENT[0] += monotonic() - started


class VerifiedSummaryRuntime:
    def __init__(self, blocks, config, *, cutpoints=(), timeout_ms=3000, max_depth=400, deadline=None, runtime=None):
        # Share only discovered templates. Every node has fresh proof records,
        # and every hit still replays and checks the actual machine code.
        self.runtime = runtime if runtime is not None else build_x86_summary_runtime(blocks, summary_config=config)
        self.blocks = list(blocks)
        self.cutpoints = set(cutpoints)
        self.timeout_ms, self.max_depth = timeout_ms, max_depth
        self.deadline = deadline
        self.certificates = []
        self.last_records = []
        self._counter = 0
        self.proof_queries = 0
        self._generic_mode = False
        self._joined = set()
        self._statement = None  # lemma statement items while _generic_mode

    def __getattr__(self, name):
        return getattr(self.runtime, name)

    def _code(self):
        """Digest of the program code, computed once per runtime."""
        if "_code_digest" not in self.__dict__:
            from verification.block_equivalence import digest
            self.__dict__["_code_digest"] = digest(tuple(
                (i.addr, bytes(i.bytes), i.mnemonic, i.op_str) for b in self.blocks for i in b.instructions))
        return self.__dict__["_code_digest"]

    def _geometry(self, summary):
        """(entry, continuation, owned addresses); raises if ownership crosses a cutpoint."""
        by_addr = {b.start_addr: b for b in self.blocks}
        start_block = by_addr[summary.start_block_addr]
        cont_block = by_addr[summary.continuation.block_addr]
        entry = start_block.instructions[summary.start_instruction_index].addr
        continuation = (cont_block.instructions[summary.continuation.instruction_index].addr
            if summary.continuation.instruction_index < len(cont_block.instructions)
            else cont_block.end_addr)
        owned = {by_addr[b].instructions[i].addr
                 for b, i in self.runtime.manager._covered_instruction_keys(summary)}
        if entry not in owned or continuation in owned or owned & self.cutpoints:
            raise ValueError("summary ownership crosses a block cutpoint or omits its entry")
        return entry, continuation, owned

    def _movable_key(self, summary, before):
        """Position-independent lemma key (see movable_slice), or None.

        Besides the code fingerprint and the relocated summary it holds what
        the generic proof read from outside the slice: whether each clobber's
        pointer tag is dead after the continuation (the proof may join
        path-dependent tags to NONE only then)."""
        entry, continuation, owned = self._geometry(summary)
        fingerprint = movable_slice(self.blocks, owned, entry, continuation)
        relocated = _relocated(summary, entry) if fingerprint is not None else None
        if relocated is None:
            return None
        return (structure_key(relocated, before, ("movable", fingerprint, self._dead(summary, continuation))),
                entry, fingerprint)

    def _dead(self, summary, continuation):
        from x86_64.summaries.calldataload import pointer_tag_dead_at
        return tuple(pointer_tag_dead_at(self.blocks, continuation, reg, kill_at=self.cutpoints)
                     for reg in summary.clobber_registers)

    def _shifted_slice(self, summary):
        """(normalized summary, anchor, entry, shifted_slice result), or None."""
        normalized = _normalized(summary)
        if normalized is None:
            return None
        shape, anchor = normalized
        entry, continuation, owned = self._geometry(summary)
        sliced = shifted_slice(self.blocks, owned, entry, continuation, anchor)
        return None if sliced is None else (shape, anchor, entry, continuation, sliced)

    def _shifted_key(self, summary, before):
        """Stack-depth- and layout-independent lemma key (see shifted_slice), or None."""
        found = self._shifted_slice(summary)
        if found is None:
            return None
        shape, _, entry, continuation, (code, _, _) = found
        return structure_key(shape, before, ("shifted", code)), entry, continuation

    def _origin_hint(self, key, summary, before, entry):
        """(origin entry, its summary) to prove the shifted lemma `key` at.

        A persisted hint names the entry some process proved it at: proving
        at the same slice makes the statement identical, so it is reused
        (_discharge) instead of re-proved at another slice of the shape. The
        hint is only a choice of slice: an unusable one (no such summary here,
        another key, ownership crossing this node's cutpoints) is ignored,
        and the lemma proved at the origin still reaches this hit only via
        the per-hit shift instance check."""
        from verification import proof_cache
        hint = proof_cache.lookup_hint(key)
        if hint is not None and hint != entry:
            for other in self.runtime.summaries:
                try:
                    if (other.kind == summary.kind and self._geometry(other)[0] == hint
                            and (self._shifted_key(other, before) or (None,))[0] == key):
                        return hint, other
                except ValueError:
                    continue
        return entry, summary

    def _shifted_instance(self, lemma, summary, before):
        """Instance obligations of a shifted lemma at ``summary``: the code
        (shifted_step_semantics) and the summary (shifted_summary_semantics)
        of the pair agree up to R14 += delta. The number of compared
        transformers, or None."""
        try:
            a, b = self._shifted_slice(lemma.origin_summary), self._shifted_slice(summary)
        except ValueError:  # the origin's ownership crosses this node's cutpoints
            return None
        if a is None or b is None or a[0] != b[0] or a[4][0] != b[4][0]:
            return None
        delta = b[1] - a[1]
        generic = generalize_state(before)
        steps = shifted_step_semantics(a[4][1], b[4][1], a[4][2] + b[4][2], delta, generic)
        if steps is None or not shifted_summary_semantics(lemma.origin_summary, summary, delta, generic):
            return None
        return steps

    def _lemma(self, summary, before):
        """The premise-free gate proved once per structure (see generalize_state).

        A slice first gets the stack-shift key (shifted_slice): slices that
        differ only in their r14 displacements by one delta, and in layout
        (encoding lengths, nops, branch offsets), share one lemma. Soundness,
        for A the slice the lemma was proved on and B = A shifted by delta,
        shift(s) = s with R14 := R14 + delta (memory, tags, all else unchanged):

          raw_B(s) = shift^-1(raw_A(shift(s)))   paired CFGs (shifted_slice) and
                                                 A_i∘shift = shift∘B_i per
                                                 instruction, nops = identity
                                                 (shifted_step_semantics); R14
                                                 is never written, so shift^-1
                                                 just restores R14
                   = shift^-1(sum_A(shift(s)))   the lemma of A: shift(s) has
                                                 the same structure (field set,
                                                 sorts, tags) as s, R14 is a
                                                 free constant of the lemma
                   = sum_B(s)                    shifted_summary_semantics

        Memory through other bases (r13 side channels, the calldata pointer)
        is unaffected as those instructions are identical and do not read
        R14; stack routing is by base register (R14 -> STACK) and so is
        displacement-independent; the clobber tags of the lemma carry over as
        shift leaves tags alone. The only fact the lemma reads from outside
        the slice is pointer-tag liveness after the continuation, for the
        clobbers whose path-dependent tag it joined (lemma.joined): each hit,
        also at the origin (cutpoints differ per node), checks them dead at
        its own continuation. A failed lemma, liveness or instance check
        falls back to the movable key (movable_slice: identical bytes;
        same_step_semantics), then to the per-address key."""
        cache = self.runtime.__dict__.setdefault("_summary_lemmas", {})
        shifted = self._shifted_key(summary, before)
        if shifted is not None:
            key, entry, continuation = shifted
            if ("origin", key) not in cache:
                cache[("origin", key)] = self._origin_hint(key, summary, before, entry)
            origin, at = cache[("origin", key)]
            if key not in cache:
                self._prove_lemma(cache, key, at, before, origin=origin)
                if cache[key] is not None:
                    from verification import proof_cache
                    proof_cache.store_hint(key, origin)
            lemma = cache[key]
            if lemma is not None and all(dict(zip(summary.clobber_registers, self._dead(summary, continuation)))
                                         .get(reg, False) for reg in lemma.joined):
                if lemma.origin == entry:
                    return key, lemma
                pair = ("shift", key, entry)
                if pair not in cache:
                    cache[pair] = self._shifted_instance(lemma, summary, before)
                if cache[pair] is not None:
                    return key, lemma
            elif lemma is None and origin == entry:
                return key, None  # the same proof already failed here
        movable = self._movable_key(summary, before)
        if movable is not None:
            key, entry, fingerprint = movable
            lemma = cache.get(key)
            if lemma is None or lemma.origin == entry:
                return self._prove_lemma(cache, key, summary, before, origin=entry)
            pair = ("steps", key, entry)
            if pair not in cache:
                insn_at = {i.addr: i for b in self.blocks for i in b.instructions}
                cache[pair] = same_step_semantics(
                    [insn_at[lemma.origin + rel] for rel, _, _ in fingerprint[1]],
                    [insn_at[entry + rel] for rel, _, _ in fingerprint[1]], generalize_state(before))
            if cache[pair] is not None:
                return key, lemma
        if "_program" not in self.runtime.__dict__:
            self.runtime.__dict__["_program"] = digest(tuple(
                (i.addr, bytes(i.bytes), i.mnemonic, i.op_str) for b in self.blocks for i in b.instructions))
        key = structure_key(summary, before, self.runtime.__dict__["_program"])
        return self._prove_lemma(cache, key, summary, before)

    def _prove_lemma(self, cache, key, summary, before, origin=None):
        if key not in cache:
            generic = generalize_state(before)
            # Generic mode builds the statement without solving (check() and
            # the effects take their expected answers as placeholders);
            # _discharge then solves it or reuses an identical proved one.
            self._generic_mode, self._statement, self._joined = True, [], set()
            try:
                with lemma_budget(self):
                    proved = self.apply(summary, generic, path_condition=None)
                    certificate = self._discharge(self.certificates.pop())
                tags = tuple((reg, proved.x86_registers.get_pointer_tag(reg)) for reg in summary.clobber_registers)
                cache[key] = SummaryLemma(key, certificate, tags, origin, summary if origin is not None else None,
                                          tuple(self._joined))
            except Exception:  # noqa: BLE001 - no lemma (incl. over budget); per-hit gate decides
                cache[key] = None
            finally:
                self._generic_mode, self._statement = False, None
        return key, cache[key]

    def _apply_lemma(self, summary, before, premise):
        """Instantiate a proved lemma: the hit state is an instance of it."""
        key, lemma = self._lemma(summary, before)
        if lemma is None or not lemma.complete:
            return None
        self._counter += 1
        candidate = self.runtime.manager.apply(summary, before.copy(),
            fresh_prefix=f"lemma_summary_{id(self)}_{self._counter}",
            path_condition=premise, precondition_timeout_ms=self.timeout_ms)
        allowed = {a.get_id() for a in before.assumptions or []}
        if (any(a.get_id() not in allowed for a in candidate.assumptions or [])
                or candidate.pending_errors or candidate.pending_constraints
                or getattr(candidate, "summary_assumed_premises", [])):
            raise ValueError("summary introduced unproved assumptions/effects")
        for reg, tag in lemma.clobber_tags:
            candidate.x86_registers.set_pointer_tag(reg, tag)
        self.certificates.append(LemmaInstanceCertificate(digest((key, id(self), self._counter)), lemma, key))
        self.runtime.manager.record_hit(summary)
        return candidate

    def _apply_div(self, summary, before, premise, records, required, check):
        """Composition proof: no replay on the hit state (the dividend is
        typically a MUL product, where replay is intractable). The slice lemma
        (div_proof: raw slice incl. builtin bridge == summary on a generic state,
        cached per slice shape; failure raises DivProofError) is instantiated
        at the hit, whose only premise, the stack geometry, is proved here.

        memgas (memgas_proof, MemGasProofError is a DivProofError) is the same
        composition; its lemma's only premise is the excluded exit guard, which
        the executor's split put into the path condition."""
        lemma = self.runtime.manager.specs[summary.kind].lemma(summary)
        if summary.kind == "memgas":
            from x86_64.summaries.memgas import exit_guard
            name, violated = "memgas_exit_guard_excluded", exit_guard(summary.payload, before)
        else:
            from x86_64.summaries.div import stack_geometry
            name, violated = "div_stack_geometry", Not(stack_geometry(before))
        check(name, And(premise, violated))
        required.append(name)
        self._counter += 1
        candidate = self.runtime.manager.apply(summary, before.copy(),
            fresh_prefix=f"verified_{summary.kind}_{id(self)}_{self._counter}",
            path_condition=premise, precondition_timeout_ms=self.timeout_ms)
        allowed = {a.get_id() for a in before.assumptions or []}
        if (any(a.get_id() not in allowed for a in candidate.assumptions or [])
                or candidate.pending_errors or candidate.pending_constraints
                or getattr(candidate, "summary_assumed_premises", [])):
            raise ValueError(f"{summary.kind} summary introduced unproved assumptions/effects")
        obligations = (*records, *lemma.obligations)
        identity = hit_identity(summary, before, premise, self._code(), lemma.key)
        certificate = SummaryHitCertificate(identity, obligations, lemma.path_count, True,
                                            tuple(o.name for o in obligations))
        if not (certificate.complete and lemma.complete):
            raise ValueError(f"incomplete {summary.kind} summary certificate")
        self.certificates.append(certificate)
        self.runtime.manager.record_hit(summary)
        return candidate

    def _solve(self, name, formula, expected="unsat"):
        started = monotonic()
        timeout = self.timeout_ms
        if self.deadline is not None:
            timeout = min(timeout, int((self.deadline - started) * 1000))
            if timeout <= 0:
                raise ProofBudgetExceeded("summary proof deadline exhausted")
        self.proof_queries += 1
        # premise ∧ goal (the exit guard check of _apply_div, which the
        # executor's split already negated on this path): see
        # refuted_by_complement; a miss runs the unchanged query below.
        if (expected == "unsat" and is_and(formula) and formula.num_args() >= 2
                and refuted_by_complement(And(*formula.children()[:-1]), formula.arg(formula.num_args() - 1))):
            return Obligation(name, formula.sexpr(), "unsat", expected, monotonic() - started)
        query = simplify(formula, expand_select_store=True)
        answer = solve_query(query, timeout)
        if answer == "unknown" and expected == "unsat":
            relaxed, changed = abstract_nonlinear_mul(formula)
            budget = self.timeout_ms
            if self.deadline is not None:
                budget = min(budget, int((self.deadline - monotonic()) * 1000))
            if changed and budget > 0:
                if solve_query(relaxed, budget) == "unsat":
                    formula, answer = relaxed, "unsat"
        return Obligation(name, formula.sexpr(), answer, expected, monotonic() - started)

    def _discharge(self, certificate):
        """Solve the lemma statement collected by a generic-mode apply, or
        reuse it if exactly this statement (proof_cache.statement_key) was
        proved before in any process. Raises unless every item got its
        expected answer; only then is the statement recorded as proved."""
        from verification import proof_cache
        statement, placeholders = self._statement, getattr(certificate, "obligations", ())
        if [o.name for o in placeholders] != [item[0] for item in statement]:
            raise ValueError("lemma certificate does not match its statement")
        if not statement:
            return certificate
        key = proof_cache.statement_key("summary_lemma", [(n, e, q) for n, e, q, _ in statement])
        if proof_cache.lemma_proved(key):
            return certificate  # placeholders carry the expected answers this key was proved with
        solved = []
        for (name, expected, query, refutation), placeholder in zip(statement, placeholders):
            if refutation is None:
                record = self._solve(name, query, expected)
            else:  # query = pre ∧ ¬goal, split exactly by refute_goal
                started = monotonic()
                answer, split = refute_goal(*refutation, self.timeout_ms, self.deadline)
                self.proof_queries += 1 + len(split)
                record = replace(placeholder, answer=answer, elapsed_seconds=monotonic() - started, lemmas=split)
            if not record.proved:
                raise ValueError(f"{name}: {record.answer}")
            solved.append(record)
        proof_cache.record_lemma(key)
        return replace(certificate, obligations=tuple(solved))

    def apply(self, summary, state, path_condition=None, witness=None):
        # Kept for diagnostics: a rejected hit still shows which obligation failed.
        records = self.last_records = []
        def check(name, formula, expected="unsat"):
            if self._generic_mode:  # lemma statement: built here, solved by _discharge
                self._statement.append((name, expected, formula, None))
                records.append(Obligation(name, formula.sexpr(), expected, expected))
                return
            record = self._solve(name, formula, expected)
            records.append(record)
            if not record.proved:
                raise ValueError(f"{name}: {record.answer}")
        try:
            before = state.copy()
            for reg in Register:
                before.x86_registers.get_register(reg)
                before.x86_registers.set_pointer_tag(reg, before.x86_registers.get_pointer_tag(reg))
            for flag in ("CF", "ZF", "SF", "OF", "PF", "AF", "DF"):
                before.x86_registers.set_flag(flag, before.x86_registers.get_flag(flag))
            premise = And(*(before.assumptions or []),
                          path_condition if path_condition is not None else BoolVal(True))
            # ponytail: opt-in (~5 min per slice structure today); default stays per-hit.
            if (summary.kind == "calldataload" and summary.payload.wrap_free
                    and not self._generic_mode and os.environ.get("BLOCK_SUMMARY_LEMMAS") == "1"):
                instance = self._apply_lemma(summary, before, premise)
                if instance is not None:
                    return instance
            try:
                # A model of the path (the executor's last reachability witness)
                # that also satisfies the premise is itself the SAT certificate:
                # eval with model completion rewrites the premise under one total
                # assignment, and only a result that is literally true counts
                # (a quantifier it cannot reduce stays symbolic, so it is a miss).
                # Otherwise (or for a generic-mode statement) solve as before.
                if (witness is not None and not self._generic_mode
                        and is_true(witness.eval(premise, model_completion=True))):
                    self.proof_queries += 1
                    records.append(Obligation("entry", premise.sexpr(), "sat", "sat"))
                else:
                    check("entry", premise, "sat")
                required = ["entry"]
            except ValueError:
                from verification.mcopy_induction import dead_hit
                if dead_hit(self, summary, before, premise, records):
                    return before
                if records[-1].answer != "unknown":
                    raise
                # Undecided entry (a SAT premise the solver could not decide in budget: Aave 7200
                # x86 needs 36.5s, the budget is 30s): proceed, recorded as undecided. Rejecting
                # made the raw fallback unroll symbolic-length copy loops hit by hit until the
                # 6h node budget ran out. The entry check only shows the hit is not vacuous;
                # every obligation below is an UNSAT query over the premise and holds whether or
                # not it is satisfiable (an infeasible hit is vacuous), so nothing rests on it.
                records[-1] = replace(records[-1], expected="unknown")
                required = ["entry"]
            # Fixed codegen (sub size, offset) cannot wrap; the raw replay below
            # still proves the summary on the full domain.
            if summary.kind == "calldataload" and not summary.payload.wrap_free:
                from x86_64.summaries.calldataload import offset_expr_from_locations
                offset = offset_expr_from_locations(summary.payload, before)
                low = Extract(63, 0, offset)
                # The proposed EVM word summary differs from the old codegen
                # when offset+32 wraps. Avoid replaying an inapplicable summary
                # before falling back to raw execution; never assume this guard.
                safe = Or(Extract(255, 64, offset) != 0,
                          UGT(low, before.callengine_input_size_bytes),
                          ULE(low, (1 << 64) - 33))
                check("calldata_no_wrap", And(premise, Not(safe)))
                required.append("calldata_no_wrap")
            entry, continuation, owned = self._geometry(summary)
            if summary.kind in ("div", "memgas"):
                return self._apply_div(summary, before, premise, records, required, check)
            if any(i.mnemonic.lower() in ("ret", "call") for b in self.blocks for i in b.instructions if i.addr in owned):
                raise ValueError("summary may not hide a host/return boundary")
            replay_blocks = split_at_cutpoints(self.blocks, {entry, continuation})
            stops = {b.start_addr for b in replay_blocks if b.instructions[0].addr not in owned} | {continuation}
            if (summary.kind == "copy_loop" and summary.payload.template in
                    ("makedata-byte-copy", "returndata-byte-copy", "mcopy-low-word", "mcopy-high-word")
                    # A concrete MCOPY length is finite: bounded raw replay below.
                    and not (summary.payload.template.startswith("mcopy") and is_bv_value(simplify(
                        before.x86_registers.get_register(Register(summary.payload.binding["S"])))))):
                from verification.copy_induction import CopyInductionCertificate, prove_byte_copy
                if summary.payload.template.startswith("mcopy"):
                    from verification.mcopy_induction import (
                        McopyInductionCertificate as CopyInductionCertificate, prove_mcopy as prove_byte_copy)
                self._counter += 1
                candidate = self.runtime.manager.apply(summary, before.copy(),
                    fresh_prefix=f"verified_copy_{id(self)}_{self._counter}",
                    path_condition=premise, precondition_timeout_ms=self.timeout_ms)
                allowed = {a.get_id() for a in before.assumptions or []}
                if (any(a.get_id() not in allowed for a in candidate.assumptions or [])
                        or candidate.pending_errors or candidate.pending_constraints
                        or getattr(candidate, "summary_assumed_premises", [])):
                    raise ValueError("copy summary introduced unproved assumptions/effects")
                count, required = prove_byte_copy(self, summary, before, premise,
                    candidate, replay_blocks, entry, continuation, stops, check)
                identity = hit_identity(summary, before, premise, self._code())
                certificate = CopyInductionCertificate(identity, tuple(records), required, count)
                if not certificate.complete:
                    raise ValueError("incomplete copy induction certificate")
                self.certificates.append(certificate)
                self.runtime.manager.record_hit(summary)
                return candidate
            # The outer path condition stays out of the replay: reachability
            # pruning then sees only the slice's own guards (weaker facts prune
            # less, never wrongly), and z3 cannot stall ignoring its timeout on
            # a huge premise. Coverage and effects below still conjoin it.
            raw_initial = before.copy()
            raw, defects, _ = run_x86_segment(replay_blocks, raw_initial, entry, stops,
                                               max_depth=self.max_depth, use_reachability_check=True,
                                               deadline=self.deadline)
            if defects or not raw:
                raise ValueError("raw summary execution incomplete: " + "; ".join(defects))
            check("coverage", And(premise, Not(Or(*(p.condition for p in raw)))))
            required.append("coverage")
            self._counter += 1
            proposal = summary
            if summary.kind == "calldataload":
                # The legacy plugin uses a concrete-offset heuristic. This
                # gate instead checks the exact raw slice on the current domain;
                # symbolic/wrapping offsets receive no assumed restriction.
                proposal = replace(summary, payload=replace(summary.payload, require_concrete_offset=False))
            candidate = self.runtime.manager.apply(proposal, before.copy(),
                fresh_prefix=f"verified_summary_{id(self)}_{self._counter}",
                path_condition=premise, precondition_timeout_ms=self.timeout_ms)
            allowed = {a.get_id() for a in before.assumptions or []}
            if any(a.get_id() not in allowed for a in candidate.assumptions or []):
                raise ValueError("summary introduced an input assumption")
            if candidate.pending_errors or candidate.pending_constraints or getattr(candidate, "summary_assumed_premises", []):
                raise ValueError("summary left unproved effects or assumptions")
            # Fresh clobber symbols describe an overapproximation. For each raw
            # path, provide its actual machine values as witnesses. Symbols
            # already present at entry cannot be existentially re-bound.
            input_vars = _input_var_ids(before, premise)
            clobbers = []
            for reg in summary.clobber_registers:
                clobbers.append((candidate.x86_registers.get_register(reg), lambda s, r=reg: s.x86_registers.get_register(r)))
                tags = {p.state.x86_registers.get_pointer_tag(reg) for p in raw}
                if len(tags) != 1 and summary.kind == "calldataload":
                    # CALLDATALOAD's zero path leaves memBeginReg untagged. If
                    # no code can observe the tag from the continuation, the
                    # tag is irrelevant: join to NONE on both sides.
                    from x86_64.summaries.calldataload import pointer_tag_dead_at
                    from state.x86_state import PointerTag
                    if pointer_tag_dead_at(self.blocks, continuation, reg, kill_at=self.cutpoints):
                        for p in raw:
                            p.state.x86_registers.set_pointer_tag(reg, PointerTag.NONE)
                        tags = {PointerTag.NONE}
                        self._joined.add(reg)  # the lemma relied on this liveness fact
                if len(tags) != 1:
                    raise ValueError("path-dependent pointer provenance cannot be summarized")
                candidate.x86_registers.set_pointer_tag(reg, tags.pop())
            for flag in summary.clobber_flags:
                clobbers.append((candidate.x86_registers.get_flag(flag), lambda s, f=flag: s.x86_registers.get_flag(f)))
            witnesses = [(v, read) for v, read in clobbers
                         if is_const(v) and v.decl().kind() == Z3_OP_UNINTERPRETED and v.get_id() not in input_vars]
            if len({v.get_id() for v, _ in witnesses}) != len(witnesses):
                raise ValueError("summary aliases independent clobber witnesses")
            allowed_raw = allowed | {premise.get_id()}
            for i, path in enumerate(raw):
                for assumption in path.state.assumptions or []:
                    if assumption.get_id() not in allowed_raw:
                        required.append(f"assumption_{i}_{len(records)}")
                        check(required[-1], And(premise, Not(assumption)))
                if path.kind == "terminal" or path.location != continuation:
                    goal = BoolVal(False)
                else:
                    goal = substitute(_equal_state(path.state, candidate),
                                      *((v, read(path.state)) for v, read in witnesses))
                required.append(f"effect_{i}")
                started = monotonic()
                if self._generic_mode:  # see check()
                    self._statement.append((required[-1], "unsat", And(premise, path.condition, Not(goal)),
                                            (And(premise, path.condition), goal)))
                    answer, split = "unsat", ()
                else:
                    answer, split = refute_goal(And(premise, path.condition), goal, self.timeout_ms, self.deadline)
                    self.proof_queries += 1 + len(split)
                record = Obligation(required[-1], And(premise, path.condition, Not(goal)).sexpr(), answer,
                                    "unsat", monotonic() - started, split)
                records.append(record)
                if not record.proved:
                    raise ValueError(f"{required[-1]}: {answer}")
            identity = hit_identity(summary, before, premise, self._code())
            certificate = SummaryHitCertificate(identity, tuple(records), len(raw), True, tuple(required))
            if not certificate.complete:
                raise ValueError("incomplete summary certificate")
            self.certificates.append(certificate)
            self.runtime.manager.record_hit(summary)
            return candidate
        except (ProofBudgetExceeded, TimeoutError, DivProofError):
            raise
        except Exception as exc:
            raise SummaryPreconditionError(kind=summary.kind, label=f"per-hit proof: {exc}",
                premise=path_condition, result="inconclusive", location=summary.start_key) from exc
