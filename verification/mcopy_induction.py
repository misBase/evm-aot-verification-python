"""Induction for the two MCOPY machine-code clusters (compileEVMMCOPYFrom{Low,High}).

Same discipline as :mod:`verification.copy_induction`: no offline lemma or
``proved`` flag is consumed; the CURRENT bytes are executed from invariant
states. The only cutpoint is the qword loop header; everything else in the
cluster is replayed raw and must be finite on its own:

* ``mcopy-high-word``: preamble -> header (establishes the invariant);
* header -> header: one qword step (unsigned-decreasing ``S`` = rank);
* header -> continuation: the je exit and the glue/shr/byte-tail epilogue,
  whose loops are bounded because ``S < 8`` there (reachability pruned).

The induction is proved once per node over a fully parametric state (every
symbolic leaf of the hit state is a fresh parameter) and then instantiated at
each hit: ``param_entry`` shows the hit state is an instance, ``param_result``
shows the returned closed form is the same instance of the proved result.
Invariants read the entry snapshot ``M`` (memmove, overlap-exact); only the
closed form returned to the executor is compared at exits.
"""
from dataclasses import dataclass
import itertools

from z3 import (And, BitVecSort, BitVecVal, BoolVal, FreshConst, If, Lambda, Not, Or, Select,
                Sum, ULE, ULT, is_app_of, is_bv_value, is_const, is_eq, is_expr, is_select,
                is_store, simplify, substitute, Z3_OP_BADD, Z3_OP_ITE, Z3_OP_UNINTERPRETED)

from verification.copy_induction import _read_byte
from x86_64.models import Register
from x86_64.tier2_semantics import mcopy_no_wrap_premises

TEMPLATES = ("mcopy-low-word", "mcopy-high-word")
_FLAGS = ("CF", "ZF", "SF", "OF")
_INSTANCE = ("entry", "mcopy_domain", "mcopy_param_entry")
_RESULT = ("mcopy_param_result", "mcopy_param_result_memory")
# Lemmas outlive their node runtime (and its id()): name their symbols globally.
_LEMMA_IDS = itertools.count()


@dataclass(frozen=True)
class McopyInductionCertificate:
    identity: str
    obligations: tuple
    required: tuple
    raw_path_count: int
    finite: bool = True

    @property
    def complete(self):
        names = tuple(o.name for o in self.obligations)
        per_path = all(
            {f"progress_{i}", f"step_{i}_other"} <= set(names)
            or f"exit_{i}_other" in names or f"pre_{i}_other" in names
            for i in range(self.raw_path_count))
        return (bool(self.identity) and self.finite and self.raw_path_count > 0
                and names == self.required and len(set(names)) == len(names)
                and names[:len(_INSTANCE)] == _INSTANCE and names[-len(_RESULT):] == _RESULT
                and {"mcopy_base", "coverage"} <= set(names)
                and any(n.startswith("progress_") for n in names)
                and any(n.startswith("exit_") for n in names)
                and per_path and all(o.proved for o in self.obligations))


@dataclass(frozen=True)
class DeadHitCertificate:
    """A copy-loop hit reached on an UNSAT path: the only obligation is that proof."""
    identity: str
    obligations: tuple

    @property
    def complete(self):
        return (bool(self.identity) and len(self.obligations) == 1
                and self.obligations[0].name == "entry" and self.obligations[0].answer == "unsat")


def dead_hit(runtime, summary, before, premise, records):
    """The executor reaches hits on infeasible paths (it prunes syntactically).
    Raw fallback there replays an unbounded loop; the hit is vacuous instead.

    Every copy-loop template, not only MCOPY: a symbolic-length CALLDATACOPY
    byte loop on an UNSAT path (Aave 7200 x86 0x72fc8) was replayed hit by hit
    until the node budget ran out. The UNSAT entry is the whole proof: no state
    satisfies the premise, so any successor is vacuously correct."""
    if (summary.kind != "copy_loop"
            or [(r.name, r.answer) for r in records] != [("entry", "unsat")]):
        return False
    from verification.block_summaries import hit_identity
    identity = hit_identity(summary, before, premise, runtime._code(), "dead")
    runtime.certificates.append(DeadHitCertificate(identity, tuple(records)))
    runtime.runtime.manager.record_hit(summary)
    return True


def mcopy_domain(template, dst, src, size, base):
    """Exactly the summary's own premises, in R15-relative offsets."""
    d0, s0 = dst - base, src - base
    if template == "mcopy-low-word":
        shape = Or(ULE(d0, s0), ULE(size, BitVecVal(8, 64)))
    else:
        shape = And(ULT(s0, d0), ULT(BitVecVal(8, 64), size))
    return And(shape, *mcopy_no_wrap_premises(d0, s0, size))


def _canon(term):
    # Flatten and order bvadd operands: identical addresses become the same
    # AST, so SAT never has to prove adder commutativity.
    if is_app_of(term, Z3_OP_BADD):
        flat, work = [], list(term.children())
        while work:
            t = work.pop()
            if is_app_of(t, Z3_OP_BADD):
                work.extend(t.children())
            else:
                flat.append(_canon(t))
        constant = sum(t.as_long() for t in flat if is_bv_value(t)) % (1 << term.size())
        flat = sorted((t for t in flat if not is_bv_value(t)), key=lambda t: t.get_id())
        return Sum(*flat, BitVecVal(constant, term.size())) if flat else BitVecVal(constant, term.size())
    return term


def _leaves(term, guard, arrays):
    # Byte = ITE tree over reads of the entry snapshot -> [(guard, index)].
    if is_select(term) and any(term.arg(0).eq(a) for a in arrays):
        return [(guard, _canon(term.arg(1)))]
    if is_app_of(term, Z3_OP_ITE):
        a = _leaves(term.arg(1), And(guard, term.arg(0)), arrays)
        b = _leaves(term.arg(2), And(guard, Not(term.arg(0))), arrays)
        if a is not None and b is not None:
            return a + b
    return None


def same_source(goal, array):
    """Sufficient, array- and adder-free form of ``byte_a == byte_b``: some pair
    of guards under which both read ``array`` at the same canonical index. Any
    other shape (e.g. a constant stored by tampered code) keeps the exact
    equality, decided by the solver."""
    goal = simplify(goal)
    if is_eq(goal):
        arrays = (array, simplify(array))
        a = _leaves(goal.arg(0), BoolVal(True), arrays)
        b = _leaves(goal.arg(1), BoolVal(True), arrays)
        if a is not None and b is not None:
            return Or(*(And(ga, gb) for ga, ia in a for gb, ib in b if ia.eq(ib)), BoolVal(False))
    return goal


def _set_path(obj, path, value):
    *parents, last = path.split(".")[1:]
    for part in parents:
        obj = obj[next(k for k in obj if str(k) == part)] if isinstance(obj, dict) else (
            obj[int(part)] if isinstance(obj, list) else getattr(obj, part))
    if isinstance(obj, dict):
        obj[next(k for k in obj if str(k) == last)] = value
    elif isinstance(obj, list):
        obj[int(last)] = value
    elif hasattr(obj, "__dict__") or hasattr(type(obj), "__slots__"):
        setattr(obj, last, value)
    else:
        return False
    return True


def _roles(summary, entry):
    payload = summary.payload
    if payload.template not in TEMPLATES:
        raise ValueError(f"unsupported mcopy template {payload.template}")
    binding = payload.binding
    header = binding.get("@HEADER")
    if not isinstance(header, int) or (payload.template == "mcopy-low-word") != (header == entry):
        raise ValueError("mcopy word-loop header does not match the summary entry")
    tail = payload.tail_binding or {}
    if any(tail.get(r) != binding.get(r) for r in ("DST", "S", "T")):
        raise ValueError("mcopy tail loop uses different registers")
    if payload.template == "mcopy-high-word" and (payload.shr_binding or {}).get("C") != binding.get("SRC"):
        raise ValueError("mcopy shr loop counter is not the SRC register")
    roles = tuple(Register(binding[r]) for r in ("DST", "SRC", "S", "T"))
    if len(set(roles) | {Register.R15}) != 5:
        raise ValueError("mcopy register roles alias")
    return header, roles


def prove_mcopy(runtime, summary, before, premise, candidate, blocks,
                entry, continuation, stops, check):
    from verification.block_summaries import _equal_state, _input_var_ids, _leaves as state_leaves

    template = summary.payload.template
    if getattr(before, "abstract_mcopy_memory", False):
        raise ValueError("relational mcopy memory cannot be checked extensionally")
    header, (dst_r, src_r, size_r, tmp_r) = _roles(summary, entry)
    read = lambda state, r: state.x86_registers.get_register(r)
    domain = lambda s: mcopy_domain(template, read(s, dst_r), read(s, src_r), read(s, size_r),
                                    read(s, Register.R15))
    records = runtime.last_records
    # The caller must establish the dispatch shape from its actual path.
    check("mcopy_domain", And(premise, Not(domain(before))))

    # The lemma is universal over its parameters and every hit below proves
    # that it is an instance (param_entry: all expression fields by the solver,
    # all metadata fields by _equal_state's exact comparison; param_result).
    # The key therefore only indexes the cache: a too-coarse key can make a
    # lemma fail to prove (fail-closed), never apply one that does not fit.
    # It holds what the lemma's proof depends on: the summary, the replayed
    # code, the field set with sorts and the metadata. DST/SRC are rebuilt as
    # R15 + offset, so their values never enter it. Tier 1 parameterizes
    # numerals too (shared by every path/node); tier 2, only if tier 1 did not
    # prove, keeps numerals concrete (the old per-state key).
    fields = state_leaves(before)
    skip = {f".x86_registers._registers.{r.value}" for r in (dst_r, src_r)}
    from verification.block_equivalence import ProofBudgetExceeded, digest
    code = (digest(summary), tuple((b.start_addr, tuple((i.addr, bytes(i.bytes)) for i in b.instructions))
                                   for b in blocks))
    # Shared by every node's runtime (the discovered-template object).
    cache = runtime.runtime.__dict__.setdefault("_mcopy_lemmas", {})
    numerals = any(is_bv_value(v) for p, v in fields.items() if p not in skip and is_expr(v))
    lemma = None
    for keep_numerals in ((False, True) if numerals else (True,)):
        key, abstract = [], []
        for path, value in sorted(fields.items(), key=lambda kv: kv[0]):  # dict order is path history
            if path in skip:
                continue
            if is_expr(value) and not (keep_numerals and is_bv_value(value)):
                abstract.append(path)
                key.append((path, value.sort().sexpr()))
            else:
                key.append((path, value.sexpr() if is_expr(value) else repr(value)))
        cache_key = (code, tuple(key), tuple(abstract))
        if cache_key not in cache:
            mark = len(records)
            try:
                from verification.block_summaries import lemma_budget
                with lemma_budget(runtime):  # shared lemma: its own budget, not the node's
                    proved = _prove_lemma(runtime, summary, before, fields, abstract, blocks, entry, header,
                                          continuation, stops, check, (dst_r, src_r, size_r, tmp_r), domain,
                                          _equal_state, _input_var_ids)
                cache[cache_key] = proved.with_records(tuple(records[mark:]))
            except (ProofBudgetExceeded, TimeoutError):
                raise
            except Exception:  # noqa: BLE001 - no lemma for this key
                if keep_numerals:
                    raise  # not cached (old per-hit behaviour); records kept for diagnostics
                # ponytail: a tier-1 failure is cached for the program even if only `unknown`;
                # tier 2 still proves such states per numeral key.
                cache[cache_key] = None
            del records[mark:]
        lemma = cache[cache_key]
        if lemma is not None:
            break
    generic, generalized = lemma.generic, lemma.generalized
    r15 = read(before, Register.R15)
    parameters = [(p, fields[path]) for p, path in lemma.parameters]
    parameters += [(lemma.offsets[0], read(before, dst_r) - r15), (lemma.offsets[1], read(before, src_r) - r15)]
    check("mcopy_param_entry", And(premise, Not(substitute(_equal_state(generic, before), *parameters))))
    records.extend(lemma.records)

    input_vars = _input_var_ids(before, premise) | _input_var_ids(generic, BoolVal(True))
    memory_goal, frame_goal = (substitute(g, *parameters) for g in _effect(
        generalized, candidate, (dst_r, src_r, tmp_r), input_vars,
        generic.x86_registers.get_register(dst_r) + lemma.probe, _equal_state))
    check("mcopy_param_result", And(premise, Not(frame_goal)))
    # The memory half is decided by index matching over the ORIGINAL memory
    # term; its Store chain is never expanded.
    check("mcopy_param_result_memory", And(premise, Not(same_source(
        memory_goal, before.x86_memory.evm_mem))))
    for r, tag in lemma.exit_tags.items():
        candidate.x86_registers.set_pointer_tag(r, tag)
    return lemma.count, _INSTANCE + lemma.names + _RESULT


@dataclass(frozen=True)
class _Lemma:
    generic: object
    generalized: object
    parameters: tuple
    offsets: tuple
    probe: object
    names: tuple
    count: int
    exit_tags: dict
    records: tuple = ()

    def with_records(self, records):
        if tuple(r.name for r in records) != self.names:
            raise ValueError("mcopy lemma records do not match its manifest")
        from dataclasses import replace
        return replace(self, records=records)


def _effect(actual, expected, witnessed, input_vars, address, equal_state, tags=None):
    """(memory byte equality at `address`, frame equality); fresh clobbers of
    `expected` are existential and instantiated with the machine's values."""
    free = lambda v: (is_const(v) and v.decl().kind() == Z3_OP_UNINTERPRETED
                      and v.get_id() not in input_vars)
    regs = [r for r in witnessed if free(expected.x86_registers.get_register(r))]
    witnesses = [(expected.x86_registers.get_register(r), actual.x86_registers.get_register(r))
                 for r in regs]
    witnesses += [(expected.x86_registers.get_flag(f), actual.x86_registers.get_flag(f))
                  for f in _FLAGS if free(expected.x86_registers.get_flag(f))]
    if len({v.get_id() for v, _ in witnesses}) != len(witnesses):
        raise ValueError("mcopy candidate aliases independent clobbers")
    pointwise = (_read_byte(actual.x86_memory.evm_mem, address)
                 == _read_byte(expected.x86_memory.evm_mem, address))
    framed = actual.copy()
    framed.x86_memory.evm_mem = expected.x86_memory.evm_mem
    if tags is not None:
        # Candidate clobbers take the machine's provenance, which must be
        # path-independent (same rule as the raw summary gate).
        for r in regs:
            tags.setdefault(r, set()).add(actual.x86_registers.get_pointer_tag(r))
            framed.x86_registers.set_pointer_tag(r, expected.x86_registers.get_pointer_tag(r))
    return (substitute(pointwise, *witnesses),
            substitute(equal_state(framed, expected), *witnesses))


def _prove_lemma(runtime, summary, before, fields, abstract, blocks, entry, header, continuation, stops,
                 check, roles, domain, equal_state, input_var_ids):
    from verification.block_summaries import run_x86_segment

    dst_r, src_r, size_r, tmp_r = roles
    read = lambda state, r: state.x86_registers.get_register(r)
    fresh = lambda name, bits=64: FreshConst(BitVecSort(bits), name)
    generic = before.copy()
    generic.assumptions = []
    parameters = []
    for path in abstract:
        value = FreshConst(fields[path].sort(), "mcopy_parameter")
        if not _set_path(generic, path, value):
            raise ValueError(f"cannot parameterize state field {path}")
        parameters.append((value, path))
    # Pointers are R15 + offset so the base cancels syntactically.
    base = read(generic, Register.R15)
    offsets = (fresh("mcopy_dst_offset"), fresh("mcopy_src_offset"))
    for r, off in zip((dst_r, src_r), offsets):
        tag = generic.x86_registers.get_pointer_tag(r)
        generic.x86_registers.set_register(r, base + off)
        generic.x86_registers.set_pointer_tag(r, tag)
    generic_domain = domain(generic)
    D, S0, N = read(generic, dst_r), read(generic, src_r), read(generic, size_r)
    M = generic.x86_memory.evm_mem
    input_vars = input_var_ids(generic, generic_domain)
    probe, bound = fresh("mcopy_probe"), fresh("mcopy_address")
    address = D + probe  # D-relative probe still ranges over every address
    exit_tags, names = {}, []

    def checked(name, formula):
        names.append(name)
        check(name, formula)

    effect = lambda actual, expected, tags=None: _effect(
        actual, expected, (dst_r, src_r, tmp_r), input_vars, address, equal_state, tags)

    generalized = runtime.runtime.manager.apply(summary, generic.copy(),
        fresh_prefix=f"verified_mcopy_parameters_{next(_LEMMA_IDS)}",
        path_condition=generic_domain, precondition_timeout_ms=runtime.timeout_ms)
    if (generalized.assumptions or generalized.pending_errors or generalized.pending_constraints
            or getattr(generalized, "summary_assumed_premises", [])):
        raise ValueError("parameterized candidate introduced assumptions/effects")

    def copied(lo, hi):
        # Offsets [lo, hi) of the destination hold the ORIGINAL source bytes.
        return Lambda([bound], If(ULT(bound - D - lo, hi - lo),
                                  Select(M, S0 + (bound - D)), Select(M, bound)))

    # Phase k: bytes done (FromLow, forward) or S itself (FromHigh, backward).
    # Stating FromLow over "done" keeps the SAT queries adder-light.
    low = summary.payload.template == "mcopy-low-word"
    start = BitVecVal(0, 64) if low else N
    phase = lambda state: N - read(state, size_r) if low else read(state, size_r)

    def invariant(k):
        state = generic.copy()
        if low:
            state.x86_memory.evm_mem = copied(BitVecVal(0, 64), k)
            values = (D + k, S0 + k, N - k)
        else:
            state.x86_memory.evm_mem = copied(k, N)
            values = (D + k - 8, S0 + k - 8, k)
        for r, value in zip((dst_r, src_r, size_r), values):
            state.x86_registers.set_register(r, value)
        state.x86_registers.set_register(tmp_r, fresh("mcopy_scratch"))
        # set_register clears provenance; the invariant keeps the entry tags.
        for r in roles:
            state.x86_registers.set_pointer_tag(r, generic.x86_registers.get_pointer_tag(r))
        for f in _FLAGS:
            state.x86_registers.set_flag(f, fresh("mcopy_flag", 1))
        return state

    def inv_domain(k):
        if low:
            # Alignment excludes unreachable mid-word states in the small
            # reversed-overlap case, where the source is already clobbered.
            return And(generic_domain, ULE(k, N), k & 7 == 0)
        return And(generic_domain, ULE(BitVecVal(8, 64), k), ULE(k, N))

    def replay(head, location, domain_expr):
        head.add_assumption(domain_expr)
        paths, defects, _ = run_x86_segment(blocks, head, location, stops | {header},
            max_depth=runtime.max_depth, use_reachability_check=True, deadline=runtime.deadline,
            # The byte tails are bounded only via pruning; 50 ms flakes under load.
            reachability_timeout_ms=2000)
        if defects or not paths:
            raise ValueError("raw mcopy segment incomplete: " + "; ".join(defects))
        allowed = {domain_expr.get_id()}
        for path in paths:
            if path.kind == "terminal" or path.location not in (header, continuation):
                raise ValueError("mcopy segment leaves its owned region")
            if any(a.get_id() not in allowed for a in path.state.assumptions or []):
                raise ValueError("mcopy segment introduced an assumption")
        return paths

    def split(name, pre, actual, goals):
        memory_goal, frame_goal = goals
        checked(f"{name}_frame", And(pre, Not(frame_goal)))
        # Exhaustive split on the probe: each store address of this path,
        # then none of them. Keeps every query small.
        stores, memory = {}, actual.x86_memory.evm_mem
        while is_store(memory):
            stores.setdefault(memory.arg(1).get_id(), memory.arg(1))
            memory = memory.arg(0)
        for j, store in enumerate(stores.values()):
            checked(f"{name}_w{j}", And(pre, Not(same_source(
                substitute(memory_goal, (probe, store - D)), M))))
        checked(f"{name}_other", And(pre, *(probe != simplify(a - D) for a in stores.values()),
                                     Not(same_source(memory_goal, M))))

    count = 0
    if low:
        checked("mcopy_base", And(generic_domain, Not(And(*effect(generic, invariant(start))))))
    else:
        # The preamble is straight-line/acyclic; it must land on the invariant.
        paths = replay(generic.copy(), entry, generic_domain)
        checked("mcopy_base", And(generic_domain, Not(Or(*(p.condition for p in paths)))))
        for path in paths:
            if path.location != header:
                raise ValueError("mcopy preamble bypasses the word loop")
            split(f"pre_{count}", And(generic_domain, path.condition), path.state,
                  effect(path.state, invariant(start)))
            count += 1

    k = fresh("mcopy_phase")
    domain_k = inv_domain(k)
    head = invariant(k)
    size_head = read(head, size_r)
    paths = replay(head, header, domain_k)
    checked("coverage", And(domain_k, Not(Or(*(p.condition for p in paths)))))
    for path in paths:
        pre = And(domain_k, path.condition)
        if path.location == header:
            checked(f"progress_{count}", And(pre, Not(And(
                ULT(read(path.state, size_r), size_head), inv_domain(phase(path.state))))))
            split(f"step_{count}", pre, path.state, effect(path.state, invariant(phase(path.state))))
        else:
            split(f"exit_{count}", pre, path.state, effect(path.state, generalized, exit_tags))
        count += 1
    tags = {}
    for r, seen in exit_tags.items():
        if len(seen) != 1:
            raise ValueError("path-dependent pointer provenance cannot be summarized")
        tags[r] = next(iter(seen))
    return _Lemma(generic, generalized, tuple(parameters), offsets, probe, tuple(names), count, tags)

