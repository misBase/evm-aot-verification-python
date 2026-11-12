"""Induction for the two backwards byte-copy machine-code loops
(makedata-byte-copy: CALLDATACOPY/CODECOPY, returndata-byte-copy).

No offline ``proved`` flag is consumed. The CURRENT bytes are executed for one
full cycle from an invariant state; all state fields, path coverage and a
decreasing unsigned counter are checked. An arbitrary address proves the
memory equality extensionally.

The induction is a lemma proved once over a fully parametric state (every
state leaf a fresh parameter; the source register is tied to its callEngine
pointer field) and cached on the per-program template runtime, so it is shared
by every hit on every path of every node. Each hit then proves, on its own
path, only that it is an instance:

* ``copy_domain``: the premise implies the no-wrap domain of the hit state;
* ``copy_param_entry``: the hit state equals the lemma's generic state under
  the substitution parameter := hit value (expression fields by the solver,
  metadata such as pointer tags / flags / source provenance by the exact
  comparison in ``_equal_state``, which raises on any mismatch);
* ``copy_param_result``: the summary's closed form equals the lemma's result
  under the same substitution.

Soundness: the lemma is universal in its parameters (they are free constants
constrained only by the generic domain); the domain and both ends of the
instantiation are proved per hit, so the lemma's conclusion transfers to the
hit. The cache key only selects a candidate lemma. It holds everything the
lemma's proof depends on besides the parameters (the summary, the replayed
bytes and geometry, the field set with sorts, all metadata and in tier 2 the
numerals); a too-coarse key can only yield a lemma whose instance obligations
fail (fail-closed), never one that is applied without them.
"""
from dataclasses import dataclass, replace
import itertools

from z3 import (And, BitVecSort, BoolVal, FreshConst, Lambda, Not, Or, Select, ULE, If,
                ULT, is_bv_value, is_const, is_expr, Z3_OP_UNINTERPRETED, substitute, is_store,
                simplify)

from state.smt_state import PointerTag
from x86_64.models import Register
from x86_64.tier2_semantics import getdata_byte

_INSTANCE = ("entry", "copy_domain", "copy_param_entry")
_RESULT = ("copy_param_result",)
_FLAGS = ("CF", "ZF", "SF", "OF")
# (template, source pointer tag) -> (callEngine pointer field, source array field)
_SOURCES = {
    ("returndata-byte-copy", PointerTag.RETURNDATA_PTR): ("callengine_return_data_pointer", "return_data"),
    ("makedata-byte-copy", PointerTag.CALLDATA_PTR): ("callengine_input_pointer", "calldata"),
    ("makedata-byte-copy", PointerTag.CODE_PTR): ("callengine_code_pointer", "code"),
}
# Lemmas outlive their node runtime (and its id()): name their symbols globally.
_LEMMA_IDS = itertools.count()


def _read_byte(memory, address):
    # Z3 leaves Select(Store(Lambda(...), ...), address) opaque even with
    # expand_select_store. Expose read-over-write before beta-reducing Lambda.
    if is_store(memory):
        return If(address == memory.arg(1), memory.arg(2),
                  _read_byte(memory.arg(0), address))
    return simplify(Select(memory, address))


@dataclass(frozen=True)
class CopyInductionCertificate:
    identity: str
    obligations: tuple
    required: tuple
    raw_path_count: int
    finite: bool = True

    @property
    def complete(self):
        names = tuple(o.name for o in self.obligations)
        lemma = set(names[len(_INSTANCE):-len(_RESULT)])
        per_path = all({f"effect_{i}", f"effect_{i}_other"} <= lemma
                       and bool({f"copy_progress_{i}", f"copy_exit_{i}"} & lemma)
                       for i in range(self.raw_path_count))
        return (bool(self.identity) and self.finite and self.raw_path_count > 0
                and names == self.required and len(set(names)) == len(names)
                and names[:len(_INSTANCE)] == _INSTANCE and names[-len(_RESULT):] == _RESULT
                and {"copy_base", "coverage"} <= lemma
                and any(n.startswith("copy_exit_") for n in lemma)
                and per_path and all(o.proved for o in self.obligations))


@dataclass(frozen=True)
class _Lemma:
    generic: object
    generalized: object
    parameters: tuple  # (parameter constant, state field path)
    names: tuple
    count: int
    records: tuple = ()

    def with_records(self, records):
        if tuple(r.name for r in records) != self.names:
            raise ValueError("copy lemma records do not match its manifest")
        return replace(self, records=records)


def _roles(summary, state):
    binding = summary.payload.binding
    reg = lambda role: Register(binding[role])
    tag = state.x86_registers.get_pointer_tag(reg("INP"))
    source = _SOURCES.get((summary.payload.template, tag))
    if source is None:
        raise ValueError("unsupported copy source provenance")
    length = None if source[1] == "return_data" else reg("LEN")
    return reg("S"), reg("DST"), reg("OFF"), length, reg("INP"), (reg("T"), reg("B")), source


def _domain(state, size_r, dst_r, off_r):
    size, dst, off = (state.x86_registers.get_register(r) for r in (size_r, dst_r, off_r))
    return And(ULT(size, 1 << 63), ULE(dst, dst + size), ULE(off, off + size))


def _effect(actual, expected, scratch_regs, input_vars, address, equal_state):
    # Only fresh clobber values are existential. A proposed constant or
    # pre-existing input symbol cannot hide a mismatching register effect.
    witnesses = [(expected.x86_registers.get_register(r), actual.x86_registers.get_register(r))
                 for r in scratch_regs]
    witnesses += [(expected.x86_registers.get_flag(f), actual.x86_registers.get_flag(f)) for f in _FLAGS]
    witnesses = [(v, value) for v, value in witnesses if is_const(v)
                 and v.decl().kind() == Z3_OP_UNINTERPRETED and v.get_id() not in input_vars]
    if len({v.get_id() for v, _ in witnesses}) != len(witnesses):
        raise ValueError("copy candidate aliases independent clobbers")
    # Use one fresh unconstrained address, not an array-equality heuristic.
    pointwise = _read_byte(actual.x86_memory.evm_mem, address) == _read_byte(expected.x86_memory.evm_mem, address)
    framed = actual.copy()
    framed.x86_memory.evm_mem = expected.x86_memory.evm_mem
    return substitute(And(pointwise, equal_state(framed, expected)), *witnesses)


def prove_byte_copy(runtime, summary, before, premise, candidate, blocks,
                    entry, continuation, stops, check):
    from verification.block_summaries import _equal_state, _input_var_ids, _leaves as state_leaves
    from verification.block_equivalence import ProofBudgetExceeded, digest

    roles = _roles(summary, before)
    size_r, dst_r, off_r, _, inp_r, scratch_regs, _ = roles
    # The caller must establish the domain from its actual path, never assume it.
    check("copy_domain", And(premise, Not(_domain(before, size_r, dst_r, off_r))))
    # Scratch provenance must be NONE at entry (the invariant havocs them
    # untagged); a different tag takes the existing raw-execution fallback.
    if any(before.x86_registers.get_pointer_tag(r) != PointerTag.NONE for r in scratch_regs):
        raise ValueError("copy scratch register has nontrivial pointer provenance")

    records = runtime.last_records
    fields = state_leaves(before)
    skip = {f".x86_registers._registers.{inp_r.value}"}  # tied to its pointer field
    code = (digest(summary), entry, continuation, tuple(sorted(stops)),
            tuple((b.start_addr, tuple((i.addr, bytes(i.bytes)) for i in b.instructions)) for b in blocks))
    # Shared by every node's runtime (the discovered-template object).
    cache = runtime.runtime.__dict__.setdefault("_copy_lemmas", {})
    numerals = any(is_bv_value(v) for p, v in fields.items() if p not in skip and is_expr(v))
    # Tier 1 parameterizes numerals too (shared by every path/node); tier 2,
    # only if tier 1 did not prove, keeps them concrete.
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
                    proved = _prove_lemma(runtime, summary, before, fields, abstract, roles, blocks,
                                          entry, continuation, stops, check, _equal_state, _input_var_ids)
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

    generic = lemma.generic
    parameters = [(p, fields[path]) for p, path in lemma.parameters]
    check("copy_param_entry", And(premise, Not(substitute(_equal_state(generic, before), *parameters))))
    records.extend(lemma.records)
    input_vars = _input_var_ids(before, premise) | _input_var_ids(generic, BoolVal(True))
    read = generic.x86_registers.get_register
    address = read(Register.R15) + read(dst_r) + FreshConst(BitVecSort(64), "copy_probe")
    check("copy_param_result", And(premise, Not(substitute(_effect(
        lemma.generalized, candidate, scratch_regs, input_vars, address, _equal_state), *parameters))))
    return lemma.count, _INSTANCE + lemma.names + _RESULT


def _prove_lemma(runtime, summary, before, fields, abstract, roles, blocks, entry, continuation,
                 stops, check, equal_state, input_var_ids):
    from verification.block_summaries import run_x86_segment
    from verification.mcopy_induction import _set_path

    size_r, dst_r, off_r, len_r, inp_r, scratch_regs, (pointer_attr, source_attr) = roles
    names = []

    def checked(name, formula):
        names.append(name)
        check(name, formula)

    generic = before.copy()
    generic.assumptions = []
    parameters = []
    for path in abstract:
        value = FreshConst(fields[path].sort(), "copy_parameter")
        if not _set_path(generic, path, value):
            raise ValueError(f"cannot parameterize state field {path}")
        parameters.append((value, path))
    # The summary requires INP == pointer field; tying them keeps that
    # syntactic here, and copy_param_entry proves it for the hit.
    tag = generic.x86_registers.get_pointer_tag(inp_r)
    generic.x86_registers.set_register(inp_r, getattr(generic, pointer_attr))
    generic.x86_registers.set_pointer_tag(inp_r, tag)
    domain = _domain(generic, size_r, dst_r, off_r)
    generalized = runtime.runtime.manager.apply(summary, generic.copy(),
        fresh_prefix=f"verified_copy_parameters_{next(_LEMMA_IDS)}",
        path_condition=domain, precondition_timeout_ms=runtime.timeout_ms)
    if (generalized.assumptions or generalized.pending_errors or generalized.pending_constraints
            or getattr(generalized, "summary_assumed_premises", [])):
        raise ValueError("parameterized candidate introduced assumptions/effects")

    read = generic.x86_registers.get_register
    size, dst, off, base = read(size_r), read(dst_r), read(off_r), read(Register.R15)
    length = None if len_r is None else read(len_r)
    source, old = getattr(generic, source_attr), generic.x86_memory.evm_mem
    fresh = lambda name, bits=64: FreshConst(BitVecSort(bits), name)
    remaining, bound_address, probe = fresh("copy_remaining"), fresh("copy_address"), fresh("copy_probe")
    address = base + dst + probe
    input_vars = input_var_ids(generic, domain)
    effect = lambda actual, expected: _effect(actual, expected, scratch_regs, input_vars, address, equal_state)

    def invariant(counter):
        state = generic.copy()
        position = bound_address - base - dst
        byte = (Select(source, off + position) if length is None else
                getdata_byte(source, off, length, position))
        state.x86_memory.evm_mem = Lambda([bound_address], If(
            And(ULE(counter, position), ULT(position, size)), byte, Select(old, bound_address)))
        state.x86_registers.set_register(size_r, counter)
        for r in scratch_regs:
            state.x86_registers.set_register(r, fresh("copy_scratch"))
        for f in _FLAGS:
            state.x86_registers.set_flag(f, fresh("copy_flag", 1))
        return state

    checked("copy_base", And(domain, Not(effect(generic, invariant(size)))))
    head = invariant(remaining)
    inv_domain = And(domain, ULE(remaining, size))
    head.add_assumption(inv_domain)
    paths, defects, _ = run_x86_segment(blocks, head, entry, stops | {entry},
        max_depth=runtime.max_depth, deadline=runtime.deadline)
    if defects or not paths:
        raise ValueError("raw copy cycle incomplete: " + "; ".join(defects))
    checked("coverage", And(inv_domain, Not(Or(*(p.condition for p in paths)))))
    allowed = {inv_domain.get_id()}
    for index, path in enumerate(paths):
        pre = And(inv_domain, path.condition)
        for n, assumption in enumerate(path.state.assumptions or []):
            if assumption.get_id() not in allowed:
                checked(f"copy_assumption_{index}_{n}", And(inv_domain, Not(assumption)))
        if path.kind == "terminal" or path.location not in (entry, continuation):
            raise ValueError("copy cycle leaves its owned region")
        if path.location == entry:
            next_counter = path.state.x86_registers.get_register(size_r)
            checked(f"copy_progress_{index}", And(pre, Not(And(
                ULT(next_counter, remaining), ULE(next_counter, size)))))
            goal = effect(path.state, invariant(next_counter))
        else:
            checked(f"copy_exit_{index}", And(pre, remaining != 0))
            next_counter = remaining
            goal = effect(path.state, generalized)
        # Exhaustive address split keeps the frame query out of the write case.
        written = address == base + dst + next_counter
        checked(f"effect_{index}", And(pre, written, Not(goal)))
        checked(f"effect_{index}_other", And(pre, Not(written), Not(goal)))
    return _Lemma(generic, generalized, tuple(parameters), tuple(names), len(paths))
