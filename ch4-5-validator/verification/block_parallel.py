"""Discover-first, parallel schedule for block lock-step certificates.

The worklist in block_program interleaves discovery with proof: a successor is
known only after its predecessor's full proof, nodes run one at a time and
H0/H2 waits for the whole queue (R28: 1/3 of the instances in 11h, closure
never reached). Here the three phases are separate:

1. Discovery. Instance parameters (pc, depth, MSize, fmp, stack constants) are
   EVM-side values, so the unchanged `_discover` runs on EVM segment exits
   only (no x86, no proof): minutes for the whole graph (CErc20 4708
   instances in 594s). The set is then frozen. The joint used is the EVM path
   condition alone, weaker than the worklist's EVM ∧ x86 joint, so it can only
   propose more instances, never fewer; proposals prove nothing either way.
2. Proof. Every instance is proved in a worker process (its own prover, built
   from the same recipe) together with its H2 edges against the frozen set.
   Workers return plain data: the node's BlockTheorem, the exit pairs its
   outcomes produced, and one EdgeCertificate per pair.
3. Certificate. H0 (raw entry into the frozen set) is checked here; the
   certificate needs every instance proved and every entry/H2 edge closed.

Trust boundary versus ProgramCertificate: that consumer re-derives the edge set
and outcome digests from in-process Z3 outcomes; a worker's outcomes cannot
cross processes, so the local exit manifests and theorems are taken from the
workers, which run this same code on the same program (checked: every worker
reports the parent's portable identity). H2 edges must match that manifest;
the consumer does not replay the workers' SMT computations.

Constant-insensitive proof instances (option `constant_insensitive`,
docs/块级实例常量去敏化方案.md): the frozen instances stay the relation nodes
(contexts c, H0/H2 targets); the local theorem is proved once per proof
instance k = π(c), which drops the stack constants the block never consumes.
Sound for any π with weakens(k, c): R_c = R_k ∧ K_c, so T_k covers c's
entries, and havoc(c) ≡ havoc(k) ∧ E_c (E_c: the dropped constants as
equalities on k's entry symbols; tests/unit/test_block_constant_projection.py)
makes H2 of c on k's exits under E_c exactly c's H2. Each edge records E_c's
constants as `assumed`.
"""
from __future__ import annotations

import gc
import os
import pickle
import tempfile
import zlib  # obligation texts compress ~15x: R30 wrote 15GB for 1188 nodes uncompressed
import time
from collections import defaultdict
from dataclasses import dataclass, replace
from hashlib import sha256
from pathlib import Path
from time import monotonic

from z3 import Z3_OP_CONCAT, Z3_OP_ITE, Z3_OP_UNINTERPRETED, And, Not, Or, is_app, is_eq, is_false, is_quantifier, is_true, simplify

from common.node_monitor import (MEMORY_EXIT_CODE, NodeMemoryExceeded, NodeMonitor, read_status, release_memory,
                                 rss_bytes)
from verification.block_equivalence import (BlockTheorem, InstructionBlockTheorem, ProofBudgetExceeded, digest,
                                            paths_digest, state_digest)
from verification.block_program import (BlockProgramResult, BlockProgramVerifier, EdgeCertificate,
                                        EntryCertificate)
from verification.block_relation import stack_constant_condition
from verification.block_specialization import PROJECTION_VERSION, dropped, project, sensitive_slots, weakens
from verification import proof_cache
from verification.loop_induction import run_evm_segment


def build_inputs(stem, options):
    """(evm program, x86 program, initial state, verifier) exactly as
    tools/verify_block_lockstep builds them; also run in every worker."""
    from evm_ir.json_parser import load_ir_from_json
    from evm_ir.program import EVMProgram
    from x86_64.program import X86Program
    from x86_64.summaries import X86SummaryConfig
    from state.smt_state import SMTState
    from verification.program_verifier import GasCheck
    evm = EVMProgram(load_ir_from_json(str(stem) + ".json"))
    x86 = X86Program.from_hex(Path(str(stem) + ".hex").read_text().strip(), base_addr=0x1000)
    mode = GasCheck(options["gas_check"])
    state = SMTState.create_initial_state(num_inputs=options["num_inputs"], symbolic_gas=mode == GasCheck.FULL,
                                          gas_budget=None if mode == GasCheck.FULL else options["gas_budget"])
    state.assume_calldata_offset_no_overflow = False
    state.host_gas_uf_enabled = mode != GasCheck.OFF
    config = X86SummaryConfig.enabled(calldataload="fallback", copy_loop="fallback", mul="fallback",
                                      div="fallback", memgas="fallback", shift="fallback",
                                      sdiv="fallback", smod="fallback") if options["summaries"] else None
    verifier = BlockProgramVerifier(gas_check=mode, timeout_ms=options["timeout_ms"], max_depth=options["max_depth"],
                                    max_instances=options["max_instances"], wall_timeout_seconds=options["wall_seconds"],
                                    summary_config=config, node_timeout_seconds=options["node_seconds"],
                                    max_parameter_values=options["max_parameter_values"],
                                    first_pass_node_seconds=options["first_pass_node_seconds"],
                                    pushed_code_return_tags=options.get("pushed_code_return_tags", False),
                                    terminal_constant_projection=options.get("terminal_constant_projection", False),
                                    context_constant_projection=options.get("context_constant_projection", False))
    return evm, x86, state, verifier


def order_key(s):
    return (s.pc, s.stack_depth, -1 if s.memory_size is None else s.memory_size,
            -1 if s.free_memory_pointer is None else s.free_memory_pointer, s.stack_constants)


def discover(verifier, setup, budget):
    """Frozen instance set (ordered as the worklist freezes it) from EVM exits,
    and the discovery defects (a node whose EVM segment is incomplete or exits
    to an unmapped pc cannot be proved; it stays in the set and fails there)."""
    prover = setup.prover
    registered, queue, defects = set(), [], []

    def add(pc, state, joint):
        for spec in verifier._discover(pc, state, joint, budget):
            if spec not in registered:
                if len(registered) >= verifier.max_instances:
                    raise ValueError("specialization instance budget exhausted")
                registered.add(spec)
                queue.append(spec)

    for p in setup.entry_x86:
        add(setup.epc, setup.initial, And(setup.premise, p.condition))
    cursor = 0
    while cursor < len(queue):
        budget()
        spec = queue[cursor]
        cursor += 1
        context = prover.schema.build_havoc(
            prefix=f"blk{spec.pc}_{spec.stack_depth}_{spec.memory_size}_{spec.free_memory_pointer}",
            host_gas_uf_enabled=prover.host_gas_uf_enabled, assume_calldata_offset_no_overflow=False,
            abstract_calldataload_words=False, **spec.as_havoc_kwargs())
        state = context.state
        premise = And(*(state.assumptions or []))
        evm, gaps = run_evm_segment(prover.evm_blocks, state.copy(), spec.pc, set(prover.pc_to_addr),
                                    max_depth=prover.max_depth)
        defects += [f"pc={spec.pc} {spec}: {gap}" for gap in gaps]
        for e in evm:
            if e.kind == "terminal":
                continue
            if e.location not in prover.pc_to_addr:
                defects.append(f"pc={spec.pc} {spec}: successor pc={e.location} is unmapped")
                continue
            add(e.location, e.state, And(premise, e.condition))
    return tuple(sorted(registered, key=order_key)), tuple(defects)


def proof_groups(ordered, blocks, constant_insensitive):
    """{proof instance k: its contexts, in frozen order}; k = c when off."""
    slots = {b.pc: sensitive_slots(b) for b in blocks} if constant_insensitive else None
    groups = {}
    for c in ordered:
        groups.setdefault(project(c, slots[c.pc]) if slots else c, []).append(c)
    return {k: tuple(v) for k, v in groups.items()}


# ---------------------------------------------------------------- workers

_WORKER = {}


def _init_worker(stem, options, ordered, parent_pid, pair_workers):
    # Node-level parallelism replaces the per-node pair pool unless asked for.
    os.environ["BLOCK_PAIR_WORKERS"] = str(pair_workers)
    from verification.block_equivalence import _exit_with_parent
    _exit_with_parent(parent_pid)
    load_worker(stem, options, ordered)


def load_worker(stem, options, ordered):
    """The worker's prover and frozen target sets (also usable in-process)."""
    evm, x86, initial, verifier = build_inputs(stem, options)
    result = BlockProgramResult()
    setup = verifier._setup(evm, x86, initial, result, monotonic(), [])
    from verification.instruction_chain import attach_hints
    attach_hints(setup.prover, options, stem)  # before the identity is read: the hints are part of it
    targets = {}
    for spec in ordered:
        targets.setdefault(spec.pc, []).append(spec)
    memory = options.get("node_memory_mb")
    _WORKER.update(setup=setup, targets={pc: tuple(v) for pc, v in targets.items()},
                   identity=setup.prover.portable_identity,
                   memory_budget=None if memory is None else int(memory * 2**20),
                   status_dir=options.get("status_dir"))


def slim(obligation):
    """The obligation with its formula text replaced by a sha256 fingerprint,
    lemmas recursively. No consumer reads the text (proved/complete look at
    names, answers and lemmas); kept whole it made the parent hold up to
    460MB per node (R30: 9.2GB after 2.7h, swap and disk exhausted)."""
    text = obligation.formula
    if not text.startswith("sha256:"):
        text = "sha256:" + sha256(text.encode()).hexdigest()
    return replace(obligation, formula=text, lemmas=tuple(slim(lemma) for lemma in obligation.lemmas))


def slim_theorem(value, memo=None):
    """`value` with every Obligation inside slimmed: walks dataclasses,
    tuples and lists of any certificate kind (summary hits nest lemma,
    copy/MCOPY induction and dead-hit certificates). Shared objects stay
    shared (memo by id); anything else is returned as is."""
    from dataclasses import fields, is_dataclass
    from verification.block_equivalence import Obligation
    memo = {} if memo is None else memo
    if id(value) in memo:
        return memo[id(value)]
    if isinstance(value, Obligation):
        # slim() through the memo: a lemma shared by many records (an instruction-chain leaf is a dependency of
        # every derived record and H2 edge of its node) is slimmed once and stays shared.
        text = value.formula if value.formula.startswith("sha256:") else (
            "sha256:" + sha256(value.formula.encode()).hexdigest())
        out = replace(value, formula=text, lemmas=tuple(slim_theorem(lemma, memo) for lemma in value.lemmas))
    elif is_dataclass(value) and not isinstance(value, type):
        changes = {}
        for f in fields(value):
            if f.init:
                old = getattr(value, f.name)
                new = slim_theorem(old, memo)
                if new is not old:
                    changes[f.name] = new
        out = replace(value, **changes) if changes else value
    elif isinstance(value, (tuple, list)):
        items = [slim_theorem(v, memo) for v in value]
        out = type(value)(items) if any(a is not b for a, b in zip(items, value)) else value
    else:
        out = value
    memo[id(value)] = out
    return out


_SCREEN_GOALS = ("stack_geometry", "stack_constant_predicate")


def _symbols(term):
    """Names of the uninterpreted constants and functions in `term` (binders entered)."""
    names, seen, work = set(), set(), [term]
    while work:
        t = work.pop()
        if t.get_id() in seen:
            continue
        seen.add(t.get_id())
        if is_quantifier(t):
            work.append(t.body())
        elif is_app(t):
            if t.decl().kind() == Z3_OP_UNINTERPRETED:
                names.add(t.decl().name())
            work.extend(t.children())
    return names


def _congruent_arguments(conjunct):
    """[(a_i, b_i)] whose equalities imply `conjunct` = (L == R) by congruence, or None.

    simplify(L), simplify(R) are descended in parallel through applications of
    one uninterpreted f (a hash, a host-call result) and through a Concat in
    which a single part differs (Safe 5377: sha3_bytes_66(0x1901 ‖ s ‖
    sha3_slice(λ, n))); the differing leaves are returned. None unless the
    root is such an f."""
    if not is_eq(conjunct):
        return None

    def same(a, b):
        return is_app(a) and is_app(b) and a.num_args() > 0 and a.decl().eq(b.decl()) and a.num_args() == b.num_args()

    def leaves(a, b, out):
        differ = [(x, y) for x, y in zip(a.children(), b.children()) if not x.eq(y)] if same(a, b) else None
        if differ and (a.decl().kind() == Z3_OP_UNINTERPRETED
                       or (a.decl().kind() == Z3_OP_CONCAT and len(differ) == 1
                           and differ[0][0].size() == differ[0][1].size())):
            for x, y in differ:
                leaves(x, y, out)
        else:
            out.append((a, b))
        return out

    left, right = simplify(conjunct.arg(0)), simplify(conjunct.arg(1))
    if not (same(left, right) and left.decl().kind() == Z3_OP_UNINTERPRETED) or left.eq(right):
        return None
    return leaves(left, right, [])


def shared_bases(bases, goals):
    """{conjunct id: common base} for the goal conjuncts of two or more edges.

    bases[n] is edge n's base, goals[n] its [(target, RelationGoals)]. Edges
    of one node often end in states whose goal conjuncts are the same terms
    (Permit2 8750 d11: 12 edges; memory_0 and return_data_source_* each
    shared by 2, memory_size / memory_gas / gas by 6), their bases differing
    only in branch literals (the STATICCALL success flag). The common base is
    the conjunction of the conjuncts every such base has (first edge's order),
    so each base implies it: base_n ∧ ¬c is a strengthening of common ∧ ¬c,
    and one refutation of the latter proves c on every one of those edges."""
    from verification.block_equivalence import _conjuncts
    owners = {}
    for n, targets in enumerate(goals):
        for _, relation in targets:
            for g in relation:
                for c in _conjuncts(g.condition):
                    owners.setdefault(c.get_id(), set()).add(n)
    conjuncts = [_conjuncts(b) for b in bases]
    ids = [{c.get_id() for c in cs} for cs in conjuncts]
    out = {}
    for key, edges in owners.items():
        if len(edges) < 2:
            continue
        first, *rest = sorted(edges)
        common = set.intersection(*(ids[n] for n in rest)) if rest else ids[first]
        out[key] = And(*(c for c in conjuncts[first] if c.get_id() in common))
    return out


class _ConditionalEligibility:
    """The original no-binder/has-ITE predicates, shared across a context DAG.

    Binders and open Vars are not entered. Each keyed term stays alive, so
    neither its AST id nor its context id can be recycled while memoized.
    This only selects an optional proof route; it never rewrites a formula.
    """

    def __init__(self, budget):
        self.memo, self.budget = {}, budget

    def flags(self, root):
        work = [(root, False)]
        while work:
            self.budget()
            term, ready = work.pop()
            key = (id(term.ctx), term.get_id())
            if key in self.memo:
                continue
            if not is_app(term):
                self.memo[key] = (term, False, False)
                continue
            if not ready:
                work.append((term, True))
                work.extend((c, False) for c in term.children()
                            if (id(c.ctx), c.get_id()) not in self.memo)
                continue
            children = [self.memo[(id(c.ctx), c.get_id())] for c in term.children()]
            self.memo[key] = (term, all(c[1] for c in children),
                              term.decl().kind() == Z3_OP_ITE or any(c[2] for c in children))
        return self.memo[(id(root.ctx), root.get_id())][1:]


def prepare_shared(prover, bases, goals):
    """Context-local exact goal normalization and checked common-premise proofs.

    Only a proved weakening may cross edges. Each proof keeps its original
    used conjuncts alive and is offered only when those conjuncts occur in
    the current edge's base. It never enters the legacy global ``done`` map.
    """
    from common.store_forwarding import forward_selects, join_extracts
    from verification.block_equivalence import (_QUICK_EXACT_MS, _ROW_GROUP_DEPTH, _ROW_GROUP_MIN,
                                                _conjuncts, _ite_conditions, _no_binder,
                                                refute_conditional_ites, solve_query, Obligation)
    shared = dict(bases=shared_bases(bases, goals), done={})
    if len(bases) < _ROW_GROUP_MIN:
        return shared
    deadline = getattr(prover, "deadline", None)

    def budget():
        if deadline is not None and monotonic() >= deadline:
            raise ProofBudgetExceeded("proof wall budget exhausted")

    # Deduplicate original goals before scanning or normalizing; no array-wide
    # normalization for contexts without a ground conditional equality.
    candidates, inspected = {}, set()
    eligibility = _ConditionalEligibility(budget)
    for owner, targets in enumerate(goals):
        for _, relation in targets:
            for g in relation:
                for c in _conjuncts(g.condition):
                    budget()
                    key = c.get_id()
                    if key not in inspected:
                        inspected.add(key)
                        if is_eq(c) and all(eligibility.flags(c)):
                            candidates[key] = (c, set())
                    if key in candidates:
                        candidates[key][1].add(owner)
    if len(set().union(*(owners for _, owners in candidates.values()))) < _ROW_GROUP_MIN:
        return shared
    forwarded, joined, canonical, groups = {}, {}, {}, {}
    shared.update(forwarded=forwarded, joined=joined, canonical=canonical, canonical_proofs=defaultdict(list))
    for c, owners in candidates.values():
        budget()
        exact = join_extracts(forward_selects(c, forwarded), joined)
        normalized = simplify(exact, bv_sort_ac=True)
        if is_true(normalized) or not _no_binder(exact) or not _ite_conditions(exact):
            continue
        canonical[c.get_id()] = (c, normalized)  # keeps original and normalized AST ids alive
        group = groups.setdefault(normalized.get_id(), (normalized, []))
        group[1].append((exact, owners))
    parts = [_conjuncts(base) for base in bases]
    ids = [{c.get_id() for c in cs} for cs in parts]
    quick = min(_QUICK_EXACT_MS, prover.timeout_ms)
    for normalized, rows in groups.values():
        owners = sorted(set().union(*(owners for _, owners in rows)))
        work = [(owners, 0)] if len(owners) >= _ROW_GROUP_MIN else []
        while work:
            budget()
            owners, depth = work.pop()
            used = set.intersection(*(ids[n] for n in owners))
            keep = tuple(c for c in parts[owners[0]] if c.get_id() in used)
            until = monotonic() + quick / 1000
            if deadline is not None:
                until = min(until, deadline)
            # Keep Eq operand boundaries: simplifying the whole predicate can
            # split it into And, which the conditional route does not accept.
            representative = next(exact for exact, edges in rows if edges.intersection(owners))
            common = join_extracts(forward_selects(And(*keep), forwarded), joined)
            query = And(common, Not(representative))
            left = max(0, int((until - monotonic()) * 1000))
            _, answer, records = refute_conditional_ites(query, left, until) if left else (query, "unknown", ())
            if answer != "unsat":
                left = max(0, int((until - monotonic()) * 1000))
                if left and solve_query(query, left) == "unsat":
                    answer, records = "unsat", (Obligation("canonical_common_exact", query.sexpr(), "unsat"),)
            if answer == "unsat" and records and all(r.proved for r in records):
                shared["canonical_proofs"][normalized.get_id()].append(
                    (frozenset(used), (normalized, representative, *keep), tuple(slim(r) for r in records)))
            elif depth < _ROW_GROUP_DEPTH and len(owners) >= 2 * _ROW_GROUP_MIN:
                half = len(owners) // 2
                work.extend([(owners[half:], depth + 1), (owners[:half], depth + 1)])
    return shared


def _canonical_ready(shared, base, goals, name):
    """Checked proofs local to this base, separate from global shared results."""
    from verification.block_equivalence import _conjuncts, Obligation
    if shared is None or not shared.get("canonical_proofs"):
        return {}
    ids = {c.get_id() for c in _conjuncts(base)}
    ready = {}
    for _, relation in goals:
        for g in relation:
            for c in _conjuncts(g.condition):
                key = c.get_id()
                if key in ready or key not in shared["canonical"]:
                    continue
                _, normalized = shared["canonical"][key]
                for used, _alive, records in shared["canonical_proofs"].get(normalized.get_id(), ()):
                    if used <= ids:
                        ready[key] = [Obligation(f"{name}_canonical_{len(ready)}",
                            "exact goal normalization; checked common premise is a subset of this base", "unsat",
                            lemmas=records, required_lemmas=tuple(r.name for r in records),
                            provenance="h2_canonical_common_premise")]
                        break
    return ready


def close_edge(prover, name, base, goals, shared=None):
    """The edge record for base ⇒ ∨_t R_t, goals = [(target, RelationGoals)].

    One target at a time: base ⇒ R_t implies the disjunction, and R_t is a
    conjunction, so each conjunct is refuted on its own (base ∧ ¬c); the
    record is proved only with every part as a lemma (like _goal_split). The
    disjunction hides both from the routes (Safe 2586 / CErc20 4236 H2: the
    whole Or stayed unknown, every part proves). Targets whose stack goals a
    quick query can falsify are skipped; a conjunct first tries to be valid
    on its own (generalized products, bit-vector abstraction: both only add
    models), which closes the gas mirror R13 fields in 0.2s where every route
    with the premise stayed unknown. Anything unproved falls back to the
    original whole-disjunction check.

    Targets of one edge share every target-independent conjunct (the live
    stack, memory, gas, mirrors): its outcome is kept per edge, a proof is
    reused and a failure skips the next target with it (Safe 2405 t5 / 8915
    t1 re-ran 500-1000s of identical queries). A screen conjunct is also
    falsified by constraint independence: if the base conjuncts sharing no
    symbol with c are dropped, cone ∧ ¬c SAT means base ∧ ¬c is SAT (unless
    the rest of the base is unsatisfiable, i.e. the edge is vacuous, which the
    whole-disjunction fallback still covers) — Safe 8915 t0 needs entry slot
    14 = 0 which no base conjunct mentions: 0.0s, where base ∧ ¬c ran 3635s
    unknown looking for a model of the whole premise.

    `shared` (optional, one per context: {"bases": shared_bases(...), "done": {}})
    carries conjuncts across the context's edges: one that other edges also
    need is refuted once over the common base (each edge's base implies it);
    a failed shared attempt leaves the edge to its own base.
    """
    from verification.block_equivalence import (_QUICK_EXACT_MS, Obligation, _conjuncts, _generalize_products,
                                                abstract_divrem_results, refute_conditional_ites,
                                                refute_over_bv_abstraction, solve_query)
    from common.store_forwarding import forward_selects, join_extracts
    quick = min(_QUICK_EXACT_MS, prover.timeout_ms)
    forwarded, joined = (shared.get("forwarded", {}), shared.get("joined", {})) if shared is not None else ({}, {})
    ready = _canonical_ready(shared, base, goals, name)
    outcome = {}  # conjunct id -> proving records, or None once failed (Z3 ASTs are hash-consed)
    index = []  # [(simplified base conjunct, its symbols)], on first use

    def independent_model(c):
        if not index:
            index.extend((t, _symbols(t)) for t in (simplify(b) for b in _conjuncts(base)))
        c = simplify(c)
        cone, picked, rest, grew = _symbols(c), [], list(index), True
        while grew:
            grew = False
            for item in list(rest):
                if item[1] & cone:
                    picked.append(item[0])
                    cone |= item[1]
                    rest.remove(item)
                    grew = True
        # The whole base in the cone is the plain screen below (already tried).
        return bool(rest) and solve_query(And(*picked, Not(c)), quick) == "sat"

    def reused(parts, part):
        dependencies = tuple(parts)
        return [Obligation(part, "checked H2 common premise weakens this edge base", "unsat",
                           lemmas=dependencies, required_lemmas=tuple(r.name for r in dependencies),
                           provenance="h2_shared_weakening")]

    for t, (spec, relation) in enumerate(goals):
        # A shared proof used a weakening of this base, or no premise at all.
        if shared is not None:
            cached = [ready.get(c.get_id(), shared["done"].get(c.get_id()))
                      for g in relation for c in _conjuncts(g.condition)]
            if cached and all(parts is not None for parts in cached):
                return Obligation(name, f"base => relation of target {spec!r}", "unsat",
                                  lemmas=tuple(r for parts in cached for r in parts),
                                  provenance="h2_shared_weakening")
        screen = [g for g in relation if g.name in _SCREEN_GOALS]
        # A wrong target is refuted by propagation (base ∧ g unsat, ~0s); showing
        # base ∧ ¬g sat needs a model of the whole premise (CErc20 14263: 37/37
        # wrong targets 0.0s vs 2-12s, mostly unknown). Skipping is sound either way.
        if any(solve_query(And(base, c), quick) == "unsat" for g in screen for c in _conjuncts(g.condition)) or any(
                independent_model(c) for g in screen for c in _conjuncts(g.condition)) or any(
                solve_query(And(base, Not(g.condition)), quick) == "sat" for g in screen):
            continue
        parts, hard, owners, local = [], [], [], {}
        for g in relation:
            for k, conjunct in enumerate(_conjuncts(g.condition)):
                key = conjunct.get_id()
                if key in outcome:
                    if outcome[key] is None:
                        break  # failed for an earlier target
                    parts.extend(outcome[key])
                    continue
                cached = ready.get(key, shared["done"].get(key) if shared is not None else None)
                if cached is not None:
                    outcome[key] = reused(cached, f"{name}_shared_{len(outcome)}")
                    parts.extend(outcome[key])
                    continue
                part = f"{name}_t{t}_{g.name}_{k}"
                started = monotonic()
                # A callEngine mirror goal reads [R13+off] back through the exit
                # state's byte stores: forwarded (exact) and rejoined (identity)
                # it is `field == field` (CErc20 10233 gas_remaining: 0.0s,
                # where every route with the premise stayed unknown).
                exact = Not(join_extracts(forward_selects(conjunct, forwarded), joined))
                if is_false(simplify(exact)):
                    outcome[key] = [Obligation(part, exact.sexpr(), "unsat", elapsed_seconds=monotonic() - started)]
                    if shared is not None and key in shared["bases"]:
                        shared["done"][key] = [slim(r) for r in outcome[key]]
                    parts.extend(outcome[key])
                    continue
                # H2 often needs only a remainder's branch, not its 512-bit circuit.
                forwarded_query = And(join_extracts(forward_selects(base, forwarded), joined), exact)
                query, changed = abstract_divrem_results(forwarded_query)
                if changed and solve_query(simplify(query), quick) == "unsat":
                    outcome[key] = [Obligation(f"{part}_divrem", query.sexpr(), "unsat",
                                              elapsed_seconds=monotonic() - started)]
                    parts.extend(outcome[key])
                    continue
                _, answer, conditional = refute_conditional_ites(
                    forwarded_query, quick, getattr(prover, "deadline", None))
                if answer == "unsat" and conditional and all(r.proved for r in conditional):
                    # This proof uses this edge's base, so it is never shared with a sibling.
                    outcome[key] = list(conditional)
                    parts.extend(outcome[key])
                    continue
                general = Not(_generalize_products(conjunct))
                if refute_over_bv_abstraction(general, quick)[1] == "unsat":
                    outcome[key] = [Obligation(part, general.sexpr(), "unsat", elapsed_seconds=monotonic() - started)]
                    if shared is not None and key in shared["bases"]:
                        shared["done"][key] = [slim(r) for r in outcome[key]]
                    parts.extend(outcome[key])
                    continue
                # f(a…) == f(b…), f uninterpreted (a hash over a memory slice): by
                # congruence base ⇒ ∧ a_i = b_i suffices, one part per argument
                # (an array one is skolemized by _check, then each read is plain
                # and the blast / normalize routes apply). The routes never get
                # inside the lambda arguments (Safe 2405 sha3_slice: 2897s
                # unknown; per argument 8-25s). Only a strengthening: may fail
                # where base itself constrains f, never proves anything false.
                pairs = _congruent_arguments(conjunct)
                if pairs is not None:
                    lemma = And(*(a == b for a, b in pairs), Not(conjunct))
                    if solve_query(lemma, quick) == "unsat":
                        local[key] = [Obligation(f"{part}_congruence", lemma.sexpr(), "unsat",
                                                 elapsed_seconds=monotonic() - started)]
                        parts.extend(local[key])
                        for i, (a, b) in enumerate(pairs):
                            hard.append((f"{part}_arg{i}", And(base, a != b), ""))
                            owners.append(key)
                        continue
                # A conjunct other edges also need (shared_bases): refuted once over the
                # common base, a weakening of this one; failing that, on this base as before.
                if shared is not None and key in shared["bases"]:
                    if key not in shared["done"]:
                        mine = []
                        prover._check(f"{part}_shared", And(shared["bases"][key], Not(conjunct)), mine)
                        shared["done"][key] = [slim(r) for r in mine] if mine[-1].proved else None
                    if shared["done"][key] is not None:
                        outcome[key] = reused(shared["done"][key], f"{part}_reuse")
                        parts.extend(outcome[key])
                        continue
                hard.append((part, And(base, Not(conjunct)), ""))
                owners.append(key)
            else:
                continue
            break  # a conjunct failed for an earlier target: so does this target
        else:
            records = []
            ok = all(prover._check_all(hard, records))  # stops at the first failed part, like the serial loop
            for key in set(owners):
                mine = [r for k, r in zip(owners, records) if k == key]
                if not all(r.proved for r in mine):
                    outcome[key] = None
                elif len(mine) == owners.count(key):  # all its parts checked (else: not reached)
                    outcome[key] = local.get(key, []) + mine
            if ok:
                return Obligation(name, f"base => relation of target {spec!r}", "unsat", lemmas=tuple(parts + records))
    records = []
    prover._check(name, And(base, Not(Or(*(And(*(g.condition for g in r)) for _, r in goals)))), records)
    return records[-1]


def reset_node_caches(prover):
    """Bound a long-lived worker's memory: drop the term-keyed caches between nodes.

    They keep their ASTs alive (needed so recycled ids never alias), so without
    this a worker grows by GBs per hour. Pure caches: only speed changes; shape
    lemmas and summary templates, which are expensive and small, are kept.
    """
    from common.store_forwarding import clear_memo
    clear_memo()
    prover._lemma_cache.clear()
    gc.collect()


def forget_summary_failures():
    """Drop the per-process caches of failed summary-slice proofs. Pure
    caches (a slice is simply proved again), but a failure recorded while
    an over-budget node was being interrupted is not the slice's own."""
    from x86_64.summaries import div_proof, memgas_proof, mul_proof, shift_proof, signed_proof
    div_proof._FAILURE.clear()
    memgas_proof._FAILURE.clear()
    mul_proof._PROOF_FAILURE_CACHE.clear()
    shift_proof._FAILURE.clear()
    signed_proof._FAILURE.clear()


def _quick_whole_h2(prover, names, bases, goals, records):
    """Fill only exact UNSAT edge records, within one query-timeout phase."""
    from verification.block_equivalence import _QUICK_EXACT_MS, Obligation, check_abort, solve_query
    assert len(names) == len(bases) == len(goals) == len(records)
    until = monotonic() + prover.timeout_ms / 1000
    if prover.deadline is not None:
        until = min(until, prover.deadline)
    for index, (name, base, targets) in enumerate(zip(names, bases, goals)):
        if monotonic() >= until:
            break
        check_abort()
        started = monotonic()
        formula = And(base, Not(Or(*(And(*(g.condition for g in relation)) for _, relation in targets))))
        query = simplify(formula)
        budget = min(_QUICK_EXACT_MS, prover.timeout_ms, int((until - monotonic()) * 1000))
        if budget <= 0:
            break
        if solve_query(query, budget) == "unsat":
            records[index] = slim(Obligation(name, formula.sexpr(), "unsat",
                elapsed_seconds=monotonic() - started, provenance="h2_whole_exact"))


def prove_instance(spec, node_seconds, deadline_epoch, contexts=None, chain=False):
    """Worker task: the proof of `spec` (a proof instance k), then for every
    context c of k (default: k itself) its H2 edges into the frozen set, on
    k's exits under premise_k ∧ E_c.

    Runs under a NodeMonitor (common/node_monitor): the result records the
    worker pid, start / end time and RSS (start, peak, end), and the
    worker's status file names the node while it runs. Over the worker's
    memory budget the node stops at its next solver call and only it is
    reported inconclusive (reason: the budget); a worker still holding most
    of the budget after its caches are dropped asks to be replaced
    ("recycle", NodePool). Stopping concludes nothing, so only proofs are lost."""
    contexts = (spec,) if contexts is None else tuple(contexts)
    budget, status = _WORKER.get("memory_budget"), _WORKER.get("status_dir")
    started = monotonic()
    monitor = NodeMonitor(repr(spec), budget,
                          status_path=None if status is None else Path(status) / f"worker-{os.getpid()}.json")
    with monitor:
        try:
            node = _prove_instance(spec, node_seconds, deadline_epoch, contexts, chain)
        except NodeMemoryExceeded as exc:
            node = dict(spec=spec, contexts=contexts, identity=_WORKER["identity"], proved=False,
                        status="inconclusive", theorem=None, expected=(), edges=(), reasons=(str(exc),),
                        seconds=monotonic() - started, queries=0, failed=[])
        if monitor.exceeded is not None:
            forget_summary_failures()
        reset_node_caches(_WORKER["setup"].prover)
        release_memory()
    node.update(monitor.info())
    # ponytail: replace the worker when 3/4 of its budget stays resident after the node.
    node["recycle"] = budget is not None and (monitor.exceeded is not None or rss_bytes() > 0.75 * budget)
    return node


def _prove_instance(spec, node_seconds, deadline_epoch, contexts, chain=False):
    proof_cache.reset_local_unknown()
    setup = _WORKER["setup"]
    prover, identity = setup.prover, _WORKER["identity"]
    reset_node_caches(prover)
    started = monotonic()
    prover.deadline = started + max(0.0, deadline_epoch - time.time())
    prover.node_timeout_seconds = node_seconds
    chain_attempt = None
    hint = (getattr(prover, "instruction_hints", None) or {}).get(spec.pc)
    if hint is not None and chain:
        # The attempt after a failed legacy one (the scheduler's _attempt): the instruction chain first, capped;
        # proved: its result; otherwise (not applicable: None, or not proved) the legacy prover takes the rest of
        # the budget. Every node is still decided by one producer's complete theorem and closed H2.
        from verification.instruction_chain import CHAIN_SECONDS, prove_node
        chained = prove_node(prover, spec, contexts, hint, _WORKER["targets"], identity,
                             min(node_seconds, CHAIN_SECONDS))
        if chained is not None and chained["proved"] and not chained["reasons"]:
            return chained
        spent = monotonic() - started
        chain_attempt = dict(applicable=chained is not None, seconds=round(spent, 1),
                             reasons=[] if chained is None else list(chained["reasons"])[:3])
        reset_node_caches(prover)
        prover.node_timeout_seconds = node_seconds = max(1.0, node_seconds - spent)
    from verification.block_summaries import lemma_seconds
    spent = lemma_seconds()
    node = prover.prove(spec)
    # Shared summary lemmas (proved once, then in-process and persisted) are
    # not this node's cost: if they took a real share of its budget, prove it
    # again on a fresh one; the lemmas are reused now. Only budgets change.
    # ponytail: 10% threshold; retry repeats the pre-lemma work of the node.
    if (not node.proved and lemma_seconds() - spent >= 0.1 * node_seconds
            and not any("solver=sat" in r for r in node.reasons)):
        node = prover.prove(spec)
    proved = node.proved
    expected, edges, reasons = [], [], list(node.reasons)
    if proved:
        pairs = []
        for i, j, pc in node.theorem.cutpoint_manifest:
            e, x = node.evm_outcomes[i], node.x86_outcomes[j]
            expected.append((i, j))
            targets = _WORKER["targets"].get(pc, ())
            try:
                goals = [(s, prover.schema.relation_goals(e.state, x.state, s,
                                                         memory_snapshot=node.context.memory_snapshot))
                         for s in targets]
                pairs.append((i, j, e, x, targets, goals))
            except Exception as exc:
                reasons.append(f"H2 ({i},{j}) into pc={pc}: {type(exc).__name__}: {exc}")
        program_deadline = prover.deadline
        entry = node.context.state  # k's havoc state: both views read the same entry symbols
        for n, c in enumerate(contexts):
            assumed = dropped(spec, c)
            tag = f"c{n}_" if contexts != (spec,) else ""
            if not weakens(spec, c):
                reasons.append(f"context {c!r} is not a weakening of {spec!r}")
                continue
            # H2 gets its own node-sized budget per context, still inside the program wall.
            prover.deadline = min(program_deadline, monotonic() + node_seconds)
            base = And(node.premise, stack_constant_condition(entry, entry, assumed))
            context_records = [None] * len(pairs)
            try:
                # Not needed for soundness (an empty context has no entries); guards a wrong E_c.
                if assumed and not prover._check(f"context_nonempty_{tag}", base, [], expected="sat"):
                    reasons.append(f"context {c!r}: premise ∧ E_c empty or unknown")
                    continue
                bases = [And(base, e.condition, x.condition) for _, _, e, x, _, _ in pairs]
                names = [f"H2_{tag}{i}_{j}" for i, j, *_ in pairs]
                _quick_whole_h2(prover, names, bases, [goals for *_, goals in pairs], context_records)
                hard = [index for index, record in enumerate(context_records) if record is None]
                if hard and monotonic() >= prover.deadline:
                    raise ProofBudgetExceeded("proof wall budget exhausted")
                shared = prepare_shared(prover, [bases[index] for index in hard],
                    [pairs[index][-1] for index in hard]) if hard else None
                for index in hard:
                    i, j, e, x, targets, goals = pairs[index]
                    # Keep each edge's evidence, without retaining every SMT text until H2 finishes.
                    record = context_records[index] = slim(close_edge(prover, names[index], bases[index], goals, shared))
                    if not record.proved:
                        reasons.append(f"H2 {tag}({i},{j}) not closed into pc={e.location} (solver={record.answer})")
            except ProofBudgetExceeded:
                # The context's H2 budget ran out: its edges are not closed (unknown), not a worker error.
                reasons.append(f"H2 {tag}budget exhausted (solver=unknown)")
            finally:
                for (i, j, e, x, targets, goals), record in zip(pairs, context_records):
                    if record is not None:
                        edges.append(EdgeCertificate(c, (i, j), e.location, targets, digest(targets), identity,
                                                     record, assumed))
        prover.deadline = program_deadline
    return dict(spec=spec, contexts=contexts, identity=identity, proved=proved, status=node.status,
                theorem=slim_theorem(node.theorem) if proved else None, expected=tuple(expected),
                edges=slim_theorem(tuple(edges)),
                reasons=tuple(reasons), seconds=monotonic() - started, queries=node.queries,
                failed=[dict(name=o.name, answer=o.answer, expected=o.expected, seconds=o.elapsed_seconds)
                        for o in node.obligations if not o.proved],
                chain_attempt=chain_attempt)


# ---------------------------------------------------------------- certificate

def _producer_ok(theorem, prover, proof):
    """The producer registry: a legacy BlockTheorem, or an instruction-chain theorem whose chain starts at this
    block's real entry and depth, from the hint the prover loaded for it (the hints' digest is part of the
    portable identity). Any other theorem type is an unregistered producer."""
    if type(theorem) is BlockTheorem:
        return True
    if type(theorem) is not InstructionBlockTheorem:
        return False
    hint = (getattr(prover, "instruction_hints", None) or {}).get(proof.pc)
    if hint is None or theorem.hint_digest != hint.digest:
        return False
    # The chain payload covers exactly the hint's ops and intervals, from the block's real entry at this depth: a
    # shorter or re-cut chain is not this producer's theorem. (The heights are the EVM model's, carried in the
    # trusted payload; complete() checks that they link.)
    expected = tuple((o.index, o.start, o.end) for o in hint.ops)
    return (bool(expected) and tuple(c[:3] for c in theorem.chain) == expected
            and expected[0][1] == prover.pc_to_addr.get(proof.pc) and theorem.chain[0][3] == proof.stack_depth)


@dataclass(frozen=True)
class ParallelProgramCertificate:
    identity: str  # portable identity
    scope: str
    entry: EntryCertificate
    specializations: tuple
    nodes: tuple  # worker result dicts, one per specialization (context)

    def valid(self, prover, initial):
        """Data-only consumer (see the module docstring's trust boundary).

        A node's theorem is about its proof instance `proof_spec` (k), which
        must weaken the node's context (same pc/depth/MSize/fmp, K_k ⊆ K_c);
        every H2 edge of c assumes exactly D_c = K_c \\ K_k, and all contexts
        of one k pair the same outcomes. Which constants k drops is not
        checked: any weakening is sound, a bad one is only harder to prove.
        """
        if getattr(prover, "_issued_program_certificate", None) is not self:
            return False
        if self.identity != prover.portable_identity or not self.scope:
            return False
        if self.entry is None or self.entry.initial_digest != state_digest(initial):
            return False
        names = [o.name for o in self.entry.obligations]
        if (not {"init_nonempty", "evm_coverage", "x86_coverage"} <= set(names)
                or not all(o.proved for o in self.entry.obligations)
                or len(self.entry.edges) != self.entry.path_count or self.entry.path_count < 1
                or {e.pair for e in self.entry.edges} != {(0, j) for j in range(self.entry.path_count)}):
            return False
        specs = set(self.specializations)
        if not specs or len(specs) != len(self.specializations):
            return False
        if len(self.nodes) != len(specs) or {n["spec"] for n in self.nodes} != specs:
            return False
        for edge in self.entry.edges:
            if edge.assumed or not self._edge_ok(edge, self.entry.evm_entry):
                return False
        exits = {}  # proof instance -> (outcome digest, cutpoint manifest), shared by its contexts
        for node in self.nodes:
            theorem, spec, proof = node["theorem"], node["spec"], node.get("proof_spec")
            if (node["identity"] != self.identity or not node["proved"] or node["reasons"]
                    or theorem is None or proof is None or theorem.spec != proof
                    or not weakens(proof, spec) or not theorem.complete):
                return False
            if not _producer_ok(theorem, prover, proof):
                return False
            # Pin H2 to the local theorem's actual exits, not two deletable worker lists.
            manifest = getattr(theorem, "cutpoint_manifest", None)
            if manifest is None or any(type(i) is not int or type(j) is not int
                    or not 0 <= i < theorem.evm_count or not 0 <= j < theorem.x86_count
                    or type(pc) is not int or pc not in prover.pc_to_addr for i, j, pc in manifest):
                return False
            targets = {(i, j): pc for i, j, pc in manifest}
            expected = tuple((i, j) for i, j, _ in manifest)
            if (len(targets) != len(manifest) or tuple(node["expected"]) != expected
                    or len(node["edges"]) != len(expected)
                    or {e.pair for e in node["edges"]} != set(expected)):
                return False
            shape = (theorem.outcome_digest, manifest)
            if exits.setdefault(proof, shape) != shape:
                return False
            assumed = dropped(proof, spec)
            for edge in node["edges"]:
                if (edge.source != spec or edge.assumed != assumed
                        or edge.target_pc != targets[edge.pair]
                        or not self._edge_ok(edge, edge.target_pc)):
                    return False
        return True

    def _edge_ok(self, edge, target_pc):
        registered = tuple(s for s in self.specializations if s.pc == target_pc)
        return (edge.target_pc == target_pc and edge.identity == self.identity and edge.obligation.proved
                and edge.targets == registered and edge.target_version == digest(registered)
                and set(edge.targets) <= set(self.specializations))


# ---------------------------------------------------------------- schedule

def verify_parallel(stem, options, *, workers=4, pair_workers=1, results_dir=None, progress_callback=None):
    """Discover, prove in `workers` processes, close; returns BlockProgramResult.

    results_dir: finished worker results are pickled there (keyed by the
    portable identity, the frozen set, the projection version, the proof
    instance and its contexts), so an interrupted run resumes without
    re-proving them.

    options["constant_insensitive"]: prove each proof instance k = π(c) once
    for all its contexts (module docstring); off: k = c.
    """
    start = monotonic()
    deadline_epoch = time.time() + options["wall_seconds"]
    evm_program, x86_program, initial_state, verifier = build_inputs(stem, options)
    result = BlockProgramResult()
    records = []
    try:
        setup = verifier._setup(evm_program, x86_program, initial_state, result, start, records)
        prover, initial = setup.prover, setup.initial
        from verification.instruction_chain import attach_hints
        attach_hints(prover, options, stem)  # before the identity is read: the hints are part of it
        identity = prover.portable_identity

        def budget():
            if monotonic() - start >= options["wall_seconds"]:
                raise ValueError("program wall budget exhausted")

        phase = monotonic()
        ordered, defects = discover(verifier, setup, budget)
        result.timings["discovery"] = monotonic() - phase
        result.reasons += tuple(f"discovery: {d}" for d in defects)
        result.diagnostics = {b.pc: {"status": "unvisited", "instances": []} for b in setup.evm}
        for spec in ordered:
            result.diagnostics[spec.pc]["status"] = "queued"

        # H0: the raw entry lands in the frozen set (parent, in-process states).
        phase = monotonic()
        targets = tuple(s for s in ordered if s.pc == setup.epc)
        entry_edges = []
        for j, p in enumerate(setup.entry_x86):
            goals = [(s, prover.schema.relation_goals(initial, p.state, s, memory_snapshot=None)) for s in targets]
            record = close_edge(prover, f"H0_{j}", And(setup.premise, p.condition), goals)
            if not record.proved:
                result.reasons += (f"H0_{j} not closed into pc={setup.epc} (solver={record.answer})",)
            entry_edges.append(EdgeCertificate(None, (0, j), setup.epc, targets, digest(targets), identity, record))
        entry = EntryCertificate(state_digest(initial), setup.raw, setup.epc,
                                 tuple(o for o in records if not o.name.startswith(("H0_", "H2_"))),
                                 tuple(entry_edges), paths_digest([setup.entry_evm], setup.entry_x86),
                                 len(setup.entry_x86))
        result.timings["entry_H0"] = monotonic() - phase

        phase = monotonic()
        insensitive = bool(options.get("constant_insensitive"))
        groups = proof_groups(ordered, setup.evm, insensitive)
        result.closure_checks.append(dict(phase="proof_instances", contexts=len(ordered), proof_instances=len(groups),
                                          projection=PROJECTION_VERSION if insensitive else None))
        done = _prove_all(stem, options, ordered, groups, identity, deadline_epoch, workers, pair_workers,
                          results_dir, result, progress_callback,
                          store_tag=f"-{PROJECTION_VERSION}" if insensitive else "",
                          chain_pcs=frozenset(getattr(prover, "instruction_hints", None) or {}))
        result.timings["proofs_and_H2"] = monotonic() - phase
        failed = [n for n in done.values() if not n["proved"] or n["reasons"]]
        result.reasons += tuple(f"local pc={n['spec'].pc} {n['spec']}: {'; '.join(n['reasons'])}" for n in failed)
        nodes = {c: dict(group, spec=c, proof_spec=k, edges=tuple(e for e in group["edges"] if e.source == c))
                 for k, group in done.items() for c in group.get("contexts", (k,))}
        missing = [s for s in ordered if s not in nodes]
        if missing:
            result.reasons += (f"{len(missing)} instances not attempted",)
        if result.reasons:
            raise ValueError("certificate withheld: unresolved local or closure obligations")
        certificate = ParallelProgramCertificate(identity, result.scope, entry, ordered,
                                                 tuple(nodes[s] for s in ordered))
        prover._issued_program_certificate = certificate
        if not certificate.valid(prover, initial):
            raise ValueError("parallel certificate consumer rejected the evidence")
        result.certificate = certificate
        result.status = "verified"
    except Exception as exc:
        result.reasons += (f"{type(exc).__name__}: {exc}",)
    result.elapsed_seconds = monotonic() - start
    return result


class WorkerDied(RuntimeError):
    """A NodePool worker exited while running a task (signal, OOM kill, os._exit)."""

    def __init__(self, pid, exitcode, status=None):
        self.pid, self.exitcode, self.status = pid, exitcode, status
        how = f"signal {-exitcode}" if exitcode is not None and exitcode < 0 else f"exit code {exitcode}"
        last = "" if status is None else (f" (node {status.get('node')}, state {status.get('state')}, "
                                          f"peak RSS {status.get('peak_rss_mb')} MB)")
        super().__init__(f"worker pid {pid} died with {how}{last}")

    @property
    def memory(self):
        """Killed for memory: our own hard ceiling, or a SIGKILL (the kernel OOM killer)."""
        return self.exitcode in (MEMORY_EXIT_CODE, -9) or (self.status or {}).get("state") == "killed"


def _pool_worker(conn, initializer, initargs):
    try:
        if initializer is not None:
            initializer(*initargs)
    except BaseException as exc:
        conn.send(("init_error", f"{type(exc).__name__}: {exc}"))
        return
    while True:
        try:
            task = conn.recv()
        except (EOFError, OSError):
            return
        if task is None:
            return
        fn, args = task
        try:
            out = ("ok", fn(*args))
        except BaseException as exc:
            out = ("error", f"{type(exc).__name__}: {exc}")
        conn.send(out)
        if out[0] == "ok" and isinstance(out[1], dict) and out[1].get("recycle"):
            return


class NodePool:
    """Worker processes with one pipe each, so a worker is watched and
    replaced on its own: one that dies (segfault, OOM kill, the node
    monitor's hard ceiling) fails only the task it was running (WorkerDied),
    and a worker whose result asks to be recycled is restarted after it.
    concurrent.futures' pool marks itself broken instead and fails every
    running task (and the run with it). The caller keeps at most `workers`
    tasks in flight."""

    def __init__(self, workers, initializer=None, initargs=(), context=None, status_dir=None):
        import multiprocessing
        self._context = context or multiprocessing.get_context("spawn")
        self._init = (initializer, initargs)
        self.status_dir = status_dir
        self._slots = [self._spawn() for _ in range(workers)]

    def _spawn(self):
        parent, child = self._context.Pipe()
        process = self._context.Process(target=_pool_worker, args=(child, *self._init), daemon=True)
        process.start()
        child.close()
        return dict(process=process, conn=parent, future=None)

    def _replace(self, n):
        """Stop slot n's worker (if still running) and start a fresh one there."""
        slot = self._slots[n]
        slot["process"].join(30)
        if slot["process"].is_alive():
            slot["process"].kill()
        slot["conn"].close()
        self._slots[n] = self._spawn()

    def submit(self, fn, *args):
        from concurrent.futures import Future
        n = next(k for k, s in enumerate(self._slots) if s["future"] is None)
        if not self._slots[n]["process"].is_alive():  # died while idle (a kill, the OS)
            self._replace(n)
        future = Future()
        future.set_running_or_notify_cancel()
        try:
            self._slots[n]["conn"].send((fn, args))
        except (BrokenPipeError, EOFError, OSError):  # died between the check and the send
            self._replace(n)
            self._slots[n]["conn"].send((fn, args))
        slot = self._slots[n]
        slot["future"] = future
        future.pid = slot["process"].pid
        return future

    def _status(self, pid):
        return None if self.status_dir is None else read_status(Path(self.status_dir) / f"worker-{pid}.json")

    def running(self):
        """Status (common/node_monitor) of every worker with a task in flight."""
        return [dict(self._status(s["process"].pid) or {}, pid=s["process"].pid)
                for s in self._slots if s["future"] is not None]

    def wait(self, timeout):
        """Futures finished within `timeout` seconds (results, errors, dead workers)."""
        from multiprocessing.connection import wait as ready_of
        busy = [s for s in self._slots if s["future"] is not None]
        if not busy:
            return set()
        ready = set(ready_of([s["conn"] for s in busy] + [s["process"].sentinel for s in busy], timeout))
        done = set()
        for n, slot in enumerate(self._slots):
            future, process = slot["future"], slot["process"]
            if future is None or (slot["conn"] not in ready and process.sentinel not in ready):
                continue
            message = None
            try:
                if slot["conn"].poll():
                    message = slot["conn"].recv()
            except (EOFError, OSError):
                pass
            if message is not None and message[0] == "init_error":
                raise RuntimeError(f"worker initializer failed: {message[1]}")
            if message is None:  # exited without an answer
                process.join(5)
                future.set_exception(WorkerDied(process.pid, process.exitcode, self._status(process.pid)))
            elif message[0] == "ok":
                future.set_result(message[1])
            else:
                future.set_exception(RuntimeError(message[1]))
            done.add(future)
            slot["future"] = None
            # A worker that answered and then exited (its result was already queued) is
            # replaced too: an idle dead slot would fail the next submit.
            if (message is None or not process.is_alive()
                    or (message[0] == "ok" and isinstance(message[1], dict) and message[1].get("recycle"))):
                self._replace(n)
        return done

    def shutdown(self):
        for slot in self._slots:
            slot["process"].kill()
            slot["conn"].close()


class LeaderFirstSchedule:
    """Submission order only; which instances get proved never depends on it.

    Items are proof instances. Siblings (same pc, MSize, fmp) share most proof-cache keys, so one leader
    per group runs first and its siblings are released once it finished. A
    leader that needed the full budget (first pass failed, retried) releases
    its siblings at the full budget directly: they mostly replay its cached
    queries, and a short first pass would just repeat the leader's failure.
    """

    def __init__(self, todo, first, full):
        self.first, self.full = first, full
        groups = {}
        for s in todo:
            groups.setdefault((s.pc, s.memory_size, s.free_memory_pointer), []).append(s)
        self.leaders, self.siblings, self.blocked = [], [], {}
        for members in groups.values():
            leader = min(members, key=lambda s: (len(s.stack_constants), s.stack_depth))
            self.leaders.append((leader, first))
            self.blocked[leader] = [s for s in members if s != leader]
        self.full_leaders = set()
        self.full_start = set()  # submitted at the full budget: no further retry

    def pop(self):
        """Next (spec, seconds): leaders (retries first) before released siblings."""
        queue = self.leaders or self.siblings
        spec, seconds = queue.pop(0) if queue else (None, None)
        if spec is not None and seconds >= self.full:
            self.full_start.add(spec)
        return spec, seconds

    def retry(self, spec):
        """Requeue at the full budget; a retried leader keeps its siblings blocked."""
        if spec in self.blocked:
            self.full_leaders.add(spec)
            self.leaders.insert(0, (spec, self.full))
        else:
            self.siblings.append((spec, self.full))

    def finish(self, spec):
        seconds = self.full if spec in self.full_leaders else self.first
        self.siblings += [(s, seconds) for s in self.blocked.pop(spec, ())]

    def add(self, specs, seconds):
        """New work released now (the contexts of a split proof instance)."""
        self.siblings += [(s, seconds) for s in specs]

    def pending(self):
        """Specs never submitted (still queued or blocked behind a leader)."""
        return ([s for s, _ in self.leaders + self.siblings]
                + [s for members in self.blocked.values() for s in members])


def stored_path(store, spec, contexts):
    """A finished group's pickle: keyed by the proof instance and its contexts."""
    return store / (sha256((repr(spec) + digest(contexts)).encode()).hexdigest()[:32] + ".pkl.z")


def load_stored(store, spec, contexts, identity):
    """The stored final result (proved or not) for exactly this group, or None."""
    path = stored_path(store, spec, contexts)
    if not path.exists():
        return None
    node = pickle.loads(zlib.decompress(path.read_bytes()))
    ok = (node["identity"] == identity and node["spec"] == spec
          and tuple(node.get("contexts", (spec,))) == contexts)
    return node if ok else None


def final_status(node):
    """A node is proved only with every H2 edge closed; a proved node with an
    open edge is inconclusive."""
    if node["proved"] and not node["reasons"]:
        return "proved"
    return "inconclusive" if node["proved"] else node["status"]


def _attempt(spec, seconds, first, chain_pcs, legacy_tried, chain_tried):
    """(budget, chain) of a node's next attempt. A block without an instruction-chain hint: as scheduled, legacy.
    With one: every node's first attempt is the legacy prover within the first-pass budget, whatever budget the
    schedule released it at (a sibling or a split context may come at the full one); the attempt after a failed
    legacy one tries the chain (then legacy with the rest, _prove_instance)."""
    if spec.pc not in chain_pcs:
        return seconds, False
    if spec in legacy_tried and spec not in chain_tried:
        return seconds, True
    return (seconds if spec in legacy_tried else min(seconds, first)), False


def _retry(node, spec, schedule, chain_pcs=frozenset(), legacy_tried=frozenset(), chain_tried=frozenset()):
    """Whether a node earns another attempt. Never after a counterexample (solver=sat). A block with a hint whose
    legacy attempt failed and which has not tried the chain: yes, even after a memory stop or at the full budget
    (that is how a block whose legacy proof runs out of time or memory gets the chain). Otherwise the full-budget
    retry of a first pass (an open H2 edge earns it too, the retry reproves the node), not after a memory stop: a
    longer legacy budget only grows further."""
    if final_status(node) == "proved" or any("solver=sat" in r for r in node["reasons"]):
        return False
    if spec.pc in chain_pcs and spec in legacy_tried and spec not in chain_tried:
        return True
    return spec not in schedule.full_start and not node.get("memory_exceeded")


def _prove_all(stem, options, ordered, groups, identity, deadline_epoch, workers, pair_workers, results_dir,
               result, progress_callback, store_tag="", chain_pcs=frozenset()):
    """Prove every proof instance of `groups` ({k: contexts}, updated in place
    when a group is split); returns {k: worker result}. `chain_pcs`: blocks with an instruction-chain hint."""
    import multiprocessing
    frozen = digest(ordered)
    store = None
    if results_dir is not None:
        store = Path(results_dir) / f"{identity[:16]}-{frozen[:16]}{store_tag}"
        store.mkdir(parents=True, exist_ok=True)

    def split(spec):
        # Fall back to the contexts themselves (k := c, the unprojected instance).
        contexts = groups.pop(spec)
        for c in contexts:
            if c in groups:
                raise ValueError(f"split context {c!r} collides with a proof instance")
            groups[c] = (c,)
        return [c for c in contexts if c != spec]

    def keep(spec, contexts, node):
        # Every final verdict is kept, so a restart redoes none of them; worker errors are not final.
        if store is not None and node["status"] != "error":
            stored_path(store, spec, contexts).write_bytes(zlib.compress(pickle.dumps(node), 6))

    done = {}
    if store is not None:
        for spec, contexts in list(groups.items()):
            node = load_stored(store, spec, contexts, identity)
            if node is not None and (node["proved"] or contexts == (spec,)):
                done[spec] = node
                _record(result, node, final_status(node))
            elif contexts != (spec,):
                singles = {c: n for c in contexts if (n := load_stored(store, c, (c,), identity)) is not None}
                if node is not None or singles:  # split in an earlier run
                    split(spec)
                    for c, n in singles.items():
                        done[c] = n
                        _record(result, n, final_status(n))
    first = options.get("first_pass_node_seconds") or options["node_seconds"]
    full = options["node_seconds"]
    schedule = LeaderFirstSchedule([s for s in groups if s not in done], min(first, full), full)
    legacy_tried, chain_tried = set(), set()  # per node: which producers it has tried (_attempt, _retry)
    # Worker status files (common/node_monitor): which node each worker runs, since when, how big.
    status_dir = options.get("status_dir") or tempfile.mkdtemp(prefix="block-workers-")
    options = dict(options, status_dir=status_dir)
    pool = NodePool(workers, _init_worker, (str(stem), options, ordered, os.getpid(), pair_workers),
                    multiprocessing.get_context("spawn"), status_dir)
    try:
        running = {}

        def fill():
            # At most `workers` in flight so the schedule, not the pool's FIFO, picks the next one.
            while len(running) < workers and time.time() < deadline_epoch:
                spec, seconds = schedule.pop()
                if spec is None:
                    return
                seconds, chain = _attempt(spec, seconds, min(first, full), chain_pcs, legacy_tried, chain_tried)
                (chain_tried if chain else legacy_tried).add(spec)
                running[pool.submit(prove_instance, spec, seconds, deadline_epoch, groups[spec], chain)] = spec

        fill()
        while running:
            left = deadline_epoch + 60 - time.time()
            if left <= 0:
                break
            finished = pool.wait(min(left, 60))
            for future in finished:
                spec = running.pop(future)
                try:
                    node = future.result()
                except Exception as exc:
                    node = dict(spec=spec, contexts=groups[spec], identity=identity, proved=False, status="error",
                                theorem=None, expected=(), edges=(),
                                reasons=(f"worker: {type(exc).__name__}: {exc}",), seconds=0.0, queries=0, failed=[],
                                pid=getattr(exc, "pid", getattr(future, "pid", None)))
                    if isinstance(exc, WorkerDied):
                        node.update({k: exc.status[k] for k in ("started_at", "peak_rss_mb", "memory_budget_mb")
                                     if exc.status and k in exc.status})
                        if exc.memory:
                            # Killed for memory: final for this node (a retry grows the same way).
                            node.update(status="inconclusive", memory_exceeded=str(exc))
                out_of_wall = time.time() >= deadline_epoch
                if out_of_wall and not node["proved"]:
                    # Queued behind the program wall: never attempted, not a failed proof.
                    _record(result, node, "not attempted")
                    continue
                retry = _retry(node, spec, schedule, chain_pcs, legacy_tried, chain_tried)
                if retry:
                    schedule.retry(spec)
                    _record(result, node, "deferred")
                elif not node["proved"] and groups[spec] != (spec,):
                    # k failed for good, or got sat (a model of the weaker R_k may lie
                    # outside every context): prove the contexts themselves.
                    seconds = full if spec in schedule.full_start else min(first, full)
                    schedule.finish(spec)
                    keep(spec, groups[spec], node)
                    schedule.add(split(spec), seconds)
                    _record(result, node, "split")
                    if spec in groups:  # k is itself a context: that proof just failed
                        done[spec] = dict(node, contexts=(spec,))
                        _record(result, node, final_status(node))
                        keep(spec, (spec,), done[spec])
                else:
                    done[spec] = node
                    schedule.finish(spec)
                    _record(result, node, final_status(node))
                    keep(spec, groups[spec], node)
            fill()
            result.running = pool.running()
            if progress_callback is not None:
                progress_callback(result)
        # Never submitted before the wall (queued, or blocked behind an unfinished leader).
        for spec in schedule.pending():
            _record(result, dict(spec=spec, reasons=(), seconds=0.0, queries=0, failed=[]), "not attempted")
    finally:
        pool.shutdown()
        result.running = []
    return done


# Worker observations kept per instance (prove_instance / NodeMonitor.info, WorkerDied).
_OBSERVED = ("pid", "started_at", "finished_at", "start_rss_mb", "peak_rss_mb", "end_rss_mb", "memory_budget_mb",
             "memory_exceeded")


def _record(result, node, status):
    diagnostic = result.diagnostics[node["spec"].pc]
    diagnostic["instances"] = [n for n in diagnostic["instances"] if n["spec"] != repr(node["spec"])]
    diagnostic["instances"].append(dict(spec=repr(node["spec"]), status=status, reasons=list(node["reasons"]),
                                        contexts=len(node.get("contexts", ())) or 1,
                                        seconds=node["seconds"], queries=node["queries"],
                                        failed_obligations=node["failed"],
                                        **({"proof_kind": node["proof_kind"]} if node.get("proof_kind") else {}),
                                        **({"chain_attempt": node["chain_attempt"]} if node.get("chain_attempt") else {}),
                                        **{k: node[k] for k in _OBSERVED if node.get(k) is not None}))
    if status == "split":
        diagnostic["instances"][-1]["split_contexts"] = [repr(c) for c in node.get("contexts", ())]
    # A split proof instance is superseded by its contexts' own entries.
    live = {n["spec"]: n for n in diagnostic["instances"] if n["status"] != "split"}
    splits = [n for n in diagnostic["instances"] if n["status"] == "split"]
    complete = (live and all(n["status"] == "proved" for n in live.values())
                and all(n.get("split_contexts") and all(live.get(c, {}).get("status") == "proved"
                                                       for c in n["split_contexts"]) for n in splits))
    diagnostic["status"] = "proved" if complete else "inconclusive"
