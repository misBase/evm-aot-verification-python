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
cross processes, so the edge set and theorems are taken from the workers,
which run this same code on the same program (checked: every worker reports
the parent's portable identity).

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

import os
import pickle
import zlib  # obligation texts compress ~15x: R30 wrote 15GB for 1188 nodes uncompressed
import time
from concurrent.futures import FIRST_COMPLETED, ProcessPoolExecutor, wait
from dataclasses import dataclass, replace
from hashlib import sha256
from pathlib import Path
from time import monotonic

from z3 import Z3_OP_CONCAT, Z3_OP_UNINTERPRETED, And, Not, Or, is_app, is_eq, is_false, is_quantifier, simplify

from verification.block_equivalence import ProofBudgetExceeded, digest, paths_digest, state_digest
from verification.block_program import (BlockProgramResult, BlockProgramVerifier, EdgeCertificate,
                                        EntryCertificate)
from verification.block_relation import stack_constant_condition
from verification.block_specialization import PROJECTION_VERSION, dropped, project, sensitive_slots, weakens
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
                                      div="fallback", memgas="fallback") if options["summaries"] else None
    verifier = BlockProgramVerifier(gas_check=mode, timeout_ms=options["timeout_ms"], max_depth=options["max_depth"],
                                    max_instances=options["max_instances"], wall_timeout_seconds=options["wall_seconds"],
                                    summary_config=config, node_timeout_seconds=options["node_seconds"],
                                    max_parameter_values=options["max_parameter_values"],
                                    first_pass_node_seconds=options["first_pass_node_seconds"])
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
    targets = {}
    for spec in ordered:
        targets.setdefault(spec.pc, []).append(spec)
    _WORKER.update(setup=setup, targets={pc: tuple(v) for pc, v in targets.items()},
                   identity=setup.prover.portable_identity)


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
        out = slim(value)
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


def close_edge(prover, name, base, goals):
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
    """
    from verification.block_equivalence import (_QUICK_EXACT_MS, Obligation, _conjuncts, _generalize_products,
                                                refute_over_bv_abstraction, solve_query)
    from common.store_forwarding import forward_selects, join_extracts
    quick = min(_QUICK_EXACT_MS, prover.timeout_ms)
    forwarded, joined = {}, {}  # one cache per edge: the targets share the exit state's store chains
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

    for t, (spec, relation) in enumerate(goals):
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
                part = f"{name}_t{t}_{g.name}_{k}"
                started = monotonic()
                general = Not(_generalize_products(conjunct))
                if refute_over_bv_abstraction(general, quick)[1] == "unsat":
                    outcome[key] = [Obligation(part, general.sexpr(), "unsat", elapsed_seconds=monotonic() - started)]
                    parts.extend(outcome[key])
                    continue
                # A callEngine mirror goal reads [R13+off] back through the exit
                # state's byte stores: forwarded (exact) and rejoined (identity)
                # it is `field == field` (CErc20 10233 gas_remaining: 0.0s,
                # where every route with the premise stayed unknown).
                exact = Not(join_extracts(forward_selects(conjunct, forwarded), joined))
                if is_false(simplify(exact)):
                    outcome[key] = [Obligation(part, exact.sexpr(), "unsat", elapsed_seconds=monotonic() - started)]
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


def prove_instance(spec, node_seconds, deadline_epoch, contexts=None):
    """Worker task: the proof of `spec` (a proof instance k), then for every
    context c of k (default: k itself) its H2 edges into the frozen set, on
    k's exits under premise_k ∧ E_c."""
    contexts = (spec,) if contexts is None else tuple(contexts)
    setup = _WORKER["setup"]
    prover, identity = setup.prover, _WORKER["identity"]
    started = monotonic()
    prover.deadline = started + max(0.0, deadline_epoch - time.time())
    prover.node_timeout_seconds = node_seconds
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
        for i, e in enumerate(node.evm_outcomes):
            for j, x in enumerate(node.x86_outcomes):
                if not (e.kind != "terminal" and x.kind != "terminal"
                        and prover.pc_to_addr.get(e.location) == x.location):
                    continue
                expected.append((i, j))
                targets = _WORKER["targets"].get(e.location, ())
                try:
                    goals = [(s, prover.schema.relation_goals(e.state, x.state, s,
                                                             memory_snapshot=node.context.memory_snapshot))
                             for s in targets]
                    pairs.append((i, j, e, x, targets, goals))
                except Exception as exc:
                    reasons.append(f"H2 ({i},{j}) into pc={e.location}: {type(exc).__name__}: {exc}")
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
            try:
                # Not needed for soundness (an empty context has no entries); guards a wrong E_c.
                if assumed and not prover._check(f"context_nonempty_{tag}", base, [], expected="sat"):
                    reasons.append(f"context {c!r}: premise ∧ E_c empty or unknown")
                    continue
                for i, j, e, x, targets, goals in pairs:
                    record = close_edge(prover, f"H2_{tag}{i}_{j}", And(base, e.condition, x.condition), goals)
                    if not record.proved:
                        reasons.append(f"H2 {tag}({i},{j}) not closed into pc={e.location} (solver={record.answer})")
                    edges.append(EdgeCertificate(c, (i, j), e.location, targets, digest(targets), identity,
                                                 record, assumed))
            except ProofBudgetExceeded:
                # The context's H2 budget ran out: its edges are not closed (unknown), not a worker error.
                reasons.append(f"H2 {tag}budget exhausted (solver=unknown)")
        prover.deadline = program_deadline
    return dict(spec=spec, contexts=contexts, identity=identity, proved=proved, status=node.status,
                theorem=slim_theorem(node.theorem) if proved else None, expected=tuple(expected),
                edges=slim_theorem(tuple(edges)),
                reasons=tuple(reasons), seconds=monotonic() - started, queries=node.queries,
                failed=[dict(name=o.name, answer=o.answer, expected=o.expected, seconds=o.elapsed_seconds)
                        for o in node.obligations if not o.proved])


# ---------------------------------------------------------------- certificate

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
        exits = {}  # proof instance -> (outcome digest, expected pairs), shared by its contexts
        for node in self.nodes:
            theorem, spec, proof = node["theorem"], node["spec"], node.get("proof_spec")
            if (node["identity"] != self.identity or not node["proved"] or node["reasons"]
                    or theorem is None or proof is None or theorem.spec != proof
                    or not weakens(proof, spec) or not theorem.complete):
                return False
            if len(node["edges"]) != len(node["expected"]) or {e.pair for e in node["edges"]} != set(node["expected"]):
                return False
            shape = (theorem.outcome_digest, frozenset(node["expected"]))
            if exits.setdefault(proof, shape) != shape:
                return False
            assumed = dropped(proof, spec)
            for edge in node["edges"]:
                if (edge.source != spec or edge.assumed != assumed
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
                          store_tag=f"-{PROJECTION_VERSION}" if insensitive else "")
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


def _prove_all(stem, options, ordered, groups, identity, deadline_epoch, workers, pair_workers, results_dir,
               result, progress_callback, store_tag=""):
    """Prove every proof instance of `groups` ({k: contexts}, updated in place
    when a group is split); returns {k: worker result}."""
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
    pool = ProcessPoolExecutor(workers, mp_context=multiprocessing.get_context("spawn"),
                               initializer=_init_worker,
                               initargs=(str(stem), options, ordered, os.getpid(), pair_workers))
    try:
        running = {}

        def fill():
            # At most `workers` in flight so the schedule, not the pool's FIFO, picks the next one.
            while len(running) < workers and time.time() < deadline_epoch:
                spec, seconds = schedule.pop()
                if spec is None:
                    return
                running[pool.submit(prove_instance, spec, seconds, deadline_epoch, groups[spec])] = spec

        fill()
        while running:
            left = deadline_epoch + 60 - time.time()
            if left <= 0:
                break
            finished, _ = wait(running, timeout=min(left, 60), return_when=FIRST_COMPLETED)
            for future in finished:
                spec = running.pop(future)
                try:
                    node = future.result()
                except Exception as exc:
                    node = dict(spec=spec, contexts=groups[spec], identity=identity, proved=False, status="error",
                                theorem=None, expected=(), edges=(),
                                reasons=(f"worker: {type(exc).__name__}: {exc}",), seconds=0.0, queries=0, failed=[])
                out_of_wall = time.time() >= deadline_epoch
                if out_of_wall and not node["proved"]:
                    # Queued behind the program wall: never attempted, not a failed proof.
                    _record(result, node, "not attempted")
                    continue
                # An open H2 edge also earns the full-budget retry (it reproves the node too).
                retry = (final_status(node) != "proved" and spec not in schedule.full_start
                         and not any("solver=sat" in r for r in node["reasons"]))
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
                if progress_callback is not None:
                    progress_callback(result)
            fill()
        # Never submitted before the wall (queued, or blocked behind an unfinished leader).
        for spec in schedule.pending():
            _record(result, dict(spec=spec, reasons=(), seconds=0.0, queries=0, failed=[]), "not attempted")
    finally:
        for process in list(getattr(pool, "_processes", {}).values()):
            process.kill()
        pool.shutdown(wait=False, cancel_futures=True)
    return done


def _record(result, node, status):
    diagnostic = result.diagnostics[node["spec"].pc]
    diagnostic["instances"] = [n for n in diagnostic["instances"] if n["spec"] != repr(node["spec"])]
    diagnostic["instances"].append(dict(spec=repr(node["spec"]), status=status, reasons=list(node["reasons"]),
                                        contexts=len(node.get("contexts", ())) or 1,
                                        seconds=node["seconds"], queries=node["queries"],
                                        failed_obligations=node["failed"]))
    # A split proof instance is superseded by its contexts' own entries.
    diagnostic["status"] = ("inconclusive" if any(n["status"] not in ("proved", "split")
                                                  for n in diagnostic["instances"]) else "proved")
