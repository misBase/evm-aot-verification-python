"""Base + full successor closure + finite worklist consumer for block lockstep.

Candidates are proposals. Only executed path formulas establish reachability and
closure. No persistent certificate cache and no partial-success aggregation.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from time import monotonic

from z3 import And, Not, Or, is_bv_value, is_int_value, is_false, sat, unsat, simplify

from verification.block_equivalence import (BlockEquivalenceProver, Obligation,
    _solver, digest, state_digest, paths_digest, host_model_axioms, obligation_manifest)
from verification.block_partition import split_at_cutpoints
from verification.block_relation import PLATFORM_SCOPE, platform_premises
from verification.block_specialization import BlockSpecialization, project, sensitive_slots, terminal_block
from verification.cutpoint_relation import read_evm_memory_word
from verification.loop_induction import (SegmentPath, run_evm_segment, run_x86_segment,
                                        terminal_observable_conditions)
from verification.program_verifier import GasCheck, _find_unsupported_dynamic_gas_ops
from tools.tag_align import build_block_alignment
from x86_64.cfg import identify_basic_blocks


@dataclass(frozen=True)
class EdgeCertificate:
    source: BlockSpecialization | None
    pair: tuple[int, int]
    target_pc: int
    targets: tuple[BlockSpecialization, ...]
    target_version: str
    identity: str
    obligation: Obligation
    # Stack constants assumed on the source's entry symbols (D_c of a context
    # proved through a weaker proof instance, block_parallel); () otherwise.
    assumed: tuple = ()


@dataclass(frozen=True)
class EntryCertificate:
    initial_digest: str
    raw_address: int
    evm_entry: int
    obligations: tuple[Obligation, ...]
    edges: tuple[EdgeCertificate, ...]
    path_digest: str
    path_count: int


@dataclass(frozen=True)
class ProgramCertificate:
    identity: str
    scope: str
    entry: EntryCertificate
    nodes: tuple
    edges: tuple[EdgeCertificate, ...]
    specializations: tuple[BlockSpecialization, ...]
    worklist_closed: bool

    def valid(self, prover, initial):
        """Single consumer used by API and CLI; counters/status are not evidence."""
        if getattr(prover, "_issued_program_certificate", None) is not self:
            return False
        current_identity = prover.identity
        if not self.worklist_closed or self.identity != current_identity or not self.scope:
            return False
        if self.entry is None or self.entry.initial_digest != state_digest(initial):
            return False
        enames = [o.name for o in self.entry.obligations]
        if (not {"init_nonempty", "evm_coverage", "x86_coverage"} <= set(enames)
                or not all(o.proved for o in self.entry.obligations)
                or len(self.entry.edges) != self.entry.path_count or self.entry.path_count < 1):
            return False
        specs = set(self.specializations)
        if not specs or len(specs) != len(self.specializations):
            return False
        if len(self.nodes) != len(specs) or {n.spec for n in self.nodes} != specs:
            return False
        expected = set()
        for node in self.nodes:
            if node._issuer is not prover or not node._proved_for_identity(current_identity):
                return False
            for i, e in enumerate(node.evm_outcomes):
                for j, x in enumerate(node.x86_outcomes):
                    if e.kind != "terminal" and x.kind != "terminal" and prover.pc_to_addr.get(e.location) == x.location:
                        expected.add((node.spec, (i, j)))
        if len(self.edges) != len(expected) or {(e.source, e.pair) for e in self.edges} != expected:
            return False
        if {e.pair for e in self.entry.edges} != {(0, j) for j in range(self.entry.path_count)}:
            return False
        for edge in (*self.edges, *self.entry.edges):
            if edge.source is None:
                if edge.target_pc != self.entry.evm_entry:
                    return False
            else:
                node = next(n for n in self.nodes if n.spec == edge.source)
                if edge.target_pc != node.evm_outcomes[edge.pair[0]].location:
                    return False
            registered = tuple(s for s in self.specializations if s.pc == edge.target_pc)
            if (edge.identity != self.identity or not edge.obligation.proved
                    or edge.targets != registered or edge.target_version != digest(registered)
                    or not set(edge.targets) <= specs):
                return False
        return True


@dataclass(frozen=True)
class IndependentProgramCertificate:
    """Complete finite execution from Init; no partial block theorem is consumed."""
    identity: str
    initial_digest: str
    obligations: tuple[Obligation, ...]
    required: tuple[str, ...]
    evm_outcomes: tuple
    x86_outcomes: tuple
    outcome_digest: str

    def valid(self, prover, initial):
        if getattr(prover, "_issued_program_certificate", None) is not self:
            return False
        names = tuple(o.name for o in self.obligations)
        return (self.identity == prover.identity and self.initial_digest == state_digest(initial)
                and bool(self.evm_outcomes) and bool(self.x86_outcomes)
                and all(p.kind == "terminal" for p in (*self.evm_outcomes, *self.x86_outcomes))
                and self.outcome_digest == paths_digest(self.evm_outcomes, self.x86_outcomes)
                and names == self.required and len(names) == len(set(names))
                and {"init_nonempty", "model_domain_nonempty", "evm_coverage", "x86_coverage"} <= set(names)
                and all(f"pair_{i}_{j}" in names for i in range(len(self.evm_outcomes))
                        for j in range(len(self.x86_outcomes)))
                and all(o.proved for o in self.obligations))


@dataclass
class BlockProgramResult:
    status: str = "inconclusive"
    reasons: tuple[str, ...] = ()
    certificate: ProgramCertificate | IndependentProgramCertificate | None = None
    nodes: tuple = ()
    queries: int = 0
    elapsed_seconds: float = 0
    scope: str = ""
    block_failure_reasons: tuple[str, ...] = ()
    timings: dict = field(default_factory=dict)
    diagnostics: dict = field(default_factory=dict)
    closure_checks: list = field(default_factory=list)
    _prover: object = field(default=None, repr=False)
    _initial: object = field(default=None, repr=False)
    _issued_scope: str = field(default="", repr=False)

    @property
    def verified(self):
        try:
            return (self.status == "verified" and not self.reasons and self.certificate is not None
                    and bool(self.scope) and self.scope == self._issued_scope
                    and self.certificate.valid(self._prover, self._initial))
        except Exception:
            return False

    @property
    def message(self):
        if self.verified:
            if isinstance(self.certificate, IndependentProgramCertificate):
                return "VERIFIED: independent full-program rerun certificate (no block results reused). " + self.scope
            return f"VERIFIED: closed block lockstep certificate ({len(self.nodes)} instances). {self.scope}"
        return "INCONCLUSIVE: " + "; ".join(self.reasons or ("incomplete certificate graph",)) + ". " + self.scope


def pushed_code_addresses(blocks):
    """PUSH immediates that are jump destinations: code addresses used as data.

    Static jumps carry their target in the JUMP/JUMPI itself, so a pushed
    JUMPDEST is a return address or a function pointer. A dynamic JUMP whose
    IR immediate_set is empty (Go left it to the jump table) contributes no
    return tags, so its return addresses look like plain constants: discovery
    widens them away and the return JUMP then forks to every JUMPDEST of the
    complete jump domain (DABEManager: 13 such JUMPs, ~626 successors per
    widened return context). A literal that merely equals a JUMPDEST is kept
    too; that only makes a context more specific.
    """
    jumpdests = {b.pc for b in blocks if b.is_jump_target}
    return {op.immediate for b in blocks for op in b.operations
            if op.kind.upper() == "PUSH" and op.immediate in jumpdests}


class BlockProgramVerifier:
    def __init__(self, *, gas_check=GasCheck.FIXED_BUDGET, timeout_ms=30_000,
                 max_depth=400, max_instances=2048, max_values_per_edge=32,
                 wall_timeout_seconds=300, schema=None, fallback="none", summary_config=None, progress_callback=None, node_timeout_seconds=60,
                 max_parameter_values=8, first_pass_node_seconds=None, pushed_code_return_tags=False,
                 terminal_constant_projection=False, context_constant_projection=False):
        self.gas_check = GasCheck(gas_check)
        self.timeout_ms = timeout_ms
        self.max_depth = max_depth
        self.max_instances = max_instances
        self.max_values_per_edge = max_values_per_edge
        self.wall_timeout_seconds = wall_timeout_seconds
        self.schema = schema
        if fallback not in ("none", "full-program"):
            raise ValueError("fallback must be none or full-program")
        self.fallback = fallback
        self.summary_config = summary_config
        self.progress_callback = progress_callback
        self.node_timeout_seconds = node_timeout_seconds
        if max_parameter_values < 1:
            raise ValueError("max_parameter_values must be positive")
        self.max_parameter_values = max_parameter_values
        if first_pass_node_seconds is not None and first_pass_node_seconds <= 0:
            raise ValueError("first_pass_node_seconds must be positive")
        self.first_pass_node_seconds = first_pass_node_seconds
        # Opt-in proposal hint (_setup): also keep pushed code addresses as return tags.
        self.pushed_code_return_tags = bool(pushed_code_return_tags)
        # Opt-in proposal hint (_discover): a terminal-only block's context
        # keeps only the constants the block consumes.
        self.terminal_constant_projection = bool(terminal_constant_projection)
        # Opt-in proposal hint (_discover): every context keeps its return tags
        # and only the other constants the block consumes. Without pushed code
        # addresses as return tags it would drop return addresses of JUMPs
        # lacking an immediate_set and fork them over the whole jump domain.
        if context_constant_projection and not pushed_code_return_tags:
            raise ValueError("context_constant_projection requires pushed_code_return_tags")
        self.context_constant_projection = bool(context_constant_projection)
        self._terminal_slots, self._block_slots = {}, {}
        self._constant_domains = {}

    def verify_program_pair(self, evm_program, x86_program, initial_state, *, candidates=None):
        """Return structured evidence. Explicit candidates never imply closure.

        With candidates=None enumerate stack depths and generalize changing m/f
        parameters. Nodes are accepted only after full relational H0/H2 queries.
        Failed nodes are collected; unexplored descendants remain unvisited.
        """
        start = monotonic()
        self._discovery_queries = 0
        self._discovery_cache = {}
        self._parameter_domains = {}
        self._constant_domains = {}
        result = BlockProgramResult()
        nodes, records = {}, []
        result._model_validated = False
        try:
            evm = sorted(evm_program.blocks, key=lambda b: b.pc)
            setup = self._setup(evm_program, x86_program, initial_state, result, start, records)
            initial, prover, alignment, identity = setup.initial, setup.prover, setup.alignment, setup.identity
            premise, epc, raw = setup.premise, setup.epc, setup.raw
            entry_evm, entry_x86, phase_start = setup.entry_evm, setup.entry_x86, setup.phase_start
            result.diagnostics = {b.pc: {"status": "unvisited", "instances": []} for b in evm}
            registered = set()
            queue = []
            pending = []  # source, pair, target pc, states, joint, snapshot

            def budget():
                if monotonic() - start >= self.wall_timeout_seconds:
                    raise ValueError("program worklist wall budget exhausted")

            def propose(source, pair, pc, e, x, joint, snapshot):
                budget()
                pending.append((source, pair, pc, e, x, joint, snapshot))
                if pc not in alignment.pc_to_addr:
                    raise ValueError(f"actual successor pc={pc} is unmapped")
                if candidates is None:
                    values = self._discover(pc, e, joint, budget)
                else:
                    values = tuple(candidates.get(pc, ()))
                    if any(s.pc != pc for s in values):
                        raise ValueError("candidate registered under the wrong block")
                for spec in values:
                    if spec not in registered:
                        if len(registered) >= self.max_instances:
                            raise ValueError("specialization worklist instance budget exhausted")
                        registered.add(spec)
                        queue.append(spec)
                        if not result.diagnostics[pc]["instances"]:
                            result.diagnostics[pc]["status"] = "queued"
                # H0/H2 below checks every pending edge against the frozen
                # target set. A speculative query here duplicates that work.

            for j, p in enumerate(entry_x86):
                propose(None, (0, j), epc, initial, p.state, And(premise, p.condition), None)
            result.timings["entry_execution_and_candidates"] = monotonic() - phase_start
            phase_start = monotonic()
            # Scheduling only; the certificate still needs every node proved and
            # every H0/H2 edge closed. (A) successors are discovered from any
            # node whose segments were executed, proved or not, so one run
            # reaches every block. (B) with first_pass_node_seconds, a node that
            # runs out of budget or gets `unknown` is retried once with the full
            # budget after the queue drains, so hard nodes do not stall it.
            full_budget = prover.node_timeout_seconds
            first_pass = self.first_pass_node_seconds
            deferred, retried, expanded = [], set(), set()
            cursor = 0
            while cursor < len(queue) or deferred:
                budget()
                if cursor >= len(queue):
                    queue.extend(deferred)
                    deferred.clear()
                spec = queue[cursor]
                cursor += 1
                prover.node_timeout_seconds = (full_budget if first_pass is None or spec in retried
                                               else min(first_pass, full_budget))
                node = prover.prove(spec)
                nodes[spec] = node
                node_proved = node.proved
                defer = (not node_proved and first_pass is not None and spec not in retried
                         and first_pass < full_budget and not any("solver=sat" in r for r in node.reasons))
                diagnostic = result.diagnostics[spec.pc]
                diagnostic["instances"] = [n for n in diagnostic["instances"] if n["spec"] != repr(spec)]
                diagnostic["instances"].append(dict(spec=repr(spec), status="deferred" if defer else node.status,
                    reasons=list(node.reasons), seconds=node.elapsed_seconds, queries=node.queries,
                    failed_obligations=[dict(name=o.name, answer=o.answer, expected=o.expected,
                        seconds=o.elapsed_seconds) for o in node.obligations if not o.proved]))
                diagnostic["status"] = ("inconclusive" if any(
                    n["status"] != "proved" for n in diagnostic["instances"]) else "proved")
                if defer:
                    deferred.append(spec)
                    retried.add(spec)
                elif not node_proved:
                    result.reasons += (f"local pc={spec.pc} {spec}: {'; '.join(node.reasons)}",)
                result.nodes = tuple(nodes.values())
                result.timings["local_theorems_and_discovery"] = monotonic() - phase_start
                if self.progress_callback is not None:
                    self.progress_callback(result)
                if spec in expanded or node.premise is None or node.context is None or not node.evm_outcomes:
                    continue
                expanded.add(spec)
                for i, e in enumerate(node.evm_outcomes):
                    for j, x in enumerate(node.x86_outcomes):
                        if e.kind != "terminal" and x.kind != "terminal" and alignment.pc_to_addr.get(e.location) == x.location:
                            try:
                                propose(spec, (i, j), e.location, e.state, x.state,
                                        And(node.premise, e.condition, x.condition),
                                        node.context.memory_snapshot)
                            except Exception as exc:
                                result.reasons += (f"successor pc={e.location}: {exc}",)
            # Freeze the finite relation set, then establish H0/H2 against that
            # exact version. Cyclic references are to relations, never to assumed
            # correctness of another local theorem.
            ordered = tuple(sorted(registered, key=lambda s: (s.pc, s.stack_depth, -1 if s.memory_size is None else s.memory_size, -1 if s.free_memory_pointer is None else s.free_memory_pointer, s.stack_constants)))
            result.timings["local_theorems_and_discovery"] = monotonic() - phase_start
            phase_start = monotonic()
            edges, entry_edges = [], []
            for source, pair, pc, e, x, joint, snapshot in pending:
                budget()
                targets = tuple(s for s in ordered if s.pc == pc)
                name = f"{'H0' if source is None else 'H2'}_{len(edges) + len(entry_edges)}"
                try:
                    goal = Or(*(And(*(g.condition for g in prover.schema.relation_goals(
                        e, x, s, memory_snapshot=snapshot))) for s in targets))
                except Exception as exc:
                    result.reasons += (f"{name} relation construction at pc={pc}: {exc}",)
                    result.closure_checks.append(dict(phase="final", source=repr(source),
                        pair=pair, target_pc=pc, answer="construction_error"))
                    continue
                edge_records = []
                if not prover._check(name, And(joint, Not(goal)), edge_records):
                    result.reasons += (f"{name} full successor relation not closed into pc={pc} (solver={edge_records[-1].answer})",)
                records.extend(edge_records)
                result.closure_checks.append(dict(phase="final", source=repr(source),
                    pair=pair, target_pc=pc, answer=edge_records[0].answer))
                certificate = EdgeCertificate(source, pair, pc, targets, digest(targets), identity, edge_records[0])
                (entry_edges if source is None else edges).append(certificate)
            entry = EntryCertificate(state_digest(initial), raw, epc,
                tuple(o for o in records if not o.name.startswith(("H0_", "H2_"))),
                tuple(entry_edges), paths_digest([entry_evm], entry_x86), len(entry_x86))
            result.nodes = tuple(nodes.values())
            result.timings["H0_H2_closure"] = monotonic() - phase_start
            if result.reasons:
                raise ValueError("certificate withheld: unresolved local or closure obligations")
            result.certificate = ProgramCertificate(identity, result.scope, entry, result.nodes,
                                                    tuple(edges), ordered, True)
            prover._issued_program_certificate = result.certificate
            if not result.certificate.valid(prover, initial):
                raise ValueError("global certificate consumer rejected incomplete dependencies")
            result.status = "verified"
        except Exception as exc:
            result.reasons += (f"{type(exc).__name__}: {exc}",)
            if self.fallback == "full-program" and result._model_validated:
                result.block_failure_reasons = result.reasons
                try:
                    self._independent_rerun(evm, x86_program, result._validated_initial, result)
                    result.reasons = ()
                    result.status = "verified"
                except Exception as fallback_exc:
                    result.reasons += (f"independent rerun: {type(fallback_exc).__name__}: {fallback_exc}",)
        result.nodes = tuple(nodes.values())
        result.queries = len(records) + sum(n.queries for n in result.nodes) + self._discovery_queries + result.queries
        result.elapsed_seconds = monotonic() - start
        return result

    def _setup(self, evm_program, x86_program, initial_state, result, start, records):
        """Validate the model, build the prover and run the raw entry adapter.

        Shared by the worklist above and the discover-first parallel schedule
        (verification/block_parallel.py), so both start from the same initial
        domain, prover and entry paths. `model_validated` is set on `result`
        as soon as the model checks pass, so a later failure (alignment) can
        still take the full-program fallback.
        """
        from types import SimpleNamespace
        self._discovery_queries = 0
        self._discovery_cache = {}
        self._parameter_domains = {}
        self._constant_domains = {}
        result._model_validated = False
        if min(self.max_instances, self.max_values_per_edge, self.wall_timeout_seconds) <= 0:
            raise ValueError("positive worklist and time budgets required")
        evm = sorted(evm_program.blocks, key=lambda b: b.pc)
        # Untrusted hints only: retaining a literal return address proposes
        # a predicate that must be established by actual H0/H2 states.
        self._return_tags = {target for b in evm for op in b.operations
                             for target in (op.immediate_set or ())}
        if self.pushed_code_return_tags:
            self._return_tags |= pushed_code_addresses(evm)
        self._terminal_slots = ({b.pc: sensitive_slots(b) for b in evm if terminal_block(b)}
                                if self.terminal_constant_projection else {})
        self._block_slots = ({b.pc: sensitive_slots(b) for b in evm}
                             if self.context_constant_projection else {})
        if not evm or not x86_program.instructions:
            raise ValueError("empty program")
        for b in evm:
            if b.static_gas and not any(op.kind.upper() == "TAG" for op in b.operations):
                raise ValueError(f"pc={b.pc}: static gas without TAG")
        if self.gas_check != GasCheck.OFF:
            unsupported = _find_unsupported_dynamic_gas_ops(evm_program)
            if unsupported:
                raise ValueError(f"unsupported dynamic gas: {unsupported}")
        # Copy once, then give independent copies to each executor. The
        # original user object is never overwritten with havoc or new assumptions.
        initial = initial_state.copy()
        initial.complete_jump_domain = True
        for condition in platform_premises(initial):
            initial.add_assumption(condition)
        if initial.abstract_calldataload_words or initial.assume_calldata_offset_no_overflow:
            raise ValueError("block mode requires exact calldata with no no-overflow assumption")
        if initial.unrouted_memory_domain is not None:
            raise ValueError("unrouted memory fallback is not a production model")
        gas = simplify(initial.evm_gas.Gas)
        if not gas.eq(simplify(initial.callengine_gas_remaining)):
            raise ValueError("initial gas mismatch")
        if (self.gas_check == GasCheck.FULL) == is_bv_value(gas):
            raise ValueError("initial gas is inconsistent with the requested gas mode")
        if initial.host_gas_uf_enabled != (self.gas_check != GasCheck.OFF):
            raise ValueError("host gas setting differs from requested gas mode")
        result._model_validated, result._validated_initial = True, initial
        result.scope = (
            f"model=GO_HPC_EVM_PROFILE, exact calldata, full jump-destination domain, summaries={'per-hit raw proof' if self.summary_config else 'off'}; gas={self.gas_check.value}"
            + (f", initial_budget={gas.as_long()}" if is_bv_value(gas) else ", symbolic initial gas")
            + "; terminal status, return metadata/bytes, storage, transient storage"
            + (", remaining gas" if self.gas_check != GasCheck.OFF else
               "; reduced host-cost model: no real-gas/OOG equivalence claim")
            + "; finite segment matching and termination correspondence within the model; host calls use bounded-cost atomic UFs where declared, and host-internal exhaustion/termination is outside the claim"
            + "; " + PLATFORM_SCOPE + "."
        )
        result._issued_scope = result.scope
        bb = identify_basic_blocks(x86_program.instructions)
        alignment = build_block_alignment(evm, x86_program.instructions, bb)
        bb = split_at_cutpoints(bb, alignment.pc_to_addr.values())
        prover = BlockEquivalenceProver(evm, bb, alignment.pc_to_addr, self.schema,
            timeout_ms=self.timeout_ms, max_depth=self.max_depth,
            compare_gas=self.gas_check != GasCheck.OFF,
            host_gas_uf_enabled=initial.host_gas_uf_enabled, summary_config=self.summary_config,
            deadline=start + self.wall_timeout_seconds, node_timeout_seconds=self.node_timeout_seconds)
        prover.validate()
        result._prover, result._initial = prover, initial
        identity = prover.identity
        result.timings["analysis_and_setup"] = monotonic() - start
        phase_start = monotonic()
        premise = And(*(initial.assumptions or []))
        if not prover._check("init_nonempty", premise, records, expected="sat"):
            raise ValueError("initial domain empty or unknown")
        epc, raw = evm[0].pc, x86_program.instructions[0].addr
        entry_evm = SegmentPath("exit", epc, premise, initial.copy())
        if raw == alignment.pc_to_addr[epc]:
            entry_x86 = [SegmentPath("exit", raw, premise, initial.copy())]
        else:
            entry_x86, defects, _ = run_x86_segment(
                bb, initial.copy(), raw, set(alignment.pc_to_addr.values()),
                max_depth=self.max_depth, use_reachability_check=True,
                deadline=start + self.wall_timeout_seconds,
                call_site_mapping=prover.call_site_mapping)
            if defects:
                raise ValueError("entry adapter coverage: " + "; ".join(defects))
        prover.check_paths([entry_evm], entry_x86, premise, initial, records)
        # Raw prologue may only hand off to the first TAG; an early terminal
        # is a Continue/Terminal mismatch against the EVM initial boundary.
        for p in entry_x86:
            if p.kind == "terminal" or p.location != alignment.pc_to_addr[epc]:
                raise ValueError("raw entry adapter does not reach the first pre-TAG boundary")
        return SimpleNamespace(evm=evm, initial=initial, prover=prover, alignment=alignment, identity=identity,
                               premise=premise, epc=epc, raw=raw, entry_evm=entry_evm, entry_x86=entry_x86,
                               phase_start=phase_start, model_validated=True)

    def _independent_rerun(self, evm, x86_program, initial, result):
        # Fresh executors, fresh formulas, ORIGINAL initial state, empty stop
        # sets. Even an alignment failure can fall back; no alignment premise
        # is used by this independent proof.
        prover = BlockEquivalenceProver(
            evm, identify_basic_blocks(x86_program.instructions), {}, self.schema,
            timeout_ms=self.timeout_ms, max_depth=self.max_depth,
            compare_gas=self.gas_check != GasCheck.OFF,
            host_gas_uf_enabled=initial.host_gas_uf_enabled,
            deadline=monotonic() + self.wall_timeout_seconds)
        records = []
        from verification.call_site_mapping import build_call_site_mapping_from_blocks
        prover.call_site_mapping = build_call_site_mapping_from_blocks(
            evm, prover.x86_blocks, aot_profile=prover.aot_profile)
        premise = And(*(initial.assumptions or []))
        if not prover._check("init_nonempty", premise, records, expected="sat"):
            raise ValueError("empty or unknown initial domain")
        evm_paths, ed = run_evm_segment(evm, initial.copy(), evm[0].pc, set(), max_depth=self.max_depth)
        x86_paths, xd, _ = run_x86_segment(
            prover.x86_blocks, initial.copy(), x86_program.instructions[0].addr, set(),
            max_depth=self.max_depth, use_reachability_check=True, deadline=prover.deadline,
            call_site_mapping=prover.call_site_mapping)
        if ed or xd:
            raise ValueError("finite execution incomplete: " + "; ".join((*ed, *xd)))
        if any(p.kind != "terminal" for p in (*evm_paths, *x86_paths)):
            raise ValueError("independent execution left a nonterminal outcome")
        premise = And(premise, *host_model_axioms([premise, *(p.condition for p in (*evm_paths, *x86_paths))]))
        if not prover._check("model_domain_nonempty", premise, records, expected="sat"):
            raise ValueError("oracle model domain empty or unknown")
        prover.check_paths(evm_paths, x86_paths, premise, initial, records)
        for i, e in enumerate(evm_paths):
            for j, x in enumerate(x86_paths):
                goal = And(*terminal_observable_conditions(e.state, x.state,
                            initial.evm_memory.Memory, prover.compare_gas))
                if not prover._check(f"pair_{i}_{j}", And(premise, e.condition, x.condition, Not(goal)), records):
                    raise ValueError(f"terminal mismatch pair_{i}_{j}")
        certificate = IndependentProgramCertificate(prover.identity, state_digest(initial),
            tuple(records), obligation_manifest(evm_paths, x86_paths, initial, block=False), tuple(evm_paths), tuple(x86_paths),
            paths_digest(evm_paths, x86_paths))
        prover._issued_program_certificate = certificate
        if not certificate.valid(prover, initial):
            raise ValueError("independent certificate consumer rejected evidence")
        result._prover, result._initial, result.certificate = prover, initial, certificate
        result.scope = result.scope.replace("summaries=per-hit raw proof", "summaries=off (independent rerun)")
        result._issued_scope = result.scope
        result.queries += len(records)

    def _discover(self, pc, state, joint, budget):
        """Enumerate only finite stack depths; widen changing memory parameters.

        Memory parameters and non-return constants each widen at most once per
        pc/depth/return-tag context. None denotes equality plus the schema domain, not a sampled
        model value. All proposals still require H0/H2 on both actual states.
        """
        expressions = (state.evm_stack.SP, state.evm_memory.MSize, read_evm_memory_word(state, 0x40))
        budget()
        joint = simplify(joint)
        if is_false(joint):
            return ()

        def proposal(depth):
            parameters = tuple(v.as_long() if is_bv_value(v) else None
                               for v in map(simplify, expressions[1:]))
            constants = tuple((i, v.as_long()) for i in range(depth)
                if is_bv_value(v := simplify(state.evm_stack.peek(i))))
            returns = tuple(c for c in constants if c[1] in self._return_tags)
            extra = tuple(c for c in constants if c[1] not in self._return_tags)
            if pc in self._block_slots:
                # Before the widening check: a changing constant the block never
                # consumes no longer widens away the ones it does.
                extra = tuple(c for c in extra if c[0] in self._block_slots[pc])
            domain_key = (pc, depth, returns)
            # Retain literal buffer offsets too, but widen changing constants
            # once so an incrementing counter cannot create infinite instances.
            previous_extra = self._constant_domains.setdefault(domain_key, extra)
            if previous_extra != extra:
                self._constant_domains[domain_key] = None
                constants = returns
            else:
                constants = tuple(sorted((*returns, *extra)))
            # Keep up to max_parameter_values concrete (msize, fmp) per context
            # before widening to TOP: concrete values make every memory address
            # a constant, while TOP blocks carry symbolic aliasing (61% of the
            # CErc20 node time at 15% of instances, R15). Still finite per context.
            seen = self._parameter_domains.setdefault(domain_key, set())
            if seen is None:
                parameters = (None, None)
            elif parameters not in seen:
                if len(seen) >= self.max_parameter_values:
                    self._parameter_domains[domain_key] = None
                    parameters = (None, None)
                else:
                    seen.add(parameters)
            spec = BlockSpecialization(pc, depth, *parameters, constants)
            # Both projections register a weakening of the proposed context
            # (_block_slots: the extra constants filtered above): R_π(c) is weaker
            # than R_c, so every exit that met R_c meets it (premise weakening, as
            # for k = π(c)). A terminal-only block has no successor to propose
            # from its exits, so there nothing downstream changes either.
            if pc in self._terminal_slots:
                return project(spec, self._terminal_slots[pc])
            return spec

        depth = simplify(expressions[0])
        if is_int_value(depth):
            # An untrusted candidate needs no feasibility proof. Most raw
            # block exits already have a literal SP; H0/H2 below must still
            # establish the entire relation on BOTH actual successor states.
            return (proposal(depth.as_long()),)
        key = (pc, *(simplify(v).sexpr() for v in expressions),
               state.evm_stack.Stack.sexpr(), joint.sexpr())
        if key in self._discovery_cache:
            return self._discovery_cache[key]
        solver = _solver(self.timeout_ms)
        solver.add(joint)
        values = []
        while True:
            budget()
            answer = solver.check()
            self._discovery_queries += 1
            if answer == unsat:
                answer_values = tuple(values)
                self._discovery_cache[key] = answer_values
                return answer_values
            if answer != sat:
                raise ValueError(f"successor stack-depth enumeration unknown at pc={pc}")
            if len(values) >= self.max_values_per_edge:
                raise ValueError(f"stack-depth value budget at pc={pc}")
            depth = solver.model().eval(expressions[0], model_completion=True).as_long()
            values.append(proposal(depth))
            solver.add(expressions[0] != depth)
