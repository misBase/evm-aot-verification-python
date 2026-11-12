"""Instruction-chain block producer (proof kind ``instruction-chain/1``).

A block's local theorem as a finite chain of per-EVM-operation lemmas instead of one whole-block path-pair
comparison. For op k with EVM stack height h_k and a location table L_k (where each 64-bit limb of each in-block
EVM stack slot lives on the x86 side: its home slot [R14 + 32((h-d0)-1-i) + 8l], a register or a constant), the
lemma is: from every pair state satisfying R_k, op k on the EVM side and the x86 code from start_k reach end_k
with R_{k+1} on every continuing path, or both sides stop with matching terminal observations. Op 0 starts from
the block-entry relation (every limb home, the pre-TAG R14). The last op (JUMP/JUMPI/terminal) proves the
successor's block-boundary relation at every successor entry, paired by x86 address == pc_to_addr[successor].
The theorem's x86 outcome classes are the EVM outcome classes (observational quotient): pair_i_i, x86_maps_i_0
and x86_coverage are derived from the leaves, not separate solver calls; H2 is completed per edge by (a) the
EVM exit satisfies some frozen target's specialisation and a lift (the unspecialised relation plus that
specialisation implies the target's full relation).

Trust boundary. The per-op hint (x86 intervals and compile-time location tables, e.g. a diagnostic codegen trace)
is untrusted: it only chooses which statements are proved. Every lemma is proved in full and the chain is checked
here (complete unique indices, op 0 at the real entry with every limb home, (end_k, L_after_k) ==
(start_{k+1}, L_before_{k+1})). A wrong hint makes a lemma or the chain fail, never a proof succeed. The hints'
digest is part of the prover's portable identity.

Entry tags. The block-boundary relation does not constrain register pointer tags, while op 0's generic state
fixes them. entry_tags_dead checks on the executor's own blocks that no tag-routed memory access can observe a tag
present at block entry (tag-origin dataflow; unknown transfers keep every origin; a ret follows the executor: a
CallGoFunction bridge resumes at its statically determined saved return address with every tag kept, any other
ret is terminal), so the lemmas hold whatever the entry tags are. A block failing it is left to the legacy prover.

Payload trust. As for the legacy producer (block_parallel's trust boundary), the node results a worker returns and
the results directory caches are trusted payload: the consumer's registry check (block_parallel._producer_ok)
binds a theorem to the loaded hint, the real entry and the depth, and complete() checks its derivation structure,
but neither re-proves or authenticates the leaves themselves.
"""
from __future__ import annotations

import json
from bisect import bisect_left
from dataclasses import dataclass, replace
from hashlib import sha256
from pathlib import Path
from time import monotonic
from types import SimpleNamespace

from z3 import And, BitVec, BitVecVal, Extract, Not, Or, is_false, simplify

PROOF_KIND = "instruction-chain/1"
OP_TIMEOUT_MS = 20_000
ROUTE_SECONDS = 600.0
MAX_STEPS = 900
MACRO_KINDS = ("copy_loop", "memgas", "mul", "div", "sdiv", "smod")
_REG = {"AX": "RAX", "BX": "RBX", "CX": "RCX", "DX": "RDX", "SI": "RSI", "DI": "RDI", "BP": "RBP", "SP": "RSP"}
LOAD_BASE = 0x1000  # X86Program base address; hint addresses are absolute
# shortcut: fixed cap on a chain attempt in the full-budget retry (the slowest measured chain, Pool 7200, took 4621 s);
# make it an option if a block needs longer.
CHAIN_SECONDS = 7200.0


# ---------------------------------------------------------------- hints

@dataclass(frozen=True)
class OpHint:
    index: int
    opcode: str
    start: int
    end: int
    before: tuple  # ((limb index from R14, word index from R14, limb in word, kind, register, value), ...)
    after: tuple


@dataclass(frozen=True)
class BlockHint:
    pc: int
    code_sha256: str
    ops: tuple
    digest: str


def _entry(e):
    return (int(e["index"]), int(e["word_index_from_r14"]), int(e["limb_in_word"]), e["kind"], e.get("register"),
            int(e.get("value", 0) or 0))


def _full_trace_hints(data, want):
    """{pc: BlockHint} from a whole-program codegen trace ({"hex": code, "rows": [...]}, one row per IR operation in
    emission order, each with its block pc, opcode, x86 [start, end) and the compiler's location window before and
    after as limb entries {index, kind, register, value}), for every block. {} if made for other code."""
    if sha256(bytes.fromhex(data["hex"])).hexdigest() != want:
        return {}
    by_block = {}
    for row in data["rows"]:
        by_block.setdefault(int(row["block"]), []).append(row)

    def entry(e):
        index = int(e["index"])
        return (index, index // 4, index % 4, e["kind"], e.get("register"), int(e.get("value", 0) or 0))
    hints = {}
    for pc, rows in by_block.items():
        ops = tuple(OpHint(k, r["opcode"], int(r["start"]), int(r["end"]), tuple(entry(e) for e in r["before"] or ()),
                           tuple(entry(e) for e in r["after"] or ())) for k, r in enumerate(rows))
        hints[pc] = BlockHint(pc, want, ops, sha256(repr((pc, want, ops)).encode()).hexdigest())
    return hints


def load_hints(source, code: bytes):
    """{pc: BlockHint} for exactly this code (sha256 of the code bytes, load base 0x1000). `source` is either a
    whole-program codegen trace file (every block gets a hint: _full_trace_hints) or a directory of per-block traces
    ({pc, code_sha256, instructions}); files made for other code are ignored. Duplicate indices or two traces for
    one pc raise."""
    want, hints = sha256(code).hexdigest(), {}
    if Path(source).is_file():
        return _full_trace_hints(json.loads(Path(source).read_text()), want)
    for path in sorted(Path(source).glob("*.json")):
        data = json.loads(path.read_text())
        if not isinstance(data, dict) or data.get("code_sha256") != want or "instructions" not in data:
            continue
        if int(str(data.get("code_load_base", LOAD_BASE)), 0) != LOAD_BASE:
            continue
        rows = sorted(data["instructions"], key=lambda r: r["instruction_index"])
        indices = [r["instruction_index"] for r in rows]
        if len(indices) != len(set(indices)):
            raise ValueError(f"{path.name}: duplicate instruction indices")
        pc = int(data["pc"])
        if pc in hints:
            raise ValueError(f"two hints for pc={pc}")
        ops = tuple(OpHint(int(r["instruction_index"]), r["opcode"], int(r["start"]), int(r["end"]),
                           tuple(_entry(e) for e in r["before"]), tuple(_entry(e) for e in r["after"])) for r in rows)
        hints[pc] = BlockHint(pc, want, ops, sha256(repr((pc, want, ops)).encode()).hexdigest())
    return hints


def hints_digest(hints):
    return sha256(repr(sorted((pc, h.digest) for pc, h in hints.items())).encode()).hexdigest() if hints else None


def attach_hints(prover, options, stem):
    """Load options["instruction_hints"] for this program onto the prover (before its identity is read)."""
    directory = options.get("instruction_hints")
    if not directory:
        prover.instruction_hints, prover.instruction_hints_digest = {}, None
        return
    code = bytes.fromhex(Path(str(stem) + ".hex").read_text().strip())
    prover.instruction_hints = load_hints(directory, code)
    prover.instruction_hints_digest = hints_digest(prover.instruction_hints)


def height(entries, d0):
    return d0 + (max(e[0] for e in entries) + 1) // 4 if entries else d0


def locations(entries, h, d0):
    """Hint entries -> per-slot (from the top) limb locations at height h; unmentioned limbs are home."""
    from x86_64.models import Register
    locs = [[("s",)] * 4 for _ in range(h)]
    for _, word, l, kind, register, value in entries:
        i = (h - d0) - 1 - word
        if not 0 <= i < h:
            continue
        if kind == "register":
            locs[i][l] = ("r", Register[_REG.get(register, register)])
        elif kind == "constant":
            locs[i][l] = ("c", value)
        else:
            locs[i][l] = ("s",)
    return tuple(tuple(slot) for slot in locs)


def block_range(prover, pc):
    entry = prover.pc_to_addr[pc]
    later = [a for a in prover.pc_to_addr.values() if a > entry]
    return entry, (min(later) if later else max(b.end_addr for b in prover.x86_blocks))


def chain_problems(block, hint, d0, entry_addr, block_pcs=(), heights=None):
    """Structural reasons the hint's chain cannot compose (empty: it can). Besides the hint's own chain, the block
    must have the shape the per-op lemmas rely on: one TAG, as op 0 (its lemma runs the block's real gas and stack
    guards; every later op runs without them), and, for a block of more than one op, a last op pc strictly above
    block.pc with no other block's pc in (block.pc, last op pc]: the exit lemma starts a stand-in block at the last
    op's pc, which must sort right after this block, neither replace a real block (this one included: it would
    lose is_jump_target) nor change the fallthrough. A single-op block's exit runs the real block itself.
    `block_pcs`: the pcs of all EVM blocks; `heights`: semantic_plan's (None: the location tables are not compared,
    structural checks only)."""
    ops, n = hint.ops, len(block.operations)
    if tuple(o.index for o in ops) != tuple(range(n)):
        return ["hint does not cover ops 0..n-1 exactly once"]
    problems = [f"op {o.index}: hint opcode {o.opcode} != {op.kind}" for o, op in zip(ops, block.operations)
                if o.opcode != op.kind]
    kinds = [op.kind for op in block.operations]
    if kinds[0] != "TAG" or "TAG" in kinds[1:]:
        problems.append("the block is not in TAG normal form (one TAG, as op 0)")
    last = block.operations[-1].pc
    if n > 1 and (last <= block.pc or any(block.pc < pc <= last for pc in block_pcs)):
        problems.append("the exit stand-in at the last op's pc would not sort right after this block "
                        "(last pc not above the block pc, or another block's pc lies in between)")
    if ops[0].start != entry_addr:
        problems.append("op 0 does not start at the block entry")
    if any(loc != ("s",) for slot in locations(ops[0].before, d0, d0) for loc in slot):
        problems.append("op 0 does not start from the block-entry relation")
    for k, (a, b) in enumerate(zip(ops, ops[1:])):
        if a.end < a.start or a.end != b.start:
            problems.append(f"chain break after op {a.index}")
        elif heights is not None and locations(a.after, heights[k + 1], d0) != locations(b.before, heights[k + 1], d0):
            problems.append(f"location tables differ after op {a.index}")
    return problems


def semantic_plan(prover, block, d0, entry_facts=()):
    """(heights, facts, problem): the EVM stack height and the known stack constants before each op, from the EVM
    model itself. Each op runs alone on a generic state of the previous height whose known slots are pinned to their
    constants; its continuing paths must agree on the next height, and a slot whose value simplifies to the same
    constant on all of them is a fact at the next boundary (a PUSH's immediate, a passed-through return address, a
    constant folded from constants). The hint's location window cannot tell the height once it is empty below the
    entry depth. Facts only choose lemma statements: each lemma proves the facts it states at its end, so a wrong
    one makes a lemma fail. problem names an op the plan cannot run (no chain; the legacy prover takes the block)."""
    from z3 import is_bv_value
    from evm_ir.models import GO_MAX_INT64, EVMBlock
    from verification.loop_induction import run_evm_segment
    ops, heights, facts = block.operations, [d0], [tuple(sorted(entry_facts))]
    for k in range(len(ops) - 1):
        op, h = ops[k], heights[-1]
        nxt = ops[k + 1].pc if ops[k + 1].pc > op.pc else op.pc + 1
        first = EVMBlock(op.pc, 0, 0, GO_MAX_INT64, 0, False, True, False, [op])  # no TAG accounting: plan only
        tail = EVMBlock(nxt, 0, 0, GO_MAX_INT64, 0, False, True, False, [])
        try:
            state = prover.schema.build_havoc(h, prefix=f"ich{block.pc}_{k}",
                                              host_gas_uf_enabled=prover.host_gas_uf_enabled,
                                              abstract_calldataload_words=False,
                                              assume_calldata_offset_no_overflow=False,
                                              stack_constants=facts[-1]).state
            paths, defects = run_evm_segment([first, tail], state, op.pc, {nxt}, max_depth=10)
            cont = [p.state for p in paths if p.kind != "terminal"]
            after = {simplify(s.evm_stack.SP).as_long() for s in cont}
            if defects or len(after) != 1:
                return heights, facts, (f"op {k}: no single continuing EVM stack height ({sorted(after)}, "
                                        f"defects={defects})")
            h = after.pop()
            if h < 0:  # the plan runs without the TAG's depth guard (e.g. a guarded underflow at a shallow entry)
                return heights, facts, f"op {k}: negative EVM stack height {h} (the block's depth guard stops it)"
            known = None
            for s in cont:
                values = {}
                for i in range(h):
                    v = simplify(s.evm_stack.peek(i))
                    if is_bv_value(v):
                        values[i] = v.as_long()
                known = values if known is None else {i: v for i, v in known.items() if values.get(i) == v}
        except Exception as exc:  # noqa: BLE001 - an op the plan cannot run: no chain, the legacy prover takes it
            return heights, facts, f"op {k}: plan failed: {type(exc).__name__}: {exc}"[:300]
        heights.append(h)
        facts.append(tuple(sorted(known.items())))
    return heights, facts, None


def r15_tags(x86_blocks, hint):
    """R15's pointer tag at each boundary k: at the block entry (k = 0) the state's own (None: as built); after it
    NONE until an op reloads R15 from [r13+0x10], EVM_PTR afterwards. Every boundary k >= 1 is explicit, so each
    lemma checks its end tag on every continuing path: a wrong prediction blocks, it never disables the check."""
    insns = sorted((i.addr, i) for b in x86_blocks for i in b.instructions)
    addrs = [a for a, _ in insns]
    tags, tag = {0: None}, "NONE"
    for o in hint.ops:
        for a, i in insns[bisect_left(addrs, o.start):bisect_left(addrs, o.end)]:
            if i.mnemonic == "mov" and i.op_str.replace(" ", "") == "r15,qwordptr[r13+0x10]":
                tag = "EVM_PTR"
        tags[o.index + 1] = tag
    return tags


# ---------------------------------------------------------------- entry tags

_GPRS = ("rax", "rbx", "rcx", "rdx", "rsi", "rdi", "rbp", "rsp", "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15")
_ALIASES = {a: r for r, names in {"rax": "eax ax al ah", "rbx": "ebx bx bl bh", "rcx": "ecx cx cl ch",
                                  "rdx": "edx dx dl dh", "rsi": "esi si sil", "rdi": "edi di dil",
                                  "rbp": "ebp bp bpl", "rsp": "esp sp spl"}.items() for a in names.split()}
_ALIASES.update({f"r{k}{s}": f"r{k}" for k in range(8, 16) for s in "dwb"})
# Instructions that write memory without an explicit memory operand.
_IMPLICIT_STORES = ("push", "call", "stos", "movs", "rep", "enter", "cmpxchg16b", "xsave", "fxsave")


def _full(i, r):
    """The 64-bit register a capstone register id belongs to (eax, ax, al, ah -> rax)."""
    name = i.reg_name(r)
    return _ALIASES.get(name, name)


def _static_return_address(insns, ret_offset):
    """The executor's bridge resume address for a ret block (capstone instructions with detail), or None when it
    cannot be shown here. The last instruction before the ret that writes (or may write) the saved return-address
    field [r13 + ret_offset, +8) must be a full 8-byte `mov qword ptr [r13 + ret_offset], X`; a write of another
    kind or width to the field, any memory write not based on r13/r14/r15 (it may alias the field) and any
    implicit store give None. X must be an immediate, or a register whose last write in the block (any alias:
    eax, ax, al, ah count for rax) is `lea reg, [rip + disp]`."""
    import capstone as cs
    from capstone.x86 import X86_REG_RIP
    for n in range(len(insns) - 2, -1, -1):
        i = insns[n]
        if i.mnemonic.startswith(_IMPLICIT_STORES):
            return None
        for op in i.operands:
            if op.type != cs.CS_OP_MEM or not op.access & cs.CS_AC_WRITE:
                continue
            base = _full(i, op.mem.base) if op.mem.base else None
            if base in ("r14", "r15"):
                continue  # stack / EVM memory domains, never the callEngine field
            if base != "r13" or op.mem.index:
                return None
            if not (op.mem.disp < ret_offset + 8 and op.mem.disp + op.size > ret_offset):
                continue  # another callEngine field
            ops = i.operands
            dest = ops[0]
            if not (i.mnemonic == "mov" and len(ops) == 2 and dest.type == cs.CS_OP_MEM and dest.size == 8
                    and _full(i, dest.mem.base) == "r13" and not dest.mem.index and dest.mem.disp == ret_offset):
                return None  # the field's last writer is not a full 8-byte mov of it: its value is not shown
            if ops[1].type == cs.CS_OP_IMM:
                return ops[1].imm & 0xFFFFFFFFFFFFFFFF
            if ops[1].type != cs.CS_OP_REG or ops[1].size != 8:
                return None
            source = _full(i, ops[1].reg)
            for w in reversed(insns[:n]):
                if source in {_full(w, r) for r in w.regs_access()[1]}:
                    wo = w.operands
                    if (w.mnemonic == "lea" and wo[0].type == cs.CS_OP_REG and wo[0].size == 8
                            and _full(w, wo[0].reg) == source and wo[1].mem.base == X86_REG_RIP
                            and wo[1].mem.index == 0):
                        return w.address + w.size + wo[1].mem.disp
                    return None
            return None
    return None


def entry_tags_dead(blocks, start: int, end: int, is_bridge, ret_offset):
    """(dead, detail): no memory access routed by a register's pointer tag (base/index other than r13/r14/r15,
    which route by name) can read a tag the register held at `start`, on any path through [start, end) of the
    executor's own blocks (each instruction re-decoded with operand detail). Origins flow through moves, lea and
    add/sub; every other write clears them; an indirect branch or a native call makes the result unknown. A ret
    follows the executor: a block matching its CallGoFunction pattern (`is_bridge`) resumes at the static return
    address written to [r13 + ret_offset] in that block, with every tag kept (no dispatcher clearing is assumed);
    one whose address cannot be determined statically makes the result unknown; any other ret is terminal."""
    import capstone as cs
    md = cs.Cs(cs.CS_ARCH_X86, cs.CS_MODE_64)
    md.detail = True
    by, resume = {}, {}
    for block in blocks:
        decoded = []
        for insn in block.instructions:
            got = list(md.disasm(bytes(insn.bytes), insn.addr))
            if len(got) != 1:
                return False, {"unknown": [f"undecodable instruction at {insn.addr:#x}"]}
            decoded.append(got[0])
        if start <= block.start_addr < end:
            by.update((d.address, d) for d in decoded)
            if decoded and decoded[-1].mnemonic in ("ret", "retq"):
                resume[decoded[-1].address] = (_static_return_address(decoded, ret_offset) if is_bridge(block)
                                               else "terminal")
    if start == end:
        return True, {}
    if start not in by:
        return False, {"unknown": ["start is not an instruction"]}

    def reg(i, r):
        name = i.reg_name(r)
        return _ALIASES.get(name, name)

    states, todo, reads, unknown = {start: {r: frozenset((r,)) for r in _GPRS}}, [start], set(), set()

    def join(at, out):
        if at not in by:
            return
        prior = states.get(at)
        merged = out if prior is None else {r: prior[r] | out[r] for r in _GPRS}
        if prior != merged:
            states[at] = merged
            todo.append(at)

    while todo:
        at = todo.pop()
        i, s = by[at], states[at]
        out, ops, m = dict(s), i.operands, i.mnemonic
        for op in ops:
            if op.type == cs.CS_OP_MEM and m not in ("lea", "nop"):
                for r in (reg(i, op.mem.base), reg(i, op.mem.index)):
                    if r not in ("r13", "r14", "r15"):
                        reads |= {(at, r, origin) for origin in s.get(r, ())}
        _, written = i.regs_access()
        for r in {reg(i, w) for w in written} & set(_GPRS):
            out[r] = frozenset()
        if ops and ops[0].type == cs.CS_OP_REG and ops[0].size == 8:
            dst = reg(i, ops[0].reg)
            if dst in out:
                if m in ("mov", "movabs") and len(ops) > 1 and ops[1].type == cs.CS_OP_REG:
                    out[dst] = s[reg(i, ops[1].reg)] if ops[1].size == 8 else frozenset()
                elif m == "lea":
                    out[dst] = s.get(reg(i, ops[1].mem.base), frozenset()) | s.get(reg(i, ops[1].mem.index), frozenset())
                elif m in ("add", "sub"):
                    out[dst] = s[dst] | (s[reg(i, ops[1].reg)] if len(ops) > 1 and ops[1].type == cs.CS_OP_REG
                                         else frozenset())
        if m in ("ret", "retq"):
            target = resume.get(at)
            if target is None:
                unknown.add(f"bridge resume address at {at:#x} not static here")
            elif target != "terminal":
                join(target, out)
        elif i.group(cs.CS_GRP_JUMP):
            if not ops or ops[0].type != cs.CS_OP_IMM:
                unknown.add(f"indirect branch at {at:#x}")
            else:
                join(ops[0].imm, out)
            if m != "jmp":
                join(at + i.size, out)
        elif i.group(cs.CS_GRP_CALL):
            unknown.add(f"native call at {at:#x}")
            everything = frozenset().union(*s.values())
            join(at + i.size, {r: everything for r in _GPRS})
        else:
            join(at + i.size, out)
    detail = dict(reads=sorted(f"{a:#x} via {r} (entry tag of {o})" for a, r, o in reads)[:20],
                  unknown=sorted(unknown), reachable=len(states))
    return not reads and not unknown, detail


# ---------------------------------------------------------------- proofs

def _limb(v, l):
    return Extract(64 * l + 63, 64 * l, v)


def _home(h, d0, i, l):
    return 32 * ((h - d0) - 1 - i) + 8 * l


def boolean_refutation(formula, timeout_ms=1000):
    """Obligation if the Boolean skeleton of `formula` (every non-connective atom a fresh Boolean, shared atoms
    shared) is UNSAT: any model of the formula gives its atoms values, so UNSAT transfers; SAT proves nothing."""
    from z3 import FreshBool, Implies, Solver, is_and, is_implies, is_not, is_or, is_true, unsat
    from verification.block_equivalence import Obligation
    memo = {}

    def encode(t):
        key = t.get_id()
        if key not in memo:
            if is_true(t) or is_false(t):
                memo[key] = t
            elif is_and(t):
                memo[key] = And(*(encode(c) for c in t.children()))
            elif is_or(t):
                memo[key] = Or(*(encode(c) for c in t.children()))
            elif is_not(t):
                memo[key] = Not(encode(t.arg(0)))
            elif is_implies(t):
                memo[key] = Implies(encode(t.arg(0)), encode(t.arg(1)))
            else:
                memo[key] = FreshBool("chain_atom")
        return memo[key]

    solver = Solver()
    solver.set("timeout", timeout_ms)
    solver.add(encode(formula))
    return solver.check() == unsat


class ChainProver:
    """The lemmas of one block (one entry depth d0) from its hint, on the node's production prover."""

    def __init__(self, prover, block, d0, hint, heights, facts):
        from verification.block_partition import split_at_cutpoints
        from verification.block_summaries import VerifiedSummaryRuntime
        from verification.call_site_mapping import CallSiteMapping
        self.prover, self.block, self.d0, self.hint = prover, block, d0, hint
        self.heights, self.facts = heights, facts  # semantic_plan: EVM stack height and constants before each op
        self.entry, self.end = block_range(prover, block.pc)
        region = [b for b in prover.x86_blocks if self.entry <= b.start_addr < self.end]
        # One instruction per step, except blocks ending in ret (error stubs, bridges: the executor recognises
        # them whole); every hint boundary is a cut as well.
        hinted = {a for o in hint.ops for a in (o.start, o.end) if self.entry <= a < self.end}
        cuts = {i.addr for b in region if b.instructions[-1].mnemonic != "ret" for i in b.instructions} | hinted
        self.region = split_at_cutpoints(region, cuts | {b.start_addr for b in region})
        self.starts = {b.start_addr for b in self.region}
        # Verified summaries (copy loops, memory gas, wide arithmetic) run as one macro step on natural blocks cut
        # at every summary start and hint boundary.
        cutpoints = set(prover.pc_to_addr.values())
        probe = VerifiedSummaryRuntime(region, prover.summary_config, cutpoints=cutpoints, timeout_ms=30000,
                                       max_depth=400, deadline=prover.deadline)
        by_addr = {b.start_addr: b for b in region}
        starts = {by_addr[s.start_block_addr].instructions[s.start_instruction_index].addr
                  for kind in MACRO_KINDS for s in probe.runtime.summaries_for_kind(kind)}
        self.natural = split_at_cutpoints(region, starts | hinted)
        self.runtime = VerifiedSummaryRuntime(self.natural, prover.summary_config, cutpoints=cutpoints,
                                              timeout_ms=30000, max_depth=400, deadline=prover.deadline)
        self.macro = {s.start_block_addr for kind in MACRO_KINDS for s in self.runtime.runtime.summaries_for_kind(kind)}
        # Host-call sites are keyed by their natural ret block's start: re-key them for the cut blocks by the ret.
        orig = prover.call_site_mapping.x86_ret_block_to_evm_site
        by_ret = {b.instructions[-1].addr: orig[b.start_addr] for b in prover.x86_blocks if b.start_addr in orig}
        remap = dict(orig)
        for blocks in (self.region, self.natural):
            for b in blocks:
                if b.instructions[-1].mnemonic == "ret" and b.instructions[-1].addr in by_ret:
                    remap[b.start_addr] = by_ret[b.instructions[-1].addr]
        self.call_site_mapping = CallSiteMapping(remap)
        self.memo = {}

    # -- R_k
    def make_state(self, k, h, locs, facts=(), r15_tag=None):
        """Generic pair state satisfying R_k, built natively at the entry depth d0 (the havoc's geometry is the
        in-block one); the h - d0 values pushed in the block are added on both sides. Op 0 keeps the pre-TAG R14."""
        from state.smt_state import MemoryDomain
        from x86_64.models import Register
        schema = self.prover.schema
        if schema.persistent_invariants:
            raise ValueError("schema persistent invariants: not supported by the in-block construction")
        delta = h - self.d0
        if k == 0 and (delta != 0 or any(loc != ("s",) for slot in locs for loc in slot)):
            raise ValueError("op 0 must start from the block-entry relation")
        known = dict(facts)
        entry_facts = tuple(sorted((i - delta, v) for i, v in known.items() if i >= delta))
        ctx = schema.build_havoc(self.d0, prefix=f"ic{self.block.pc}_{k}",
                                 host_gas_uf_enabled=self.prover.host_gas_uf_enabled,
                                 abstract_calldataload_words=False, assume_calldata_offset_no_overflow=False,
                                 stack_constants=entry_facts)
        s = ctx.state
        regs = s.x86_registers
        base = s.callengine_stack_base + BitVecVal(self.d0 * 32, 64)
        for _ in range(-delta):
            _, s.evm_stack = s.evm_stack.pop()
        for i in reversed(range(max(delta, 0))):  # deepest pushed slot first
            value = BitVecVal(known[i], 256) if i in known else BitVec(f"ic{self.block.pc}_{k}_pushed_{i}", 256)
            s.evm_stack = s.evm_stack.push(value)
            for l in range(4):
                s.x86_memory = s.x86_memory.store_limb(base + BitVecVal(_home(h, self.d0, i, l), 64), _limb(value, l),
                                                       domain=MemoryDomain.STACK)
        if k != 0:
            tag = regs.get_pointer_tag(Register.R14)
            regs.set_register(Register.R14, base)
            regs.set_pointer_tag(Register.R14, tag)
        if r15_tag is not None:
            from state.x86_state import PointerTag
            regs.set_pointer_tag(Register.R15, PointerTag[r15_tag])
        held = {}
        for i, slot in enumerate(locs):
            v = s.evm_stack.peek(i)
            for l, loc in enumerate(slot):
                if loc[0] == "s":
                    continue
                t = _limb(v, l)
                if loc[0] == "r":
                    if loc[1] in held:
                        s.add_assumption(t == held[loc[1]])
                    else:
                        regs.set_register(loc[1], t)
                        held[loc[1]] = t
                else:
                    s.add_assumption(t == BitVecVal(loc[1], 64))
                # the home slot of a register/constant limb is stale on the x86 side
                s.x86_memory = s.x86_memory.store_limb(base + BitVecVal(_home(h, self.d0, i, l), 64),
                                                       BitVec(f"ic{self.block.pc}_{k}_stale_{i}_{l}", 64),
                                                       domain=MemoryDomain.STACK)
        return ctx

    def relation(self, e, x, h, locs, ctx, facts=()):
        """R_{k+1}(e.state, x.state) as named conditions: in-block geometry, every limb at its location, the
        carried stack facts and every other goal of the block schema (components, running, return metadata,
        domain, ABI bases and mirrors, platform premises), whose canonical stack parts the limb goals replace."""
        from state.smt_state import MemoryDomain
        from x86_64.models import Register
        es, xs = e.state, x.state
        regs = xs.x86_registers
        r14 = regs.get_register(Register.R14)
        bo = BitVecVal(self.d0 * 32, 64)
        goals = [("geometry", And(es.evm_stack.SP == h, xs.callengine_stack_byte_offset == bo,
                                  regs.get_register(Register.R15) == xs.callengine_memory_base,
                                  r14 == xs.callengine_stack_base + bo))]
        for i, slot in enumerate(locs):
            v = es.evm_stack.peek(i)
            for l, loc in enumerate(slot):
                if loc[0] == "r":
                    got = regs.get_register(loc[1])
                elif loc[0] == "c":
                    got = BitVecVal(loc[1], 64)
                else:
                    got = xs.x86_memory.load_limb(r14 + BitVecVal(_home(h, self.d0, i, l), 64), domain=MemoryDomain.STACK)
                goals.append((f"stack_{i}_{l}", _limb(v, l) == got))
        goals += [(f"fact_{i}", es.evm_stack.peek(i) == BitVecVal(value, 256)) for i, value in facts]
        spec = SimpleNamespace(stack_depth=h, memory_size=None, free_memory_pointer=None, stack_constants=())
        try:
            schema_goals = self.prover.schema.relation_goals(es, xs, spec, memory_snapshot=ctx.memory_snapshot)
        except ValueError:  # structural defect (unconsumed pending queues, terminated side)
            return goals + [("structural", Or())]
        return goals + [(g.name, g.condition) for g in schema_goals
                        if g.name not in ("stack_geometry", "live_stack_prefix", "stack_constant_predicate")]

    # -- steps
    def evm_step(self, k, state):
        from evm_ir.models import GO_MAX_INT64, EVMBlock
        from verification.loop_induction import run_evm_segment
        ops, b = self.block.operations, self.block
        op = ops[k]
        nxt = ops[k + 1].pc if ops[k + 1].pc > op.pc else op.pc + 1  # BLOCKEND shares its pc with the jump
        if op.kind == "TAG":
            first = EVMBlock(op.pc, b.stack_depth, b.min_depth, b.max_depth, b.static_gas, b.is_jump_target,
                             False, False, [op])
        else:
            first = EVMBlock(op.pc, 0, 0, GO_MAX_INT64, 0, False, True, False, [op])
        tail = EVMBlock(nxt, 0, 0, GO_MAX_INT64, 0, False, True, False, [])
        return run_evm_segment([first, tail], state.copy(), op.pc, {nxt}, max_depth=10)

    def x86_step(self, state, addr, path):
        """One step from addr; `path` (the path condition so far) seeds the executor's constraints, so summary
        preconditions and pruning see it. It is dropped from the returned states' assumptions again."""
        from verification.loop_induction import run_x86_segment
        start = state.copy()
        start.add_assumption(path)
        macro = addr in self.macro
        paths, defects, _ = run_x86_segment(self.natural if macro else self.region, start, addr, self.starts,
                                            max_depth=50 if macro else 10, aot_profile=self.prover.aot_profile,
                                            use_reachability_check=True,
                                            summary_runtime=self.runtime if macro else None,
                                            call_site_mapping=self.call_site_mapping, deadline=self.prover.deadline)
        for r in paths:
            r.state.assumptions = [a for a in r.state.assumptions or [] if not a.eq(path)]
        return paths, defects

    # -- deciding one obligation
    def budget_ms(self, cap):
        """cap, bounded by what is left of the node's deadline (the prover's)."""
        deadline = self.prover.deadline
        return cap if deadline is None else min(cap, int((deadline - monotonic()) * 1000))

    def decide(self, name, formula, skeleton=False):
        """Obligation that `formula` is UNSAT: (coverage queries) Boolean skeleton, direct solve, value cut
        (over-approximation), then BlockEquivalenceProver._check's routes within ROUTE_SECONDS. Only the direct
        solve can answer sat."""
        from verification.block_equivalence import (Obligation, ProofBudgetExceeded, solve_query, term_digest,
                                                    value_cut)
        fingerprint = "sha256:" + term_digest(formula, self.memo)
        spent = Obligation(name, fingerprint, "unknown", provenance="node budget exhausted")
        # Each solver call takes the budget left right before it and never starts at <= 0 (Z3: 0 = no limit).
        budget = self.budget_ms(1000)
        if budget <= 0:
            return spent
        if skeleton and boolean_refutation(formula, budget):
            return Obligation(name, fingerprint, "unsat", provenance="Boolean skeleton UNSAT (over-approximation)")
        budget = self.budget_ms(OP_TIMEOUT_MS)
        if budget <= 0:
            return spent
        answer = solve_query(formula, budget)
        if answer in ("unsat", "sat"):
            return Obligation(name, fingerprint, answer)
        cut, changed = value_cut(formula)
        budget = self.budget_ms(OP_TIMEOUT_MS)
        if changed and budget > 0 and solve_query(cut, budget) == "unsat":
            return Obligation(name, fingerprint, "unsat", provenance="value cut (over-approximation, UNSAT only)")
        if self.budget_ms(1) <= 0:
            return spent
        prover, saved, records = self.prover, self.prover.deadline, []
        budget = monotonic() + ROUTE_SECONDS
        prover.deadline = budget if saved is None else min(saved, budget)
        try:
            prover._check(name, formula, records, split=False)
        except ProofBudgetExceeded:
            records = []
        finally:
            prover.deadline = saved
        if records and records[-1].proved:
            return replace(records[-1], name=name)
        return Obligation(name, fingerprint, "unknown")

    def collect(self, k, evm, xpaths, h1, locs, premise, ctx, facts):
        """Every obligation of lemma k: x86 coverage and each path pair (continuing: R_{k+1}, part by part when
        the whole is undecided; both terminal: observations; mixed: disjointness)."""
        from verification.block_equivalence import Obligation, div_quotient_axioms, host_model_axioms
        from verification.loop_induction import terminal_observable_conditions
        conditions = [premise, *(q.condition for q in (*evm, *xpaths))]
        full = And(premise, *host_model_axioms(conditions), *div_quotient_axioms(conditions))
        tag = f"ic{self.block.pc}_{k}"
        records = [self.decide(f"{tag}_x86_coverage", And(full, Not(Or(*(q.condition for q in xpaths)))), skeleton=True)]
        for i, e in enumerate(evm):
            for j, x in enumerate(xpaths):
                joint, name = And(full, e.condition, x.condition), f"{tag}_pair_{i}_{j}"
                if e.kind != "terminal" and x.kind != "terminal":
                    parts = self.relation(e, x, h1, locs, ctx, facts)
                elif e.kind == x.kind == "terminal":
                    parts = [(f"obs{n}", c) for n, c in enumerate(
                        terminal_observable_conditions(e.state, x.state, ctx.memory_snapshot, True))]
                else:
                    parts = [("disjoint", Or())]
                whole = self.decide(name, And(joint, Not(And(*(c for _, c in parts)))))
                if whole.answer == "unknown" and len(parts) > 1:
                    pieces = [self.decide(f"{name}.{part}", And(joint, Not(c))) for part, c in parts]
                    answer = ("sat" if any(p.answer == "sat" for p in pieces) else
                              "unsat" if all(p.proved for p in pieces) else "unknown")
                    whole = Obligation(name, "conjunction of its parts", answer,
                                       lemmas=tuple(pieces) if answer == "unsat" else (),
                                       required_lemmas=tuple(p.name for p in pieces) if answer == "unsat" else None)
                records.append(whole)
        return records

    def prove_op(self, k, facts, facts_after, r15_in, r15_out):
        """(leaf obligation or None, reason) for op k < last."""
        from verification.block_equivalence import Obligation
        from verification.loop_induction import SegmentPath
        from x86_64.models import Register
        o = self.hint.ops[k]
        h, h1 = self.heights[k], self.heights[k + 1]
        locs, after = locations(o.before, h, self.d0), locations(o.after, h1, self.d0)
        ctx = self.make_state(k, h, locs, facts, r15_in)
        state = ctx.state
        premise = And(*(state.assumptions or []))
        evm, defects = self.evm_step(k, state)
        cont = [e for e in evm if e.kind != "terminal"]
        if defects or len(cont) != 1:
            return None, f"evm: defects={defects} continue_paths={len(cont)}"
        if simplify(cont[0].state.evm_stack.SP).as_long() != h1:
            return None, f"EVM height after op {k} differs from the semantic height plan ({h1})"
        frontier, terminals, steps = [SegmentPath("exit", o.start, premise, state)], [], 0
        while steps < MAX_STEPS:
            addrs = {q.location for q in frontier}
            if addrs == {o.end} or not frontier:
                break
            a = min(addrs)
            if a >= o.end and a not in self.starts:
                return None, f"path left the interval at {a:#x}"
            if a == o.end:
                a = min(x for x in addrs if x != o.end)
            moving = [q for q in frontier if q.location == a]
            frontier = [q for q in frontier if q.location != a]
            for q in moving:
                paths, defects = self.x86_step(q.state, a, q.condition)
                if defects:
                    return None, f"x86 at {a:#x}: " + "; ".join(defects)
                for r in paths:
                    cond = simplify(And(q.condition, r.condition))
                    if not is_false(cond):
                        (terminals if r.kind == "terminal" else frontier).append(
                            SegmentPath(r.kind, r.location, cond, r.state))
            steps += 1
        if frontier and {q.location for q in frontier} != {o.end}:
            return None, f"no convergence at {o.end:#x} within {steps} steps"
        tags = {q.state.x86_registers.get_pointer_tag(Register.R15).name for q in frontier}
        if r15_out is not None and tags != {r15_out}:
            return None, f"R15 tag at the boundary is {sorted(tags)}, R_{k + 1} requires {r15_out}"
        records = self.collect(k, evm, frontier + terminals, h1, after, premise, ctx, facts_after)
        return self._leaf(k, records)

    def prove_exit(self, k, facts, r15_in):
        """The last op: from R_k to the successor's block-boundary relation at every successor entry."""
        from evm_ir.models import GO_MAX_INT64, EVMBlock
        from verification.block_equivalence import div_quotient_axioms, host_model_axioms
        from verification.block_partition import split_at_cutpoints
        from verification.loop_induction import run_evm_segment, run_x86_segment, terminal_observable_conditions
        o, p = self.hint.ops[k], self.prover
        h = self.heights[k]
        ctx = self.make_state(k, h, locations(o.before, h, self.d0), facts, r15_in)
        state = ctx.state
        premise = And(*(state.assumptions or []))
        op = self.block.operations[k]
        # The last op alone, without the block's TAG accounting -- unless it is the TAG itself (a single-op block),
        # whose exit must keep the real static gas and stack guards: the real block.
        synthetic = (self.block if len(self.block.operations) == 1
                     else EVMBlock(op.pc, 0, 0, GO_MAX_INT64, 0, False, True, False, [op]))
        blocks = sorted([*(b for b in p.evm_blocks if b.pc != op.pc), synthetic], key=lambda b: b.pc)
        entries = p.pc_to_addr
        evm, ed = run_evm_segment(blocks, state.copy(), op.pc, set(entries), max_depth=10)
        if ed:
            return None, f"evm: {ed}"
        x86, xd, _ = run_x86_segment(split_at_cutpoints(p.x86_blocks, {o.start}), state.copy(), o.start,
                                     set(entries.values()), max_depth=200, aot_profile=p.aot_profile,
                                     use_reachability_check=True, call_site_mapping=p.call_site_mapping,
                                     deadline=p.deadline)
        if xd:
            return None, f"x86: {xd}"
        conditions = [premise, *(q.condition for q in (*evm, *x86))]
        full = And(premise, *host_model_axioms(conditions), *div_quotient_axioms(conditions))
        tag = f"ic{self.block.pc}_{k}"
        records = [self.decide(f"{tag}_x86_coverage", And(full, Not(Or(*(q.condition for q in x86)))), skeleton=True)]
        for i, e in enumerate(evm):
            for j, x in enumerate(x86):
                if e.kind != "terminal" and x.kind != "terminal" and entries.get(e.location) == x.location:
                    h1 = simplify(e.state.evm_stack.SP).as_long()
                    spec = SimpleNamespace(stack_depth=h1, memory_size=None, free_memory_pointer=None,
                                           stack_constants=())
                    goal = And(*(g.condition for g in p.schema.relation_goals(
                        e.state, x.state, spec, memory_snapshot=ctx.memory_snapshot)))
                elif e.kind == x.kind == "terminal":
                    goal = And(*terminal_observable_conditions(e.state, x.state, ctx.memory_snapshot, True))
                else:
                    goal = Or()
                records.append(self.decide(f"{tag}_exit_{i}_{j}", And(full, e.condition, x.condition, Not(goal))))
        return self._leaf(k, records)

    def _leaf(self, k, records):
        from verification.block_equivalence import Obligation
        bad = [r for r in records if not r.proved]
        if bad:
            kinds = "sat" if any(r.answer == "sat" for r in bad) else "unknown"
            # "solver=sat" (a counterexample under the hint) stops the scheduler's full-budget retry
            return None, f"op {k}: {len(bad)} obligation(s) solver={kinds}: " + ", ".join(r.name for r in bad[:4])
        statement = (f"pc={self.block.pc} d0={self.d0} op {k} {self.block.operations[k].kind}: R_{k} -> "
                     f"R_{k + 1} or matching terminal")
        return Obligation(f"instruction_{k}", statement, "unsat", lemmas=tuple(records),
                          required_lemmas=tuple(r.name for r in records),
                          provenance="instruction-chain leaf: all its obligations UNSAT"), ""


def prove_chain(prover, block, spec, hint, chain):
    """(leaves, reasons) of the chain for proof instance `spec`; reasons non-empty: no theorem."""
    ops = block.operations
    facts = dict(enumerate(chain.facts))  # semantic_plan: the proof instance's constants, then the model's
    tags = r15_tags(prover.x86_blocks, hint)
    leaves = []
    for k in range(len(ops)):
        if prover.deadline is not None and monotonic() >= prover.deadline:
            return leaves, [f"budget exhausted before op {k}"]
        try:
            if k == len(ops) - 1:
                leaf, reason = chain.prove_exit(k, facts[k], tags[k])
            else:
                leaf, reason = chain.prove_op(k, facts[k], facts[k + 1], tags[k], tags[k + 1])
        except Exception as exc:  # noqa: BLE001 - no lemma statement could be formed: the node fails
            leaf, reason = None, f"op {k}: {type(exc).__name__}: {exc}"[:400]
        if leaf is None:
            return leaves, [reason]
        leaves.append(leaf)
    return leaves, []


def _predicate(state, target):
    from verification.cutpoint_relation import read_evm_memory_word
    return And(state.evm_stack.SP == target.stack_depth,
               *([state.evm_memory.MSize == target.memory_size] if target.memory_size is not None else []),
               *([read_evm_memory_word(state, 64) == target.free_memory_pointer]
                 if target.free_memory_pointer is not None else []),
               *(state.evm_stack.peek(i) == v for i, v in target.stack_constants))


def _derive(name, statement, deps):
    from verification.block_equivalence import Obligation
    return Obligation(name, statement, "unsat", lemmas=tuple(deps), required_lemmas=tuple(d.name for d in deps),
                      provenance="instruction-chain composition of its lemmas; not a solver call")


def prove_node(prover, spec, contexts, hint, targets, identity, node_seconds):
    """Worker node result (block_parallel._prove_instance's dict) for proof instance `spec` by the instruction
    chain, or None when the hint cannot be used (the caller falls back to the legacy prover). The node's budget
    (node_seconds, e.g. the scheduler's short first pass) bounds the chain, assembly and H2: over it the node is
    unproved for the budget and the scheduler retries it at the full budget. One exception, as for the legacy
    producer: a shared summary lemma first proved inside the chain runs under its own lemma budget
    (block_summaries.lemma_budget, proved once and then reused), not the node's."""
    saved = prover.deadline
    budget = monotonic() + node_seconds
    prover.deadline = budget if saved is None else min(saved, budget)
    try:
        return _prove_node(prover, spec, contexts, hint, targets, identity)
    finally:
        prover.deadline = saved


def _prove_node(prover, spec, contexts, hint, targets, identity):
    from verification.block_equivalence import InstructionBlockTheorem, Obligation, ProofBudgetExceeded, paths_digest
    from verification.block_program import EdgeCertificate
    from verification.block_specialization import dropped, weakens
    from verification.block_parallel import digest, slim, slim_theorem
    from verification.loop_induction import run_evm_segment
    started = monotonic()
    block = next(b for b in prover.evm_blocks if b.pc == spec.pc)
    entry, end = block_range(prover, spec.pc)
    heights, plan_facts, height_problem = semantic_plan(prover, block, spec.stack_depth, spec.stack_constants)
    if height_problem:  # no complete height plan: no chain (never index a partial plan), the legacy prover takes it
        return None
    problems = chain_problems(block, hint, spec.stack_depth, entry, {b.pc for b in prover.evm_blocks}, heights)
    from x86_64.cfg_executor import X86SymbolicExecutor
    region = [b for b in prover.x86_blocks if entry <= b.start_addr < end]
    bridge = X86SymbolicExecutor(blocks=region, enable_merge=False, use_reachability_check=False,
                                 aot_profile=prover.aot_profile)._is_call_go_function_pattern
    dead, _ = entry_tags_dead(region, entry, end, bridge, prover.aot_profile.offsets["return_address"])
    if problems or not dead:
        return None
    chain = ChainProver(prover, block, spec.stack_depth, hint, heights, plan_facts)
    leaves, reasons = prove_chain(prover, block, spec, hint, chain)

    def result(proved, theorem=None, expected=(), edges=(), status="inconclusive"):
        # Diagnostics: `queries` counts the proved leaves' obligation records (not solver calls; a leaf's routes
        # may call several); a failing leaf or assembly step is described in `reasons`, and `failed` lists the
        # unproved assembly/H2 records. x86 outcome counts of an instruction-chain theorem are quotient classes.
        memo = {}  # one memo: the leaves shared by the theorem and every edge stay shared
        unproved = [r for r in (*assembly, *(e.obligation for e in edges)) if not r.proved]
        return dict(spec=spec, contexts=contexts, identity=identity, proved=proved, status=status,
                    theorem=slim_theorem(theorem, memo) if theorem is not None else None, expected=tuple(expected),
                    edges=slim_theorem(tuple(edges), memo), reasons=tuple(reasons), seconds=monotonic() - started,
                    queries=sum(len(leaf.lemmas) for leaf in leaves), proof_kind=PROOF_KIND,
                    failed=[dict(name=r.name, answer=r.answer, expected=r.expected, seconds=r.elapsed_seconds)
                            for r in unproved])

    assembly = []  # the assembly records, for diagnostics

    if reasons:
        return result(False)
    # The block's outcome classes under the proof instance's own havoc (the existing block-entry relation).
    def check(name, formula, expected="unsat"):
        records = []
        try:
            prover._check(name, formula, records, expected=expected, split=False)
        except ProofBudgetExceeded:  # the node's budget ran out: unknown, never proved
            return Obligation(name, "budget exhausted", "unknown", expected)
        return records[-1]

    ctx = prover.schema.build_havoc(prefix=f"icb{spec.pc}", host_gas_uf_enabled=prover.host_gas_uf_enabled,
                                    assume_calldata_offset_no_overflow=False, abstract_calldataload_words=False,
                                    **spec.as_havoc_kwargs())
    from verification.block_equivalence import div_quotient_axioms, host_model_axioms
    pre = And(*(ctx.state.assumptions or []))
    evm, defects = run_evm_segment(prover.evm_blocks, ctx.state.copy(), spec.pc, set(prover.pc_to_addr),
                                   max_depth=prover.max_depth)
    if defects:
        reasons.append(f"EVM coverage: {defects}")
        return result(False)
    full = And(pre, *host_model_axioms([pre, *(e.condition for e in evm)]),
               *div_quotient_axioms([pre, *(e.condition for e in evm)]))
    goals = prover.schema.relation_goals(ctx.state, ctx.state, spec, memory_snapshot=ctx.memory_snapshot)
    records = [check("entry_nonempty", pre, "sat"),
               check("havoc_relation", And(pre, Not(And(*(g.condition for g in goals))))),
               check("model_domain_nonempty", full, "sat"),
               check("evm_coverage", And(full, Not(Or(*(e.condition for e in evm)))))]
    n = len(evm)
    records += [check(f"evm_disjoint_{i}_{j}", And(full, evm[i].condition, evm[j].condition))
                for i in range(n) for j in range(i + 1, n)]
    records.append(_derive("x86_coverage", "every x86 path is in a class of the finite leaf chain", leaves))
    for i in range(n):
        records.append(_derive(f"x86_maps_{i}_0", "x86 class i's guard is EVM outcome i's guard", leaves))
        records.append(_derive(f"pair_{i}_{i}", "terminal observations or successor relation, by the chain", leaves))
    manifest = tuple((i, i, e.location) for i, e in enumerate(evm) if e.kind != "terminal")
    # (k, start, end, height before, height after); the last op's exits leave the block: its after is its before
    links = tuple((o.index, o.start, o.end, heights[o.index], heights[o.index + 1] if o.index + 1 < len(heights)
                   else heights[o.index]) for o in hint.ops)
    assembly.extend(records)
    # Every summary applied in a macro step is justified by its hit certificate; complete() requires them all.
    certificates = tuple(chain.runtime.certificates)
    theorem = InstructionBlockTheorem(
        identity, spec, tuple(records), tuple(r.name for r in records),
        digest(("instruction-chain", paths_digest(evm, ()), hint.digest)), n, n, True, certificates,
        len(certificates),
        correspondence=tuple(range(n)), arity=(1,) * n, cutpoint_manifest=manifest,
        proof_kind=PROOF_KIND, hint_digest=hint.digest, chain=links, entry_tags_dead=dead)
    if not theorem.complete:
        reasons.append("local obligations: " + ", ".join(r.name for r in records if not r.proved)[:300])
        return result(False)
    # H2 per context and exit: (a) the EVM exit satisfies some target's specialisation, and the lift from the
    # unspecialised successor relation (the chain's exit lemma) plus that specialisation to the full relation.
    from verification.block_specialization import BlockSpecialization
    lifts, edges, expected = {}, [], tuple((i, j) for i, j, _ in manifest)
    for c_index, c in enumerate(contexts):
        if not weakens(spec, c):
            reasons.append(f"context {c!r} is not a weakening of {spec!r}")
            continue
        assumed = dropped(spec, c)
        base = And(pre, *(ctx.state.evm_stack.peek(i) == v for i, v in assumed))
        if assumed and not check(f"context_nonempty_{c_index}", base, "sat").proved:
            reasons.append(f"context {c!r}: premise and E_c empty or unknown")
            continue
        for i, j, pc in manifest:
            e, tgts = evm[i], tuple(targets.get(pc, ()))
            if not tgts:
                reasons.append(f"no frozen targets at pc={pc}")
                continue
            a = check(f"H2_a_{c_index}_{i}", And(base, e.condition, Not(Or(*(_predicate(e.state, t) for t in tgts)))))
            h = simplify(e.state.evm_stack.SP).as_long()
            if (h, pc) not in lifts:
                kw = dict(host_gas_uf_enabled=prover.host_gas_uf_enabled, assume_calldata_offset_no_overflow=False,
                          abstract_calldataload_words=False)
                ec = prover.schema.build_havoc(h, prefix=f"icl_e_{pc}_{h}", **kw)
                xc = prover.schema.build_havoc(h, prefix=f"icl_x_{pc}_{h}", **kw)
                weak = BlockSpecialization(pc, h, None, None, ())
                b = And(*(g.condition for g in prover.schema.relation_goals(ec.state, xc.state, weak,
                                                                           memory_snapshot=ec.memory_snapshot)))
                at = Or(*(_predicate(ec.state, t) for t in tgts))
                whole = Or(*(And(*(g.condition for g in prover.schema.relation_goals(
                    ec.state, xc.state, t, memory_snapshot=ec.memory_snapshot))) for t in tgts))
                lifts[(h, pc)] = check(f"H2_lift_{pc}_{h}", And(b, at, Not(whole)))
            lift = lifts[(h, pc)]
            if a.proved and lift.proved:
                h2 = _derive(f"H2_{c_index}_{i}_{j}", "source and E_c and exit guard imply OR full target relation",
                             (*leaves, a, lift))
            else:
                h2 = slim(a if not a.proved else lift)
                reasons.append(f"H2 ({i},{j}) into pc={pc} not closed (solver={h2.answer})")
            edges.append(EdgeCertificate(c, (i, j), pc, tgts, digest(tgts), identity, h2, assumed))
    # As the legacy worker: the local theorem is proved; open H2 edges are reasons (final_status: inconclusive).
    return result(True, theorem, expected, edges, status="proved")
