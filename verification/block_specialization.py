"""Untrusted specialization candidates. This module proves no reachability/closure.

H0/H2 and finite-worklist closure are established only by block_program from
actual execution states. TOP memory parameters become symbolic relation nodes;
this generalization itself proves neither reachability nor closure.
"""
from __future__ import annotations
from dataclasses import dataclass, replace
from typing import Mapping, Optional, Tuple


class Top:
    _instance = None

    def __new__(cls):
        if cls._instance is None:
            cls._instance = super().__new__(cls)
        return cls._instance

    def __repr__(self):
        return "TOP"


TOP = Top()


@dataclass(frozen=True)
class BlockSpecialization:
    pc: int
    stack_depth: int
    memory_size: Optional[int]
    free_memory_pointer: Optional[int]
    stack_constants: tuple[tuple[int, int], ...] = ()

    def __post_init__(self):
        for name in ("pc", "stack_depth", "memory_size", "free_memory_pointer"):
            if name in ("memory_size", "free_memory_pointer") and getattr(self, name) is None:
                continue
            if type(getattr(self, name)) is not int or getattr(self, name) < 0:
                raise ValueError(f"{name} must be a non-negative integer")
        if self.stack_depth > 1024:
            raise ValueError("stack_depth exceeds 1024")
        if self.memory_size is not None and (self.memory_size >= 1 << 64 or self.memory_size % 32):
            raise ValueError("memory_size must be uint64 and aligned to 32 bytes")
        if self.free_memory_pointer is not None and self.free_memory_pointer >= 1 << 256:
            raise ValueError("free_memory_pointer must fit uint256")

        if not isinstance(self.stack_constants, tuple):
            raise ValueError("stack_constants must be an immutable tuple")
        indices = []
        for item in self.stack_constants:
            if not isinstance(item, tuple) or len(item) != 2:
                raise ValueError("stack constant must be (top-relative index, uint256 value)")
            index, value = item
            if type(index) is not int or not 0 <= index < self.stack_depth:
                raise ValueError("stack constant index outside the live stack")
            if type(value) is not int or not 0 <= value < 1 << 256:
                raise ValueError("stack constant must fit uint256")
            indices.append(index)
        if indices != sorted(set(indices)):
            raise ValueError("stack constants must have unique sorted indices")

    def as_havoc_kwargs(self):
        kwargs = dict(stack_depth=self.stack_depth, memory_size=self.memory_size,
                      free_memory_pointer=self.free_memory_pointer)
        if self.stack_constants:
            kwargs["stack_constants"] = self.stack_constants
        return kwargs


# Constant-insensitive proof instances (docs/块级实例常量去敏化方案.md). Bump
# the version whenever `sensitive_slots` changes: persisted group results are
# keyed by it. The projection is untrusted: any k with weakens(k, c) is sound
# for c (premise strengthening), a bad choice only makes k harder to prove.
PROJECTION_VERSION = "pi-v1-value-used"


def sensitive_slots(block):
    """Entry slots (top-relative) whose value some operation consumes.

    Labels flow through DUP (copy), SWAP (exchange) and POP (discard); every
    other pop, including a dynamic JUMP/JUMPI target, uses its label. Slots
    that are only moved, or left in place, are not sensitive.
    """
    from tools.msize_absint import live_operations, op_stack_effect
    stack = list(reversed(range(1024)))  # entry labels, top at the end
    used = set()
    for op in live_operations(block):
        kind = op.kind.upper()
        if kind == "DUP":
            stack.append(stack[-op.param])
        elif kind == "SWAP":
            stack[-1], stack[-1 - op.param] = stack[-1 - op.param], stack[-1]
        elif kind == "POP":
            stack.pop()
        else:
            npop, npush = op_stack_effect(op)
            for _ in range(npop):
                label = stack.pop()
                if label is not None:
                    used.add(label)
            stack += [None] * npush
    return frozenset(used)


def project(spec, slots):
    """Proof instance π(c): only the constants at `slots` are kept."""
    return replace(spec, stack_constants=tuple(c for c in spec.stack_constants if c[0] in slots))


def weakens(k, c):
    """R_c = R_k ∧ K_c: same pc/depth/MSize/fmp and K_k ⊆ K_c (index and value)."""
    return ((k.pc, k.stack_depth, k.memory_size, k.free_memory_pointer)
            == (c.pc, c.stack_depth, c.memory_size, c.free_memory_pointer)
            and set(k.stack_constants) <= set(c.stack_constants))


def dropped(k, c):
    """D_c = K_c \\ K_k, in K_c order: the equalities H2 of c assumes on k's exits."""
    return tuple(x for x in c.stack_constants if x not in k.stack_constants)


@dataclass(frozen=True)
class ClosureViolation:
    # Historical API name; these are candidate-integrity defects, not SMT H2.
    kind: str
    pc: int
    detail: str


@dataclass
class SpecializationPlan:
    specializable: Mapping[int, Tuple[BlockSpecialization, ...]]
    degraded: Mapping[int, str]
    violations: Tuple[ClosureViolation, ...] = ()
    rounds: int = 0  # no semantic worklist runs in this utility

    @property
    def ok(self):
        """Candidate integrity only; never permission to report VERIFIED."""
        return not self.violations

    @property
    def theorem_instances(self):
        return sum(len(v) for v in self.specializable.values())

    def coverage_summary(self):
        total = len(self.specializable) + len(self.degraded)
        if not total:
            return "no candidate blocks"
        return (f"{len(self.specializable)}/{total} blocks specializable "
                f"({len(self.specializable) / total * 100:.1f}%), "
                f"{len(self.degraded)} degraded, {self.theorem_instances} candidate instances; "
                "H0/H2 not checked")


def _as_value_set(raw):
    # The abstract interpreter owns a separate TOP sentinel. Normalize its
    # actual producer value as well as this candidate API's public sentinel.
    from tools.msize_absint import TOP as ANALYSIS_TOP
    if raw is None:
        return frozenset({None})
    if isinstance(raw, Top) or raw is ANALYSIS_TOP:
        return None
    if type(raw) is int:
        return frozenset({raw})
    return frozenset(raw)


def build_specialization_plan(*, reachable_pcs, succs, depth_classes, memory_sizes,
                              free_pointers, max_rounds=64, max_instances=100_000):
    """Normalize proposals, rejecting malformed/missing references.

    max_rounds is retained for source compatibility and has no proof meaning.
    max_instances is a resource cap, not an inference of semantic divergence.
    """
    pcs = sorted(set(reachable_pcs))
    specializable, degraded, violations = {}, {}, []
    count = 0
    for pc in pcs:
        try:
            depths = frozenset(depth_classes.get(pc, ()))
            msizes = _as_value_set(memory_sizes.get(pc, TOP))
            fmps = _as_value_set(free_pointers.get(pc, TOP))
            if not depths:
                raise ValueError("block is in the reachable set but has no depth class")
            msizes = frozenset({None}) if msizes is None else msizes
            fmps = frozenset({None}) if fmps is None else fmps
            if not msizes or not fmps:
                raise ValueError("memory_size/fmp analysis returned an empty value set")
            count += len(depths) * len(msizes) * len(fmps)
            if count > max_instances:
                raise ValueError("candidate instance resource budget exhausted")
            specializable[pc] = tuple(BlockSpecialization(pc, d, m, f)
                for d in sorted(depths)
                for m in sorted(msizes, key=lambda v: -1 if v is None else v)
                for f in sorted(fmps, key=lambda v: -1 if v is None else v))
        except (ValueError, TypeError) as exc:
            violations.append(ClosureViolation("inconsistent", pc, str(exc)))
    for pc in pcs:
        for succ in succs.get(pc, ()):
            if succ not in pcs:
                violations.append(ClosureViolation("transition", pc,
                    f"edge {pc}->{succ} references an unregistered block"))
    return SpecializationPlan(specializable, degraded, tuple(violations))
