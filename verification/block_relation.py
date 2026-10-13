"""The block boundary is before TAG, including its error-producing guards.

This schema deliberately does not change the older post-TAG loop schema.
Unconstrained machine state is universal, never inherited from the initial
state's zero-filled scratch memory or flags.
"""
from z3 import (And, Array, BitVec, BitVecSort, BitVecVal, Extract, K,
                ULE, ULT, Store, substitute)

from state.x86_state import MemoryDomain
from verification.cutpoint_relation import CutpointRelationSchema, RelationGoal, read_x86_stack_slot
from x86_64.aot_profile import GO_HPC_EVM_PROFILE
from x86_64.models import Register


# Trusted platform premise, stated in every certificate scope: the Go heap
# (R15 = memoryElement0Address) lives in canonical x86-64 user space. MCOPY's
# direction check compares absolute addresses *signed* (compileEVMMCOPY), so
# without this bound the model admits R15 near 2^63 where the copy is wrong.
PLATFORM_MEMORY_BASE_BOUND = 1 << 47
PLATFORM_SCOPE = ("platform premise: memory base (R15) < 2^47 and calldata/code lengths < 2^47 "
                  "(canonical user space; the input and code are Go byte slices in it)")
# Same canonical-address-space fact, applied to the lengths of the immutable
# Go slices callEngine exposes (user-approved 2026-09-26). Without it the
# model admits calldata near 2^64, where offset+k wraps in the byte-copy loop
# (the interpreter itself would panic in getData's data[start:end]).
_IMMUTABLE_SLICE_LENGTHS = ("callengine_input_size_bytes", "calldatasize", "callengine_code_size_bytes")


def platform_premises(state):
    bound = BitVecVal(PLATFORM_MEMORY_BASE_BOUND, 64)
    return (ULT(state.callengine_memory_base, bound),
            *(ULT(getattr(state, name), bound) for name in _IMMUTABLE_SLICE_LENGTHS))


def stack_constant_condition(evm, x86, constants):
    """Both canonical stack views hold `constants` ((top-relative index, value))."""
    return And(*(And(evm.evm_stack.peek(index) == value, read_x86_stack_slot(x86, index) == value)
                 for index, value in constants))


class BlockRelationSchema(CutpointRelationSchema):
    version = "block-pre-tag-v4-platform-bounds"
    # Only fields actually coupled by the constructor belong here. Scratch
    # side channels and their backing bytes are independent arbitrary values.
    ABI_MIRRORS = CutpointRelationSchema._CALLENGINE_MIRROR_FIELDS + (
        ("callengine_memory_base", "memory_base"),
        ("callengine_stack_base", "stack_base"),
        ("callengine_callvalue", "callvalue"),
        ("callengine_self_address_pointer", "self_address_pointer"),
        ("callengine_origin_address_pointer", "origin_address_pointer"),
        ("callengine_caller_address_pointer", "caller_address_pointer"),
        ("callengine_input_pointer", "input_pointer"),
        ("callengine_input_size_bytes", "input_size"),
        ("callengine_code_pointer", "code_pointer"),
        ("callengine_code_size_bytes", "code_size"),
    )

    def __init__(self, **kwargs):
        kwargs.setdefault("max_stack_byte_offset", 1024 * 32)
        super().__init__(**kwargs)

    @property
    def fingerprint(self):
        from hashlib import sha256
        return sha256(repr((super().fingerprint, self.ABI_MIRRORS,
                           "running_return_metadata_empty", "pre-TAG", self.version)).encode()).hexdigest()

    def build_havoc(self, stack_depth, *, prefix=None, stack_constants=(), **kwargs):
        from verification.block_specialization import BlockSpecialization
        BlockSpecialization(0, stack_depth, kwargs.get("memory_size", 0),
                            kwargs.get("free_memory_pointer", 0), stack_constants)
        if prefix is None:
            self._counter += 1
            prefix = f"block{self._counter}"
        kwargs.setdefault("assume_calldata_offset_no_overflow", False)
        context = super().build_havoc(stack_depth, prefix=prefix, **kwargs)
        state = context.state
        if stack_constants:
            from verification.memory_mapping import StackMemoryMapper
            for index, value in stack_constants:
                state.evm_stack.Stack = Store(state.evm_stack.Stack,
                    state.evm_stack.SP - 1 - index, BitVecVal(value, 256))
            # Write the same predicate constants to both canonical views.
            values = [state.evm_stack.peek(i) for i in reversed(range(stack_depth))]
            state.x86_memory = StackMemoryMapper.initialize_x86_memory_from_stack(
                state.x86_memory, values,
                base=state.callengine_stack_base + state.callengine_stack_byte_offset)
        state.complete_jump_domain = True
        # Canonical live slots remain initialized; every other stack byte is
        # arbitrary. callEngine is rebuilt to avoid retaining scratch stores.
        zero = K(BitVecSort(64), BitVecVal(0, 8))
        state.x86_memory.stack_mem = substitute(
            state.x86_memory.stack_mem,
            (zero, Array(f"{prefix}_stack_rest", BitVecSort(64), BitVecSort(8))),
        )
        state.x86_memory.call_engine_mem = Array(
            f"{prefix}_ce_rest", BitVecSort(64), BitVecSort(8)
        )
        for name in ("callengine_stack_pointer_limbs", "callengine_builtin_func_index",
                     "callengine_go_func_index", "callengine_return_address",
                     "callengine_builtin_arg0"):
            old = getattr(state, name)
            setattr(state, name, BitVec(f"{prefix}_{name}", old.size()))
        r13 = state.x86_registers.get_register(Register.R13)
        for field, offset in self.ABI_MIRRORS:
            state.x86_memory = state.x86_memory.store_limb(
                r13 + GO_HPC_EVM_PROFILE.offsets[offset], getattr(state, field),
                domain=MemoryDomain.CALLENGINE,
            )
        for reg in Register:
            if reg not in (Register.R13, Register.R15):
                state.x86_registers.set_register(reg, BitVec(f"{prefix}_{reg.value}", 64))
        for flag in ("CF", "PF", "AF", "ZF", "SF", "OF", "DF"):
            state.x86_registers.set_flag(flag, BitVec(f"{prefix}_{flag}", 1))
        # Explicit inductive invariant, re-proved by Base and all edges below.
        # RETURN/REVERT metadata is separate from a host call's return_data.
        state.return_offset = BitVecVal(0, 64)
        state.return_length = BitVecVal(0, 64)
        for invariant in self.persistent_invariants:
            for condition in invariant(state, state):
                state.add_assumption(condition)
        for condition in platform_premises(state):
            state.add_assumption(condition)
        return context

    def relation_goals(self, evm, x86, spec, *, memory_snapshot=None):
        """The same predicate is used for havoc, Base and every actual edge."""
        goals = list(super().component_goals(
            evm, x86, spec.stack_depth, memory_snapshot=memory_snapshot,
            memory_size=spec.memory_size, free_memory_pointer=spec.free_memory_pointer,
            site="exit",  # pre-TAG: no premise on the old R14
        ))
        goals.append(RelationGoal("stack_constant_predicate",
                                  stack_constant_condition(evm, x86, spec.stack_constants)))
        report = self.structural_premises(evm, x86, site="base_arrival")
        if report.defects:
            raise ValueError("; ".join(report.defects))
        goals.append(RelationGoal("running", And(*report.conditions)))
        goals.append(RelationGoal("running_return_metadata_empty", And(
            evm.return_offset == 0, evm.return_length == 0,
            x86.return_offset == 0, x86.return_length == 0,
        )))
        goals.append(RelationGoal("domain", And(
            ULE(evm.evm_memory.MSize, self.max_memory_size_bytes),
            ULE(x86.callengine_memory_size_bytes, self.max_memory_size_bytes),
            evm.evm_memory.MSize & 31 == 0,
            x86.callengine_memory_size_bytes & 31 == 0,
            ULE(x86.callengine_stack_byte_offset, self.max_stack_byte_offset),
        )))
        goals.append(RelationGoal("abi_bases", And(
            evm.x86_registers.get_register(Register.R13) == x86.x86_registers.get_register(Register.R13),
            evm.callengine_stack_base == x86.callengine_stack_base,
            evm.callengine_memory_base == x86.callengine_memory_base,
        )))
        goals.append(RelationGoal("platform_memory_base", And(
            *platform_premises(evm), *platform_premises(x86))))
        goals.append(RelationGoal("abi_environment_range", And(*(
            Extract(255, 160, getattr(evm, field)) == 0
            for field in ("self_address", "origin_address", "caller_address")
        ))))
        r13 = x86.x86_registers.get_register(Register.R13)
        goals.append(RelationGoal("abi_mirrors", And(*(
            x86.x86_memory.load_limb(r13 + GO_HPC_EVM_PROFILE.offsets[offset],
                                     domain=MemoryDomain.CALLENGINE) == getattr(x86, field)
            for field, offset in self.ABI_MIRRORS
        ))))
        for index, invariant in enumerate(self.persistent_invariants):
            goals.append(RelationGoal(f"invariant_{index}", And(*invariant(evm, x86))))
        return tuple(goals)
