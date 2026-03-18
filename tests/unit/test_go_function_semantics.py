"""
GoFunctionSemantics 单元测试。

验证通过x86内存操作建模Go host/builtin函数的语义效果。
"""

import pytest
from z3 import BitVecVal, Solver, sat, unsat, simplify

from state.smt_state import SMTState, EVMStorageState
from x86_64.aot_profile import GO_HPC_EVM_PROFILE, X86AOTProfile
from x86_64.go_function_semantics import GoFunctionSemantics, LIMBS_PER_UINT256
from x86_64.models import Register


def _make_profile_with_host(host_map):
    """Create an AOT profile with custom host function mapping."""
    return X86AOTProfile(
        offsets=GO_HPC_EVM_PROFILE.offsets,
        status_codes=GO_HPC_EVM_PROFILE.status_codes,
        resumable_statuses=GO_HPC_EVM_PROFILE.resumable_statuses,
        builtin_functions=GO_HPC_EVM_PROFILE.builtin_functions,
        host_functions=host_map,
    )


R13_BASE = 0x10000  # callEngine base, separate from stack area
R14_BASE = 0x20000  # stack base


def _make_state_with_stack(values, sp_start=0):
    """Create an SMTState with Uint256 values in x86 memory at [R14 + offset].

    Args:
        values: list of 256-bit integer values to push
        sp_start: initial sp (in limbs)

    Returns:
        (state, sp_after_push) tuple
    """
    state = SMTState()
    state.x86_registers.set_register(Register.R13, BitVecVal(R13_BASE, 64))
    state.x86_registers.set_register(Register.R14, BitVecVal(R14_BASE, 64))

    sp = sp_start
    for val in values:
        base_offset = BitVecVal(R14_BASE + sp * 8, 64)
        state.x86_memory = state.x86_memory.store_256bit(base_offset, BitVecVal(val, 256))
        sp += LIMBS_PER_UINT256

    return state, sp


class TestPopPush:
    """Test the low-level pop/push operations."""

    def test_pop_single_value(self):
        """Pop a single Uint256 from x86 memory."""
        state, sp = _make_state_with_stack([0x1234])
        sem = GoFunctionSemantics(GO_HPC_EVM_PROFILE)

        value, new_sp, state = sem._pop_uint256(sp, state)

        solver = Solver()
        solver.add(value == BitVecVal(0x1234, 256))
        assert solver.check() == sat
        assert new_sp == sp - LIMBS_PER_UINT256

    def test_push_then_pop_roundtrip(self):
        """Push a value then pop it back."""
        state, sp = _make_state_with_stack([])
        sem = GoFunctionSemantics(GO_HPC_EVM_PROFILE)

        val = BitVecVal(0xDEADBEEF, 256)
        sp, state = sem._push_uint256(sp, val, state)
        popped, sp, state = sem._pop_uint256(sp, state)

        solver = Solver()
        solver.add(popped != val)
        assert solver.check() == unsat, "Push then pop should return the same value"

    def test_pop_two_values_order(self):
        """Pop two values and verify LIFO order."""
        state, sp = _make_state_with_stack([0xAA, 0xBB])
        sem = GoFunctionSemantics(GO_HPC_EVM_PROFILE)

        first, sp, state = sem._pop_uint256(sp, state)
        second, sp, state = sem._pop_uint256(sp, state)

        solver = Solver()
        # First popped should be 0xBB (last pushed), second should be 0xAA
        solver.add(first == BitVecVal(0xBB, 256))
        solver.add(second == BitVecVal(0xAA, 256))
        assert solver.check() == sat


class TestSloadSstore:
    """Test SLOAD and SSTORE host function handlers."""

    def test_sstore_modifies_storage(self):
        """SSTORE: pop key, pop value, store in storage."""
        key_val = 0x42
        data_val = 0x1234

        profile = _make_profile_with_host({0: "sstore"})
        sem = GoFunctionSemantics(profile)

        # Stack: [key, value] (key on top, pushed last)
        state, sp = _make_state_with_stack([data_val, key_val])

        state = sem.apply(4, 0, sp, state)

        # Verify storage was updated
        loaded = state.evm_storage.sload(BitVecVal(key_val, 256))
        solver = Solver()
        solver.add(loaded == BitVecVal(data_val, 256))
        assert solver.check() == sat

    def test_sload_reads_storage(self):
        """SLOAD: pop key, push Select(Storage, key)."""
        key_val = 0x42
        data_val = 0x9999

        profile = _make_profile_with_host({0: "sload"})
        sem = GoFunctionSemantics(profile)

        # Pre-populate storage
        state, sp = _make_state_with_stack([key_val])
        state.evm_storage = state.evm_storage.sstore(
            BitVecVal(key_val, 256), BitVecVal(data_val, 256)
        )

        state = sem.apply(4, 0, sp, state)

        # After SLOAD: key was popped, result was pushed.
        # sp should be the same (pop 1 + push 1 = net 0)
        # Read the result from the top of x86 memory stack
        # The value is at [R14 + (sp - 4) * 8]
        result = state.x86_memory.load_256bit(
            BitVecVal(R14_BASE + (sp - LIMBS_PER_UINT256) * 8, 64)
        )

        solver = Solver()
        solver.add(result == BitVecVal(data_val, 256))
        assert solver.check() == sat

    def test_sstore_sload_roundtrip(self):
        """SSTORE then SLOAD should return the stored value."""
        key_val = 0x10
        data_val = 0xABCD

        profile = _make_profile_with_host({0: "sstore", 1: "sload"})
        sem = GoFunctionSemantics(profile)

        # SSTORE: push value and key to stack
        state, sp = _make_state_with_stack([data_val, key_val])
        state = sem.apply(4, 0, sp, state)

        # After SSTORE, sp decremented by 2 * 4 limbs = 8
        new_sp = sp - 2 * LIMBS_PER_UINT256

        # SLOAD: push key to stack
        state.x86_memory = state.x86_memory.store_256bit(
            BitVecVal(R14_BASE + new_sp * 8, 64), BitVecVal(key_val, 256)
        )
        sload_sp = new_sp + LIMBS_PER_UINT256

        state = sem.apply(4, 1, sload_sp, state)

        # Read the SLOAD result from stack
        result = state.x86_memory.load_256bit(
            BitVecVal(R14_BASE + (sload_sp - LIMBS_PER_UINT256) * 8, 64)
        )

        solver = Solver()
        solver.add(result != BitVecVal(data_val, 256))
        assert solver.check() == unsat, "SSTORE/SLOAD roundtrip should preserve value"


class TestBuiltinFunctions:
    """Test builtin function handlers (statusCode=5)."""

    def _read_result_after_binary_op(self, state, original_sp):
        """Read result from x86 memory after a binary op (pop 2, push 1).

        After: pop a, pop b, push result => net sp change = -4 limbs
        Result is at [R14 + (original_sp - 2*4) * 8] (where push happened)
        """
        result_base = R14_BASE + (original_sp - 2 * LIMBS_PER_UINT256) * 8
        return state.x86_memory.load_256bit(BitVecVal(result_base, 64))

    def test_builtin_div(self):
        """DIV builtin: pop a (top), pop b, push a/b."""
        from z3 import SolverFor
        sem = GoFunctionSemantics(GO_HPC_EVM_PROFILE)

        # Stack bottom-to-top: [3, 100] => top=100, second=3
        # DIV pops a=100, b=3, pushes 100/3 = 33
        state, sp = _make_state_with_stack([3, 100])
        state = sem.apply(5, 3, sp, state)

        result = self._read_result_after_binary_op(state, sp)

        solver = SolverFor("QF_AUFBV")
        solver.set("timeout", 5000)
        solver.add(result != BitVecVal(33, 256))
        assert solver.check() == unsat, "100 / 3 should be 33"

    def test_builtin_div_by_zero(self):
        """DIV by zero should return 0 (EVM semantics)."""
        from z3 import SolverFor
        sem = GoFunctionSemantics(GO_HPC_EVM_PROFILE)

        # Stack bottom-to-top: [0, 42] => top=42, second=0
        # But for div-by-zero: we need divisor=0
        # pop a=42, pop b=0 => 42/0 = 0 (EVM semantics)
        state, sp = _make_state_with_stack([0, 42])
        state = sem.apply(5, 3, sp, state)

        result = self._read_result_after_binary_op(state, sp)

        solver = SolverFor("QF_AUFBV")
        solver.set("timeout", 5000)
        solver.add(result != BitVecVal(0, 256))
        assert solver.check() == unsat, "DIV by zero must return 0"

    def test_builtin_mod(self):
        """MOD builtin: pop a (top), pop b, push a%b."""
        from z3 import SolverFor
        sem = GoFunctionSemantics(GO_HPC_EVM_PROFILE)

        # Stack bottom-to-top: [3, 100] => top=100, second=3
        # MOD pops a=100, b=3, pushes 100%3 = 1
        state, sp = _make_state_with_stack([3, 100])
        state = sem.apply(5, 4, sp, state)

        result = self._read_result_after_binary_op(state, sp)

        solver = SolverFor("QF_AUFBV")
        solver.set("timeout", 5000)
        solver.add(result != BitVecVal(1, 256))
        assert solver.check() == unsat, "100 % 3 should be 1"

    def test_builtin_exp(self):
        """EXP builtin uses uninterpreted function (same as IR side)."""
        from z3 import Function, BitVecSort, SolverFor

        sem = GoFunctionSemantics(GO_HPC_EVM_PROFILE)

        # Stack bottom-to-top: [10, 2] => top=2 (base), second=10 (exp)
        # EXP pops base=2, exp=10, pushes evm_exp(2, 10)
        state, sp = _make_state_with_stack([10, 2])
        state = sem.apply(5, 7, sp, state)

        result = self._read_result_after_binary_op(state, sp)

        exp_func = Function('evm_exp', BitVecSort(256), BitVecSort(256), BitVecSort(256))
        expected = exp_func(BitVecVal(2, 256), BitVecVal(10, 256))

        solver = SolverFor("QF_AUFBV")
        solver.set("timeout", 5000)
        solver.add(result != expected)
        assert solver.check() == unsat


class TestExtractMethods:
    """Test metadata extraction methods in cfg_executor.

    Uses real x86 blocks from the muti_block test data to verify extraction.
    """

    def test_extract_from_real_go_bridge_block(self):
        """Extract metadata from a real Go bridge block in muti_block.hex."""
        from pathlib import Path
        from x86_64.cfg_executor import X86SymbolicExecutor
        from x86_64.disassembler import disassemble_hex
        from x86_64.cfg import identify_basic_blocks

        test_dir = Path(__file__).parent.parent
        hex_file = test_dir / "data" / "muti_block.hex"
        if not hex_file.exists():
            pytest.skip("muti_block.hex not found")

        hex_data = hex_file.read_text().strip()
        instructions = disassemble_hex(hex_data, base_addr=0x0)
        blocks = identify_basic_blocks(instructions)

        executor = X86SymbolicExecutor(blocks, enable_go_bridge=True)

        # Find blocks that match the CallGoFunction pattern
        found_go_bridge = False
        for block in blocks:
            if executor._is_call_go_function_pattern(block):
                found_go_bridge = True
                status = executor._extract_status_code(block)
                sp = executor._extract_stack_pointer(block)
                assert status is not None, f"Block 0x{block.start_addr:x} should have status_code"
                assert status in executor.aot_profile.resumable_statuses
                # SP may or may not be present (can be omitted)
                if sp is not None:
                    assert isinstance(sp, int)
                break

        # Skip if no Go bridge blocks found (shouldn't happen with muti_block)
        if not found_go_bridge:
            pytest.skip("No Go bridge blocks found in muti_block.hex")


class TestStorageEquivalence:
    """Test storage equivalence checking in RefinementChecker."""

    def test_same_storage_is_equivalent(self):
        """Identical storage arrays should be equivalent."""
        from verification.refinement_checker import RefinementChecker
        from z3 import Array, BitVecSort

        checker = RefinementChecker(timeout_ms=5000)
        storage = Array('Storage', BitVecSort(256), BitVecSort(256))

        verified, msg = checker._check_storage_equivalence(storage, storage)
        assert verified

    def test_different_storage_not_equivalent(self):
        """Storage arrays with different writes should not be equivalent."""
        from verification.refinement_checker import RefinementChecker
        from z3 import Array, BitVecSort, Store

        checker = RefinementChecker(timeout_ms=5000)
        storage = Array('Storage', BitVecSort(256), BitVecSort(256))

        s1 = Store(storage, BitVecVal(0, 256), BitVecVal(1, 256))
        s2 = Store(storage, BitVecVal(0, 256), BitVecVal(2, 256))

        verified, msg = checker._check_storage_equivalence(s1, s2)
        assert not verified

    def test_same_write_is_equivalent(self):
        """Storage arrays with the same write should be equivalent."""
        from verification.refinement_checker import RefinementChecker
        from z3 import Array, BitVecSort, Store

        checker = RefinementChecker(timeout_ms=5000)
        storage = Array('Storage', BitVecSort(256), BitVecSort(256))

        s1 = Store(storage, BitVecVal(42, 256), BitVecVal(100, 256))
        s2 = Store(storage, BitVecVal(42, 256), BitVecVal(100, 256))

        verified, msg = checker._check_storage_equivalence(s1, s2)
        assert verified
