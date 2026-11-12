from z3 import And, BitVecVal, Solver, unsat

from verification.block_relation import BlockRelationSchema, PLATFORM_MEMORY_BASE_BOUND


def _check(*formulas):
    s = Solver()
    s.add(*formulas)
    return s.check()


def test_havoc_excludes_mcopy_counterexample_memory_base():
    # R15 = 2^63-8 flips MCOPY's signed direction check (see block_relation).
    state = BlockRelationSchema().build_havoc(0, prefix="plat").state
    premise = And(*state.assumptions)
    assert _check(premise, state.callengine_memory_base == BitVecVal((1 << 63) - 8, 64)) == unsat
    assert _check(premise, state.callengine_memory_base == BitVecVal(PLATFORM_MEMORY_BASE_BOUND, 64)) == unsat
    assert _check(premise, state.callengine_memory_base == BitVecVal(PLATFORM_MEMORY_BASE_BOUND - 1, 64)) != unsat


def test_havoc_bounds_calldata_and_code_lengths():
    state = BlockRelationSchema().build_havoc(0, prefix="platlen").state
    premise = And(*state.assumptions)
    for name in ("callengine_input_size_bytes", "calldatasize", "callengine_code_size_bytes"):
        field = getattr(state, name)
        assert _check(premise, field == BitVecVal(PLATFORM_MEMORY_BASE_BOUND, 64)) == unsat, name
        assert _check(premise, field == BitVecVal((1 << 64) - 2, 64)) == unsat, name
        assert _check(premise, field == BitVecVal(PLATFORM_MEMORY_BASE_BOUND - 1, 64)) != unsat, name
