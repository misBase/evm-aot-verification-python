"""A warm prefix cache must not reuse another live Context's AST IDs."""
import z3 as z
from x86_64.cfg_state import PrefixSolver, z3_memory_cap


def test_prefix_solver_does_not_keep_foreign_context_assertion():
    with z3_memory_cap(256):
        owner_ctx = z.Context()
        foreign_ctx = z.Context()
        a = z.BitVec('prefix_test_owner_a', 8, ctx=owner_ctx)
        unused = z.BitVec('prefix_test_owner_unused', 8, ctx=owner_ctx)
        owner_condition = a != a
        b, c = z.BitVecs('prefix_test_other_b prefix_test_other_c', 8, ctx=foreign_ctx)
        foreign_condition = b != c
        assert unused.ctx is owner_ctx
        assert owner_condition.get_id() == foreign_condition.get_id()
        prefix = PrefixSolver(z.SolverFor('QF_AUFBV', ctx=owner_ctx))
        assert prefix.check([owner_condition], 1000, wall_ms=1000) == z.unsat
        raw = z.Solver(ctx=foreign_ctx)
        raw.set(timeout=1000, rlimit=100000, random_seed=0)
        raw.add(foreign_condition)
        assert raw.check() == z.sat
        assert prefix.check([owner_condition], 1000, wall_ms=1000) == z.unsat
        # The supplied solver belongs to owner_ctx: cold foreign input is rejected.
        # A warm cache must preserve that boundary, rather than check old assertions.
        try:
            answer = prefix.check([foreign_condition], 1000, wall_ms=1000)
        except z.Z3Exception:
            assert not prefix.stack and prefix.solver.num_scopes() == 0
        else:
            assert answer != z.unsat, 'Warm prefix reused another Context and hid a SAT branch'
        correct = PrefixSolver(z.SolverFor('QF_AUFBV', ctx=foreign_ctx))
        assert correct.check([foreign_condition], 1000, wall_ms=1000) == z.sat
