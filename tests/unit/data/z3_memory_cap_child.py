"""Child process of test_block_remaining_blocks_4 (fix 23/26 v2): every Z3 call under a tiny
z3_memory_cap ends as unknown or a Python Z3Exception; an abort (SIGABRT) fails the test."""
import z3

import verification.block_equivalence as be
import x86_64.cfg_state as cs

x, y, q = z3.BitVec("n4c_x", 512), z3.BitVec("n4c_y", 512), z3.BitVec("n4c_q", 512)
hard = [y != 0, z3.UDiv(x, y) * y + z3.URem(x, y) != x, z3.UDiv(x * q, y + 1) == q * x]
cs.REACHABILITY_MEMORY_MB = be.QUERY_MEMORY_MB = 1
out = []

solver = z3.SolverFor("QF_AUFBV")  # check(assumptions), as Z3_solver_check_assumptions on the servers
solver.add(*hard[1:])
try:
    with cs.z3_memory_cap():
        out.append(str(solver.check(hard[0])))
except z3.Z3Exception as exc:
    out.append("memory" if cs.out_of_memory(exc) else "other")

# Incremental, one push per conjunct: at 128 bits (pushes internalize terms outside any cap, so the
# 512-bit version grows to GBs before the check starts).
a, b, c = z3.BitVec("n4c_a", 128), z3.BitVec("n4c_b", 128), z3.BitVec("n4c_c", 128)
prefix = cs.PrefixSolver()
out.append(str(prefix.check([b != 0, z3.UDiv(a, b) * b + z3.URem(a, b) != a, z3.UDiv(a * c, b + 1) == c * a],
                            60000, "test")))
out.append(str(prefix.check([z3.And(hard)], 60000, "test")))
# As is_possible: the check trips, then PrefixSolver resets the solver inside the enclosing cap
# (memory_max_size: SIGABRT in Z3_solver_reset, PoolManager 18089 locally after 2084s).
with cs.z3_memory_cap():
    out.append(str(prefix.check([z3.And(hard)], 60000, "test")))
out.append(be.solve_query(z3.And(hard), 60000))
out.append(be.solve_pure_bv(z3.And(hard), 60000))
try:
    with cs.z3_memory_cap():
        z3.simplify(z3.And(hard), blast_select_store=True)
        out.append("simplified")
except z3.Z3Exception as exc:
    out.append("memory" if cs.out_of_memory(exc) else "other")
small = z3.SolverFor("QF_AUFBV")
small.add(z3.ULT(z3.BitVec("n4c_k", 8), 3))
print(" ".join(out), small.check())
