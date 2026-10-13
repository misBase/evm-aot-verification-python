"""CErc20 pc=6619 at stack depth 15: the returndata copy summary was rejected.

The copy operands are read through a Store chain whose length grows with the
entry stack depth.  ``forward_selects`` recursed past Python's limit, z3
reported ``ctypes.ArgumentError(RecursionError)``, every per-hit proof was
rejected and the raw copy loop ran into max_depth.
"""
import sys

from z3 import Array, BitVec, BitVecSort, BitVecVal, Select, Store, ULT, unsat

from x86_64.summaries.copy_loop import _implication_result


def test_implication_survives_store_chain_deeper_than_recursion_limit():
    base = BitVec("r14", 64)
    memory = Array("mem", BitVecSort(64), BitVecSort(8))
    memory = Store(memory, base, BitVecVal(7, 8))
    for i in range(1, 2 * sys.getrecursionlimit()):
        memory = Store(memory, base + i, BitVecVal(0xFF, 8))
    size = Select(memory, base)
    limit = sys.getrecursionlimit()
    assert _implication_result(True, [], ULT(size, BitVecVal(8, 8))) == unsat
    assert sys.getrecursionlimit() == limit


def test_forwarding_does_not_prove_a_false_premise():
    base = BitVec("r14", 64)
    memory = Array("mem", BitVecSort(64), BitVecSort(8))
    memory = Store(memory, base, BitVecVal(7, 8))
    for i in range(1, 2 * sys.getrecursionlimit()):
        memory = Store(memory, base + i, BitVecVal(0xFF, 8))
    assert _implication_result(True, [], ULT(Select(memory, base), BitVecVal(7, 8)), 2000) != unsat
