"""memoryGasCost 的 `square` 必须是 **uint64 乘法**，不是 128-bit 精确积。

权威来源（两处一致）：

- 解释器 `evm/gas_table.go:46`：`square := newMemSizeWords * newMemSizeWords`，
  `newMemSizeWords` 是 uint64 ⟹ 乘法按 2^64 回绕。
- amd64 codegen `evm/aot/gas_dynamic_amd64.go:552-566`：

      MOVQ tmpReg, RAX ; MULQ RAX ; MOVQ RAX, tmpReg4   // 丢弃 RDX（高 64 位）
      MOVQ tmpReg4, RAX ; MOVQ 512, tmpReg4
      MOVQ 0, RDX                                        // dividend 高位清零
      DIVQ tmpReg4

  即 x86 的 dividend 逐字是 `Concat(0, square_low64)` = `ZeroExt(64, w*w)`。

历史写法 `ZeroExt(64,w)*ZeroExt(64,w)` 在协议 cap 内与之等价（见
`test_two_forms_agree_within_protocol_cap`），但 AST 与 x86 不同形，Z3 只能
bit-blast 一个 64×64 乘法器去证二者相等 —— CErc20 pc=792 / Safe pc=771 的
RETURN 终止义务因此 unknown。cap 外两式**真不等**
（`test_forms_differ_above_cap_and_go_wraps`），所以当前写法是更忠实的一方。
"""

import pytest
from z3 import (BitVec, BitVecVal, Extract, Implies, LShR, Not, Solver, UDiv,
                ULE, ZeroExt, simplify, unsat)

from state.evm_gas_state import memory_expansion_fee

MEM_SIZE_CAP = 0x1FFFFFFFE0  # gas_table.go:38，calc_mem_size_64 把它建成 OOG 分支
MAX_LEGAL_WORDS = 0xFFFFFFFF  # cap >> 5


def _quad(square_128):
    return Extract(63, 0, UDiv(square_128, BitVecVal(512, 128)))


def _old_quad(w):
    """被替换掉的 128-bit 精确积写法。"""
    return _quad(ZeroExt(64, w) * ZeroExt(64, w))


def _new_quad(w):
    """当前写法：uint64 square 再 ZeroExt。"""
    return _quad(ZeroExt(64, w * w))


def _prove(formula, timeout_ms=60_000):
    solver = Solver()
    solver.set(timeout=timeout_ms)
    solver.add(Not(formula))
    return solver.check()


def test_new_form_is_go_uint64_semantics():
    """`ZeroExt(64,w*w)` 除以 512 == Go 的 `square / QuadCoeffDiv`（uint64）。"""
    w = BitVec("w", 64)
    assert _prove(_new_quad(w) == LShR(w * w, BitVecVal(9, 64))) == unsat


def test_new_form_matches_x86_dividend_shape():
    """dividend 的高 64 位必须是字面 0（x86 在 DIVQ 前 `MOVQ 0, RDX`）。

    这是让 div_bridge 能 syntactic 配对的前提；simplify 后高位不是常量 0
    就说明又退回了乘法器形状。
    """
    w = BitVec("w", 64)
    assert simplify(Extract(127, 64, ZeroExt(64, w * w))) == BitVecVal(0, 64)


def test_two_forms_agree_within_protocol_cap():
    """换写法不缩小也不改变**可达域**上的义务：cap 内两式逐位相等。

    协议自身的 cap（requested ≤ 0x1FFFFFFFE0 ⟹ memWords ≤ 0xFFFFFFFF）由
    `evm_ir/semantics_gas.py::_mem_size_tail_branches` 建成真实 OUT_OF_GAS
    分支，不是 assumption。
    """
    w = BitVec("w", 64)
    in_cap = ULE(w, BitVecVal(MAX_LEGAL_WORDS, 64))
    assert _prove(Implies(in_cap, _old_quad(w) == _new_quad(w))) == unsat


def test_forms_differ_above_cap_and_go_wraps():
    """cap 外两式不等，且当前写法站在 Go 那一边。

    w = 2^32 ⟹ Go 的 uint64 `square` 回绕成 0 ⟹ quadCoef = 0；
    128-bit 精确积给 2^64/512 = 2^55。这条断言就是防回退的变异保护：
    谁把 `ZeroExt(64,w)*ZeroExt(64,w)` 改回去，这里立刻红。
    """
    w = BitVecVal(1 << 32, 64)
    assert simplify(_new_quad(w)) == BitVecVal(0, 64)
    assert simplify(_old_quad(w)) == BitVecVal(1 << 55, 64)


@pytest.mark.parametrize("requested,words", [
    (0, 0),
    (1, 1),
    (32, 1),
    (33, 2),
    (MEM_SIZE_CAP, MAX_LEGAL_WORDS),        # 最大合法 requested
    (MEM_SIZE_CAP - 31, MAX_LEGAL_WORDS),   # 同一 word 数的下边界
])
def test_fee_matches_go_reference_at_boundaries(requested, words):
    """生产函数在边界上逐值等于 Go `memoryGasCost` 的 expansion 分支。"""
    expected_total = (words * 3 + (words * words) // 512) % (1 << 64)
    fee, new_size, new_last_gas = memory_expansion_fee(
        BitVecVal(0, 64), BitVecVal(0, 64), BitVecVal(requested, 64))
    expands = words * 32 > 0
    assert simplify(new_size) == BitVecVal(words * 32 if expands else 0, 64)
    assert simplify(new_last_gas) == BitVecVal(expected_total if expands else 0, 64)
    assert simplify(fee) == BitVecVal(expected_total if expands else 0, 64)


def test_cutpoint_formula_uses_the_same_square():
    """`cutpoint_relation` 重建 lastGasCost 的公式必须与费用函数同形。

    两处漂了就是 cutpoint R 与实际 gas 演化对不上 —— 循环归纳静默降级。
    """
    from verification.cutpoint_relation import _memory_gas_cost_formula

    size = BitVec("mem_size", 64)
    w = LShR(size, BitVecVal(5, 64))
    expected = w * BitVecVal(3, 64) + _new_quad(w)
    assert _prove(_memory_gas_cost_formula(size) == expected) == unsat


def test_two_step_rounding_matches_one_step_within_cap():
    """interpreter.go rounds (SafeMul(toWordSize(r), 32)) before memoryGasCost;
    for every r <= cap and every mem.Len()/lastGasCost the three outputs equal
    the historical one-step form (r + 31) >> 5."""
    from z3 import BitVec, BitVecVal, Extract, If, LShR, Not, Or, Solver, UDiv, UGT, ULE, ZeroExt, unsat
    from evm_ir.semantics_gas import _MEM_SIZE_CAP
    from state.evm_gas_state import memory_expansion_fee
    r, size, last = BitVec("r", 64), BitVec("size", 64), BitVec("last", 64)
    words = LShR(r + 31, BitVecVal(5, 64))
    total = words * 3 + Extract(63, 0, UDiv(ZeroExt(64, words * words), BitVecVal(512, 128)))
    rounded = words << BitVecVal(5, 64)
    expands = UGT(rounded, size)
    old = (If(expands, total - last, BitVecVal(0, 64)), If(expands, rounded, size), If(expands, total, last))
    new = memory_expansion_fee(size, last, r)
    s = Solver()
    s.add(ULE(r, _MEM_SIZE_CAP), Or(*(a != b for a, b in zip(old, new))))
    assert s.check() == unsat


def test_two_step_rounding_has_the_interpreter_shape():
    from z3 import BitVec, LShR, BitVecVal, simplify
    from state.evm_gas_state import memory_expansion_fee
    r = BitVec("r", 64)
    fee, _, _ = memory_expansion_fee(BitVecVal(0, 64), BitVecVal(0, 64), r)
    memory_size = LShR(r + 31, BitVecVal(5, 64)) << BitVecVal(5, 64)
    two_step = LShR(memory_size + 31, BitVecVal(5, 64))
    assert two_step.get_id() in {t.get_id() for t in _subterms(fee)}


def _subterms(expr):
    seen, work = {}, [expr]
    while work:
        t = work.pop()
        if t.get_id() not in seen:
            seen[t.get_id()] = t
            work.extend(t.children())
    return seen.values()
