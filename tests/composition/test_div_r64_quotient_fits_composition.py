"""x86 `div r64` 快路径 quotient_fits inline hint 的组合证明。

x86_64/semantics.py 的 div 建模在 RDX=0 的快路径上就地挂了一条恒真提速 hint
（x86_64/semantics.py:1276）：

    Implies(And(old_rdx == 0, divisor != 0),
            Extract(127, 64, UDiv(Concat(old_rdx, old_rax), ZeroExt(64, divisor))) == 0)

它让 Z3 跳过对 128-bit 商高 64 位的 bit-blast。这条 inline hint 与 EVM 侧 helper
common/arithmetic.x86_div64_quotient_fits_assumption 是**两份不同的 AST**：helper 的
守卫是 `y.z0 != 0`、从 BitVec(256) 提 z0 构造；inline 的守卫是 `rdx == 0 ∧ divisor
!= 0`、用本指令的 RAX/RDX/divisor 寄存器值就地构造。helper 已被
test_eq_borrow_chain_composition.py 覆盖，inline 这条没有任何测试直接覆盖。

本文件是那条 inline hint 的信任来源：重构一份与 semantics.py:1276 逐字同构的 hint，
独立证明它对全符号 64-bit 寄存器输入恒真。守卫只能是 `rdx == 0 ∧ divisor != 0`——
若未来有人改错（如换成 IsUint64），结论将非恒真、本测试会 SAT 抓到回归，防止假绿。
"""

import time

from z3 import (
    And,
    BitVec,
    BitVecVal,
    Concat,
    Extract,
    Implies,
    Not,
    Solver,
    UDiv,
    ZeroExt,
    unsat,
)


def _prove(claim):
    """证明 claim 对全符号输入恒成立：¬claim 不可满足。"""
    solver = Solver()
    solver.set(timeout=10_000)
    solver.add(Not(claim))
    start = time.time()
    result = solver.check()
    elapsed = time.time() - start
    assert result == unsat, (
        f"composition lemma failed: solver_result={result}, elapsed={elapsed:.2f}s"
    )


def test_x86_div_r64_quotient_fits_hint_is_sound():
    """x86 `div r64` 快路径 inline quotient_fits hint 对全符号输入恒真。

    与 x86_64/semantics.py:1276 逐字同构地重构 hint：dividend=Concat(rdx, rax)、
    divisor128=ZeroExt(64, divisor)、q128=UDiv(dividend, divisor128)，守卫
    rdx==0 ∧ divisor!=0，结论 Extract(127,64,q128)==0。

    论证：rdx==0 ⟹ dividend = Concat(0, rax) < 2^64；divisor!=0 ⟹ divisor128 >= 1；
    故 q128 = dividend / divisor128 < 2^64 ⟹ 高 64 位必为 0。
    """
    old_rax = BitVec("div64_rax", 64)
    old_rdx = BitVec("div64_rdx", 64)
    divisor = BitVec("div64_divisor", 64)

    dividend = Concat(old_rdx, old_rax)
    divisor128 = ZeroExt(64, divisor)
    q128 = UDiv(dividend, divisor128)

    quotient_fits = Extract(127, 64, q128) == BitVecVal(0, 64)
    divisor_non_zero = divisor != BitVecVal(0, 64)
    hint = Implies(
        And(old_rdx == BitVecVal(0, 64), divisor_non_zero),
        quotient_fits,
    )
    _prove(hint)
