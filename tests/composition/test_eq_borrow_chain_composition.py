"""相等判断借位链桥接的组合证明。

MOD/DIV 的精化验证里，参照模型（common/arithmetic.div_semantics/mod_semantics）
始终用 Uint256.eq_semantics 的 4-limb 直接相等——这是 EVM IR 侧 EQ opcode 的真实
写法。但 x86 codegen 的 a==b / a<b 路径条件是用 sub/sbb 借位链表达的，与 4-limb
相等的 AST 不同；Z3 直接做 256-bit 借位↔limb相等的桥接推理会显著拖慢。

为提速，验证时把 ground 实例 `eq_semantics(a,b) == eq_as_borrow_chain(a,b)` 作为
solver assumption 喂入（见 common/arithmetic.eq_borrow_chain_assumption），让 solver
无需自己桥接即可对齐 x86，而参照模型保持忠实。

本文件就是那条 assumption 的信任来源：独立证明
`eq_semantics(a,b) ⟺ eq_as_borrow_chain(a,b)` 这个与具体 slice 无关的纯代数恒等式，
对全符号 256-bit 输入成立（limb 级，秒解）。
"""

import time

from z3 import And, Not, Solver, unsat

from common.arithmetic import (
    eq_as_borrow_chain,
    eq_borrow_chain_assumption,
    x86_div64_quotient_fits_assumption,
)
from common.uint256 import Uint256


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


def test_eq_semantics_equiv_borrow_chain():
    """eq_semantics(a,b) ⟺ eq_as_borrow_chain(a,b)，全符号 256-bit。"""
    x = Uint256.symbolic("eq_lemma_x")
    y = Uint256.symbolic("eq_lemma_y")
    borrow_form = And(
        Not(x.lt_semantics(y)),
        Not(y.lt_semantics(x)),
    )
    _prove(x.eq_semantics(y) == borrow_form)


def test_eq_as_borrow_chain_matches_helper():
    """eq_as_borrow_chain 的 BitVec 接口与 lemma 中的借位链形式一致。"""
    x = Uint256.symbolic("eq_helper_x")
    y = Uint256.symbolic("eq_helper_y")
    a = x.to_bv256()
    b = y.to_bv256()
    borrow_form = And(
        Not(x.lt_semantics(y)),
        Not(y.lt_semantics(x)),
    )
    _prove(eq_as_borrow_chain(a, b) == borrow_form)


def test_eq_borrow_chain_assumption_is_sound():
    """作为 solver assumption 喂入的 ground 实例本身是恒真式（即被 lemma 蕴含）。

    eq_borrow_chain_assumption(a,b) = (eq_semantics(a,b) == eq_as_borrow_chain(a,b))，
    本测试确认它对全符号输入恒成立，因此当作 assumption 注入不会引入不健全约束。
    """
    x = Uint256.symbolic("eq_assume_x")
    y = Uint256.symbolic("eq_assume_y")
    _prove(eq_borrow_chain_assumption(x.to_bv256(), y.to_bv256()))


def test_x86_div64_quotient_fits_assumption_is_sound():
    """x86 `div r64` quotient_fits hint 对全符号输入恒真。

    x86_div64_quotient_fits_assumption(a,b) =
        (b.z0 != 0 ⟹ Extract(127,64, UDiv(Concat(0,a.z0), ZeroExt(64,b.z0))) == 0)。
    它是 x86-64 refinement hint，不是 EVM DIV 语义；本测试确认注入后不限制输入。
    """
    x = Uint256.symbolic("div64_x")
    y = Uint256.symbolic("div64_y")
    _prove(x86_div64_quotient_fits_assumption(x.to_bv256(), y.to_bv256()))
