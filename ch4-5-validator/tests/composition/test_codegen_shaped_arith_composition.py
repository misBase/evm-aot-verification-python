"""按编译器形态建模的算术语义 ≡ Go 解释器语义 的组合证明。

为了让 x86 ≡ 模型 能秒证，common/ 里若干算术语义按 AOT 编译器 amd64 codegen 的形态写
（项顺序、分段、取负写法），不再逐行照抄 Go。合约验证每次证的是 x86 ≡ 模型；想要的结论
是 x86 ≡ Go 解释器，所以还缺一段 模型 ≡ Go。它与合约无关，每个 op 在这里证一次。
表格总览见同目录 README.md。

参照 G：逐行转写解释器所调的 holiman/uint256 v1.3.2 函数（instructions.go 的
opMul/opDiv/opSdiv/opMod/opSmod/opAddmod，x = 栈顶、y = 次顶）。Go 的 uint64 运算、
比较、Neg 用 Z3 原生算子；Knuth 长除法 udivrem 用与模型同一个 UF。

信任基：
  T1  _HOLIMAN_UDIV_UF / _HOLIMAN_UDIVREM_UF 就是 holiman udivrem（模型、x86 builtin
      桥接、这里的 G 共用同一个 UF）。
  T2  仅 ADDMOD：holiman Mod / udivrem 返回数学真值余数。解释器在 m≥2^192 时走 AddMod
      快路径，编译代码和模型走 Mod/udivrem；两条路线只能靠"都是真值"接上。
  W   零扩展不改变无符号除法（见 test_x86_div_form_equals_go_uint64_div）。

组合方式：内层 op 已有引理的，外层把内层换成未解释函数 F（monkeypatch），只证本层的
形态改写；F 用到的性质（除以 0 得 0 等）对真实内层函数另证。
"""

import random
import time

import pytest
from z3 import (
    And,
    BitVec,
    BitVecs,
    BitVecSort,
    BitVecVal,
    Concat,
    Extract,
    ForAll,
    Function,
    If,
    Implies,
    Not,
    Or,
    Solver,
    SolverFor,
    UDiv,
    UGE,
    UGT,
    ULE,
    ULT,
    URem,
    ZeroExt,
    eq,
    is_true,
    simplify,
    unsat,
)

from common import arithmetic
from common.arithmetic import _HOLIMAN_UDIV_UF, _HOLIMAN_UDIVREM_UF, _div_rem_64bit
from common.uint256 import Uint256
from verification.linear_encoding import lia_query

# 隔离跑最慢一条约 10 s；全量并行满载时留足余量，unknown 一律算失败。
_TIMEOUT_MS = 120_000
_ZERO = BitVecVal(0, 256)
_ONE = BitVecVal(1, 256)
_SIGN_LIMB = BitVecVal(0x8000000000000000, 64)


def _prove(claim, timeout_ms=_TIMEOUT_MS):
    """证明 claim 对全符号输入恒成立：¬claim 不可满足。"""
    solver = Solver()
    solver.set(timeout=timeout_ms)
    solver.add(Not(claim))
    start = time.time()
    result = solver.check()
    assert result == unsat, f"lemma failed: solver_result={result}, elapsed={time.time() - start:.2f}s"


def _prove_lia(claim, timeout_ms=_TIMEOUT_MS):
    """按整数线性精确读出再证；lia_query 是过近似，只有 UNSAT 能回传成 BV 结论。"""
    solver = SolverFor("QF_LIA")
    solver.set(timeout=timeout_ms)
    solver.add(lia_query(simplify(Not(claim), bv_sort_ac=True)))
    result = solver.check()
    assert result == unsat, f"lemma failed (QF_LIA): solver_result={result}"


def _inner_uf(name):
    return Function(name, BitVecSort(256), BitVecSort(256), BitVecSort(256))


# ---------------------------------------------------------------------------
# G：holiman/uint256 v1.3.2 逐行转写
# ---------------------------------------------------------------------------

def _lo(v):
    return Extract(63, 0, v)


def _go_is_uint64(z):
    """IsUint64：(z[1] | z[2] | z[3]) == 0。"""
    return Extract(255, 64, z) == 0


def _go_sign_pos(z):
    """Sign() > 0：非零且 z[3] < 0x8000000000000000。"""
    return And(z != 0, ULT(Extract(255, 192, z), _SIGN_LIMB))


def _go_sign_neg(z):
    """Sign() < 0：非零且 z[3] >= 0x8000000000000000。"""
    return And(z != 0, UGE(Extract(255, 192, z), _SIGN_LIMB))


def _go_div(x, y, div64):
    """Int.Div（uint256.go:583）；div64(x0, y0) 即 `x.Uint64() / y.Uint64()`。"""
    return If(Or(y == 0, UGT(y, x)), _ZERO,
              If(x == y, _ONE,
                 If(_go_is_uint64(x), ZeroExt(192, div64(_lo(x), _lo(y))),
                    _HOLIMAN_UDIV_UF(x, y))))


def _go_mod(x, y, rem64):
    """Int.Mod（uint256.go:605）；rem64(x0, y0) 即 `x.Uint64() % y.Uint64()`。"""
    return If(Or(y == 0, x == y), _ZERO,
              If(ULT(x, y), x,
                 If(_go_is_uint64(x), ZeroExt(192, rem64(_lo(x), _lo(y))),
                    _HOLIMAN_UDIVREM_UF(x, y))))


def _go_sdiv(n, d, div):
    """Int.SDiv（uint256.go:789），Neg(x) = 0 - x。"""
    return If(_go_sign_pos(n),
              If(_go_sign_pos(d), div(n, d), -div(n, -d)),
              If(_go_sign_neg(d), div(-n, -d), -div(-n, d)))


def _go_smod_abs(x):
    return If(_go_sign_neg(x), -x, x)


def _go_smod(x, y, mod):
    """Int.SMod（uint256.go:665）：两侧取绝对值做 Mod，结果符号跟被除数。"""
    r = mod(_go_smod_abs(x), _go_smod_abs(y))
    return If(_go_sign_neg(x), -r, r)


def _go_addmod_slow(x, y, m, mod):
    """Int.AddMod（uint256.go:215）去掉开头 m≥2^192 快路径后的部分。

    溢出支 `udivrem(quot, [5]{z0..z3, 1}, m, &rem)` 记为 257-bit URem（T2）。
    """
    total = ZeroExt(1, x) + ZeroExt(1, y)
    return If(m == 0, _ZERO,
              If(Extract(256, 256, total) == 1, Extract(255, 0, URem(total, ZeroExt(1, m))),
                 mod(Extract(255, 0, total), m)))


def _go_addmod_fast_taken(x, y, m):
    """`m[3] != 0 && x[3] <= m[3] && y[3] <= m[3]`。"""
    top = lambda v: Extract(255, 192, v)
    return And(top(m) != 0, ULE(top(x), top(m)), ULE(top(y), top(m)))


def _go_addmod_fast(x, y, m):
    """AddMod 快路径，返回 (结果, 是否直接返回 res)。

    gteC == 0（x - m 无借位）⟺ x ≥ m；`c1 == 0 && c2 != 0` ⟺ 和不溢出且 res < m。
    """
    x_red = If(UGE(x, m), x - m, x)
    y_red = If(UGE(y, m), y - m, y)
    total = ZeroExt(1, x_red) + ZeroExt(1, y_red)
    res = Extract(255, 0, total)
    keep = And(Extract(256, 256, total) == 0, ULT(res, m))
    return If(keep, res, res - m), keep


def _x86_div_rem(x, y):
    """x86 `div r64`（RDX=0）形态：被除数、除数零扩展到 2w 位相除，截低 w 位。"""
    w = x.size()
    dividend = Concat(BitVecVal(0, w), x)
    divisor = ZeroExt(w, y)
    return Extract(w - 1, 0, UDiv(dividend, divisor)), Extract(w - 1, 0, URem(dividend, divisor))


# ---------------------------------------------------------------------------
# MUL：Uint256.mul_codegen_order（项顺序按 compileEVMMul）
# ---------------------------------------------------------------------------

def test_mul_codegen_order_concrete_matches_product():
    rng = random.Random(11)
    mask = (1 << 256) - 1
    edges = [0, 1, (1 << 64) - 1, mask, 1 << 64, 1 << 192]
    values = edges + [rng.getrandbits(256) for _ in range(20)]
    for p in values:
        for q in values[:8]:
            got = Uint256.mul_codegen_order(Uint256.from_int(p), Uint256.from_int(q)).to_bv256()
            assert is_true(simplify(got == BitVecVal((p * q) & mask, 256)))


def test_mul_codegen_order_matches_go_holiman_mul():
    """opMul 是 `y.Mul(&x, y)`（x = 栈顶 a）；Uint256.mul_semantics 逐行转写 Int.Mul。

    模型 = mul_codegen_order(b, a)（evm_ir/semantics.py）。三处差异（操作数角色、umulStep
    加法顺序、顶 limb 写法）都是交换/结合律，bit-blast 证不动，按整数线性读出即秒证。
    """
    a, b = Uint256.symbolic("mul_a"), Uint256.symbolic("mul_b")
    model = Uint256.mul_codegen_order(b, a)
    go = a.mul_semantics(b)
    _prove_lia(And(*[getattr(model, f"z{i}") == getattr(go, f"z{i}") for i in range(4)]))


# ---------------------------------------------------------------------------
# DIV / MOD：64 位快路径用 x86 `div r64` 形态
# ---------------------------------------------------------------------------

def test_model_fast_path_is_x86_div_form():
    """_div_rem_64bit 与 _x86_div_rem 在 64 位上是同一棵 AST，下面 W 的证明说的就是它。"""
    x0, y0 = BitVecs("fast_x0 fast_y0", 64)
    for model_term, x86_term in zip(_div_rem_64bit(x0, y0), _x86_div_rem(x0, y0)):
        assert eq(model_term, x86_term)


def test_x86_div_form_equals_go_uint64_div():
    """W：x86 形态的商、余数 == Go 同宽 `/`、`%`。

    纸面证明（位宽无关）：按 SMT-LIB，bvudiv/bvurem 的值是 ⌊n/d⌋ / n mod d（n、d 为操作数
    的自然数值，d ≠ 0）。零扩展不改自然数值；商 ≤ n、余数 < d，都 < 2^w，截低 w 位不丢信息。
    d = 0 时两侧分别是全 1 和 x，截低 w 位后仍相等。
    机器证明只在 w = 8 上做：64 位实例要 bit-blast 两个不同位宽的除法器，Z3 30 min 仍 unknown。
    """
    x, y = BitVecs("w8_x w8_y", 8)
    q, r = _x86_div_rem(x, y)
    _prove(And(q == UDiv(x, y), r == URem(x, y)))


def test_div_matches_go_holiman_div():
    """div_semantics ≡ Int.Div，Go 的 uint64 `/` 换成模型的 x86 形态（二者相等见 W）。"""
    a, b = BitVecs("div_a div_b", 256)
    _prove(arithmetic.div_semantics(a, b) == _go_div(a, b, lambda p, q: _div_rem_64bit(p, q)[0]))


def test_mod_matches_go_holiman_mod():
    """mod_semantics ≡ Int.Mod，同上。"""
    a, b = BitVecs("mod_a mod_b", 256)
    _prove(arithmetic.mod_semantics(a, b) == _go_mod(a, b, lambda p, q: _div_rem_64bit(p, q)[1]))


def test_div_mod_zero_properties():
    """SDIV/SMOD 引理里 F 用到的性质，对真实 div/mod_semantics 成立。"""
    x = BitVec("zero_x", 256)
    _prove(And(arithmetic.div_semantics(x, _ZERO) == _ZERO,
               arithmetic.div_semantics(_ZERO, x) == _ZERO,
               arithmetic.mod_semantics(x, _ZERO) == _ZERO))


# ---------------------------------------------------------------------------
# SDIV / SMOD：_abs256 用 limb 借位减法，符号分类与 Go 的 Sign() 嵌套不同
# ---------------------------------------------------------------------------

def test_sdiv_matches_go_holiman_sdiv(monkeypatch):
    """sdiv_semantics ≡ Int.SDiv，内层 Div 抽象为 F（F 取 div_semantics 时由 DIV 引理接上）。

    F 必须满足 F(x,0)=0 与 F(0,y)=0：被除数为 0、除数为负时 Go 给 +F(0,|d|)、模型给
    -F(0,|d|)，只有 F(0,y)=0 才相等（去掉这条前提 Z3 给 SAT）。
    """
    inner = _inner_uf("sdiv_inner_div")
    monkeypatch.setattr(arithmetic, "div_semantics", inner)
    a, b = BitVecs("sdiv_a sdiv_b", 256)
    v = BitVec("sdiv_v", 256)
    inner_zero = And(ForAll([v], inner(v, _ZERO) == _ZERO), ForAll([v], inner(_ZERO, v) == _ZERO))
    _prove(Implies(inner_zero, arithmetic.sdiv_semantics(a, b) == _go_sdiv(a, b, inner)))


def test_smod_matches_go_holiman_smod(monkeypatch):
    """smod_semantics ≡ Int.SMod，内层 Mod 抽象为 F；只需 F(|a|, 0) = 0 一个实例。"""
    inner = _inner_uf("smod_inner_mod")
    monkeypatch.setattr(arithmetic, "mod_semantics", inner)
    a, b = BitVecs("smod_a smod_b", 256)
    _prove(Implies(inner(_go_smod_abs(a), _ZERO) == _ZERO,
                   arithmetic.smod_semantics(a, b) == _go_smod(a, b, inner)))


# ---------------------------------------------------------------------------
# ADDMOD：分段按 compileEVMAddMod，没有 holiman 的 m≥2^192 快路径
# ---------------------------------------------------------------------------

def test_addmod_matches_go_holiman_addmod_without_fast_path(monkeypatch):
    """addmod_semantics ≡ Int.AddMod 删去快路径的部分，内层 Mod 抽象为 F。"""
    inner = _inner_uf("addmod_inner_mod")
    monkeypatch.setattr(arithmetic, "mod_semantics", inner)
    a, b, m = BitVecs("addmod_a addmod_b addmod_m", 256)
    _prove(arithmetic.addmod_semantics(a, b, m) == _go_addmod_slow(a, b, m, inner))


def test_addmod_go_fast_path_returns_true_remainder():
    """快路径结果 r 满足 r < m 且 a + b = r + k·m（k 按三次减 m 显式给出）。

    欧几里得除法余数唯一，故 r 就是 (a+b) mod m；删去快路径的部分在 T2 下也是它，
    所以模型（≡ 删去快路径的部分）在快路径区域同样等于 Go。
    """
    a, b, m = BitVecs("fast_a fast_b fast_m", 256)
    r, keep = _go_addmod_fast(a, b, m)
    wide = lambda v: ZeroExt(2, v)
    none = BitVecVal(0, 258)
    multiples = (If(UGE(a, m), wide(m), none) + If(UGE(b, m), wide(m), none)
                 + If(keep, none, wide(m)))
    _prove_lia(Implies(_go_addmod_fast_taken(a, b, m),
                       And(ULT(r, m), wide(a) + wide(b) == wide(r) + multiples)))
