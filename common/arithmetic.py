"""EVM 算术操作的 Z3 语义函数。

操作 BitVec(256)，无状态，供 evm_ir 和 x86_64 两侧共用。
"""
from z3 import (
    And,
    BitVecVal,
    Concat,
    Extract,
    Function,
    BitVecSort,
    If,
    Implies,
    Not,
    Or,
    UDiv,
    URem,
    ZeroExt,
    is_bv_value,
    simplify,
)


# go-hpc-evm 的 builtin div/mod 实际调用 github.com/holiman/uint256 v1.3.2 的
# Int.Div / Int.Mod，而 amd64 AOT codegen 就是这两个函数的逐分支翻译。两侧若都
# 建模成裸 z3 bvurem/bvudiv，refinement 公式会让 Z3 bit-blast 256-bit 除法而超时
# （实测 192-bit 起就 unknown）。这里改为镜像 holiman 的分段实现：快路径用 limb
# 比较/64-bit 运算展开（Z3 秒解，且与 x86 codegen 逐路径结构对齐），仅大数 Knuth
# 长除法路径折成未解释函数。大数路径 x86（经 builtin bridge）与 EVM 参照都调用同一
# holiman udivrem，折同一 UF 即保证 x86 ≡ EVM（不证 ≡ 数学真值）。
#
# Latent gap（当前不可触发）：商和余数是**两个独立 UF**，二者无 q·b+r==a 公理。
# 单指令 refinement 里 DIV/MOD 各用独立 solver，同一 solver 不会同时出现两个 UF，故
# 当前安全。但若某个多指令程序对同一 (a,b) 同时含 DIV 与 MOD、且 observable 依赖两者，
# Z3 可取 quotient/remainder 数学不一致的模型而各自 refinement 仍 pass。届时需改为单一
# udivrem UF 返回 (q,r) 再投影，或补 q·b+r==a 一致性公理。
_HOLIMAN_UDIVREM_UF = Function(
    "holiman_udivrem", BitVecSort(256), BitVecSort(256), BitVecSort(256)
)
_HOLIMAN_UDIV_UF = Function(
    "holiman_udiv", BitVecSort(256), BitVecSort(256), BitVecSort(256)
)

_ZERO256 = BitVecVal(0, 256)
_ONE256 = BitVecVal(1, 256)


def _is_uint64(value):
    """对齐 holiman Int.IsUint64：高 192 位为 0。"""
    return Extract(255, 64, value) == BitVecVal(0, 192)


def eq_as_borrow_chain(a, b):
    """把 a == b 表达成借位链形式 ¬(a<b) ∧ ¬(b<a)（a/b 为 BitVec(256)）。

    **不是**参照语义——参照（div/mod_semantics、EQ opcode）始终用 Uint256.eq_semantics
    的 4-limb 直接相等，那才是 IR 真实写法。这里只提供一个与之等价、但与 x86 codegen
    同源的形式：x86 的 a==b/a<b 路径条件是用 sub/sbb 借位链表达的，与 4-limb 相等的
    AST 不同，Z3 要做 256-bit 借位↔limb相等的桥接推理而显著拖慢（实测 MOD 的 a==b
    路径单条 ~4.7s）。

    `a == b ⟺ ¬(a<b) ∧ ¬(b<a)` 的等价性由 tests/composition 的 composition lemma
    独立证明（limb 级，秒解）。验证时可把该 lemma 的 ground 实例
    `eq_semantics(a,b) == eq_as_borrow_chain(a,b)` 作为 assumption 喂给 solver，让它无需
    自己桥接即可对齐 x86，而参照模型本身保持忠实。
    """
    from common.uint256 import Uint256

    x = Uint256.from_bv256(a)
    y = Uint256.from_bv256(b)
    return And(Not(x.lt_semantics(y)), Not(y.lt_semantics(x)))


def eq_borrow_chain_assumption(a, b):
    """返回 ground 实例 `eq_semantics(a,b) == eq_as_borrow_chain(a,b)`。

    供 refinement 验证作为 solver assumption 使用（等价性已由 composition lemma
    证明）。a/b 为 BitVec(256)。
    """
    from common.uint256 import Uint256

    x = Uint256.from_bv256(a)
    y = Uint256.from_bv256(b)
    return x.eq_semantics(y) == eq_as_borrow_chain(a, b)


def _div_rem_64bit_128(x_low, y_low):
    """返回 x86 `div r64` 快路径的 128-bit 商/余数（未截断）。

    x86 codegen 的 0xe6 段是 `mov rdx,0; mov rax,x0; div y0`，按
    x86_64/semantics.py 的 div 建模即 dividend=Concat(RDX=0, RAX=x0)，
    divisor128=ZeroExt(64, y0)。这里返回 128-bit 的 q128/r128，供 _div_rem_64bit
    与 x86_div64_quotient_fits_assumption 复用同一份 AST。
    """
    dividend = Concat(BitVecVal(0, 64), x_low)
    divisor128 = ZeroExt(64, y_low)
    return UDiv(dividend, divisor128), URem(dividend, divisor128)


def _div_rem_64bit(x_low, y_low):
    """镜像 x86 `div r64` 在 64-bit 快路径产出的商/余数 AST。

    取 _div_rem_64bit_128 的低 64 位。EVM 参照镜像同一表达式，使两侧 AST 逐字
    一致、无需 Z3 推理 bvudiv 性质即可对齐。
    """
    quotient128, remainder128 = _div_rem_64bit_128(x_low, y_low)
    return Extract(63, 0, quotient128), Extract(63, 0, remainder128)


def x86_div64_quotient_fits_assumption(a, b):
    """x86 `div r64` quotient_fits guard 的恒真 ground 实例（a/b 为 BitVec(256)）。

    当前 x86 后端 64-bit DIV 快路径会生成 `RDX=0; RAX=x.z0; div y.z0`。
    因此 y.z0 != 0 时，q128 高 64 位必为 0，可满足 x86 语义里的 quotient_fits。

    这不是 EVM DIV 语义的一部分，只是 refinement solver hint：避免 Z3 自己证明
    该 x86 guard，从而提速当前 x86-64 codegen 形状。

    守卫只能是 `y.z0 != 0`：q128 只取 x.z0，与 a 高 192 位无关；不可用 IsUint64(a)。
    """
    from common.uint256 import Uint256

    x = Uint256.from_bv256(a)
    y = Uint256.from_bv256(b)
    quotient128, _ = _div_rem_64bit_128(x.z0, y.z0)
    return Implies(
        y.z0 != BitVecVal(0, 64),
        Extract(127, 64, quotient128) == BitVecVal(0, 64),
    )


def div_semantics(a, b):
    """EVM DIV: a / b，b==0时返回0。

    分段对齐 holiman uint256 v1.3.2 Int.Div：
      y.IsZero() || y.Gt(x) -> 0;  x.Eq(y) -> 1;  x.IsUint64() -> x0/y0(64-bit);
      else -> 未解释函数（Knuth 长除法）。
    """
    from common.uint256 import Uint256

    x = Uint256.from_bv256(a)
    y = Uint256.from_bv256(b)
    quotient64, _ = _div_rem_64bit(x.z0, y.z0)
    return If(
        Or(y.iszero_semantics(), y.gt_semantics(x)),
        _ZERO256,
        If(
            x.eq_semantics(y),
            _ONE256,
            If(
                _is_uint64(a),
                ZeroExt(192, quotient64),
                _HOLIMAN_UDIV_UF(a, b),
            ),
        ),
    )


def mod_semantics(a, b):
    """EVM MOD: a % b，b==0时返回0。

    分段对齐 holiman uint256 v1.3.2 Int.Mod：
      y.IsZero() || x.Eq(y) -> 0;  x.Lt(y) -> x;  x.IsUint64() -> x0%y0(64-bit);
      else -> 未解释函数（Knuth 长除法）。
    """
    from common.uint256 import Uint256

    x = Uint256.from_bv256(a)
    y = Uint256.from_bv256(b)
    _, remainder64 = _div_rem_64bit(x.z0, y.z0)
    return If(
        Or(y.iszero_semantics(), x.eq_semantics(y)),
        _ZERO256,
        If(
            x.lt_semantics(y),
            a,
            If(
                _is_uint64(a),
                ZeroExt(192, remainder64),
                _HOLIMAN_UDIVREM_UF(a, b),
            ),
        ),
    )


def _is_negative(value):
    """有符号 256-bit：符号位（bit 255）为 1 即为负。对齐 x86 `SHRQ 63` 取最高 limb 符号位。"""
    return Extract(255, 255, value) == BitVecVal(1, 1)


def _abs256(value):
    """有符号绝对值：负数取 0-value，非负原样。

    取负**用 limb 级带借位减法**（Uint256(0).sub_semantics(x)），而非 256-bit `0-value`。
    原因：x86 codegen 的 compileZeroSubWithTmpReg 是 4 条 SUBQ/SBBQ（逐 limb 0-z 带借位
    链），其除法实参就是这个 limb 形式。EVM 侧若用 `0-value`，z3 渲染成 (2^256-1)*value
    乘法形式，与 x86 limb 形式 AST 不一致，导致 SDIV/SMOD 大数路径两侧 div 实参无法 unify、
    Z3 被迫 bit-blast 256-bit 除法而 unknown。改 limb 级后两侧 `0-x` AST 同构，div 实参
    直接对齐。

    MIN_INT256(0x8000..0) 的 |value| 仍等于自身（两侧同样 wrap），被后续 unsigned div/mod
    当作 2^255 处理——与 x86 及 holiman S256/Abs 一致（同构，不证 ≡ 数学真值）。
    """
    from common.uint256 import Uint256

    x = Uint256.from_bv256(value)
    zero = Uint256(
        BitVecVal(0, 64), BitVecVal(0, 64), BitVecVal(0, 64), BitVecVal(0, 64)
    )
    negated = zero.sub_semantics(x).to_bv256()
    return If(_is_negative(value), negated, value)


def sdiv_semantics(a, b):
    """EVM SDIV: 有符号 a / b，b==0时返回0。

    镜像 holiman uint256 Int.SDiv（参照对象就是它，非黄皮书裸 bvsdiv）：
      y==0 -> 0;  否则 sign = (sign(x)==sign(y)) ? +1 : -1，结果 = sign * (|x| / |y|)。
    x86 codegen（compileEVMSDiv）是同一套符号分类树，内部调 unsigned DIV
    （compileEVMDivWithReg）。复用 div_semantics 使两侧大数路径折成同一
    _HOLIMAN_UDIV_UF，避免 Z3 bit-blast 256-bit bvsdiv 超时。
    """
    quotient_abs = div_semantics(_abs256(a), _abs256(b))
    same_sign = _is_negative(a) == _is_negative(b)
    return If(
        b == _ZERO256,
        _ZERO256,
        If(same_sign, quotient_abs, _ZERO256 - quotient_abs),
    )


def smod_semantics(a, b):
    """EVM SMOD: 有符号 a % b，b==0时返回0。

    镜像 holiman uint256 Int.SMod（参照对象就是它）：
      y==0 -> 0;  否则 neg = sign(x)<0，结果 = neg ? -(|x| % |y|) : (|x| % |y|)。
    余数符号只取被除数 x 的符号。x86 codegen（compileEVMSMod）同构，内部调 unsigned
    MOD（compileEVMModWithReg）；复用 mod_semantics 折同一 _HOLIMAN_UDIVREM_UF。
    """
    remainder_abs = mod_semantics(_abs256(a), _abs256(b))
    return If(
        b == _ZERO256,
        _ZERO256,
        If(_is_negative(a), _ZERO256 - remainder_abs, remainder_abs),
    )


def sdiv_speedup_assumptions(a, b):
    """SDIV refinement 的恒真提速 hint（soundness 中性）。

    SDIV 内部把 (a,b) 取绝对值后喂给 unsigned div_semantics，x86 codegen 同样在
    |a|、|b| 上跑 unsigned DIV codegen。因此 DIV 的两条 ground hint（相等借位链桥接、
    x86 `div r64` quotient_fits guard）应挂在 _abs256(a)、_abs256(b) 上，而非原始
    (a,b)，否则对 SDIV 的 unsigned 子路径不起作用、solver 仍 bit-blast 64-bit 快路径
    商而 unknown。两条都是对任意 256-bit 输入恒真的 lemma，挂 ITE 形式的绝对值同样恒真。
    """
    abs_a = _abs256(a)
    abs_b = _abs256(b)
    return [
        eq_borrow_chain_assumption(abs_a, abs_b),
        x86_div64_quotient_fits_assumption(abs_a, abs_b),
    ]


def smod_speedup_assumptions(a, b):
    """SMOD refinement 的恒真提速 hint（soundness 中性）。

    同 sdiv_speedup_assumptions，但 SMOD 内部走 unsigned mod_semantics（无 `div r64`
    快路径商），故只需相等借位链桥接 hint。
    """
    return [eq_borrow_chain_assumption(_abs256(a), _abs256(b))]


def exp_semantics(base, exponent):
    """EVM EXP: base^exponent，常见常量指数直接折叠，其余使用未解释函数。"""
    exponent_simplified = simplify(exponent)
    if is_bv_value(exponent_simplified):
        exponent_value = exponent_simplified.as_long()
        if exponent_value == 0:
            return BitVecVal(1, 256)
        if exponent_value == 1:
            return base
    exp_func = Function('evm_exp', BitVecSort(256), BitVecSort(256), BitVecSort(256))
    return exp_func(base, exponent)


def addmod_semantics(a, b, mod):
    """EVM ADDMOD: (a + b) % mod，mod==0时返回0。"""
    zero = BitVecVal(0, 256)
    a_ext = ZeroExt(1, a)
    b_ext = ZeroExt(1, b)
    mod_ext = ZeroExt(1, mod)
    res_ext = URem(a_ext + b_ext, mod_ext)
    return If(mod == zero, zero, Extract(255, 0, res_ext))


def mulmod_semantics(a, b, mod):
    """EVM MULMOD: (a * b) % mod，mod==0时返回0。"""
    zero = BitVecVal(0, 256)
    a_ext = ZeroExt(256, a)
    b_ext = ZeroExt(256, b)
    mod_ext = ZeroExt(256, mod)
    res_ext = URem(a_ext * b_ext, mod_ext)
    return If(mod == zero, zero, Extract(255, 0, res_ext))
