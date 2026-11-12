#!/usr/bin/env python3
"""
Uint256 单元测试 - 测试所有语义操作的正确性。

这些测试使用具体数值验证 Uint256 的语义操作与 Go 的 holiman/uint256 实现一致。
"""

import pytest
from z3 import BitVec, BitVecVal, Not, Solver, UGT, ULT, simplify, unsat

from common.uint256 import Uint256


UINT64_MASK = (1 << 64) - 1
UINT256_MASK = (1 << 256) - 1


def assert_uint256_equals_int(actual: Uint256, expected: int):
    expected &= UINT256_MASK
    assert simplify(actual.z0 == BitVecVal(expected & UINT64_MASK, 64))
    assert simplify(actual.z1 == BitVecVal((expected >> 64) & UINT64_MASK, 64))
    assert simplify(actual.z2 == BitVecVal((expected >> 128) & UINT64_MASK, 64))
    assert simplify(actual.z3 == BitVecVal((expected >> 192) & UINT64_MASK, 64))


class TestUint256AddSemantics:
    """测试 add_semantics() 方法。"""

    def test_add_simple(self):
        """简单加法（无进位）：1 + 1 = 2"""
        val1 = Uint256.from_int(1)
        val2 = Uint256.from_int(1)
        result = val1.add_semantics(val2)
        expected = Uint256.from_int(2)
        assert simplify(result.z0 == expected.z0)
        assert simplify(result.z1 == expected.z1)

    def test_add_cross_limb_carry(self):
        """跨 limb 加法（有进位）：2^64 - 1 + 1 = 2^64"""
        val1 = Uint256.from_int(0xFFFFFFFFFFFFFFFF)
        val2 = Uint256.from_int(1)
        result = val1.add_semantics(val2)

        # 结果应该是 [0, 1, 0, 0]
        assert simplify(result.z0 == 0)
        assert simplify(result.z1 == 1)
        assert simplify(result.z2 == 0)
        assert simplify(result.z3 == 0)

    def test_add_zeros(self):
        """全 0 加法：0 + 0 = 0"""
        val1 = Uint256.from_int(0)
        val2 = Uint256.from_int(0)
        result = val1.add_semantics(val2)
        expected = Uint256.from_int(0)
        assert simplify(result.z0 == expected.z0)

    def test_add_overflow(self):
        """最大值加法（溢出）：2^256 - 1 + 1 = 0"""
        # 2^256 - 1 = 所有 limb 都是 0xFFFFFFFFFFFFFFFF
        val1 = Uint256(
            BitVecVal(0xFFFFFFFFFFFFFFFF, 64),
            BitVecVal(0xFFFFFFFFFFFFFFFF, 64),
            BitVecVal(0xFFFFFFFFFFFFFFFF, 64),
            BitVecVal(0xFFFFFFFFFFFFFFFF, 64)
        )
        val2 = Uint256.from_int(1)
        result = val1.add_semantics(val2)

        # 溢出后应该全为 0
        assert simplify(result.z0 == 0)
        assert simplify(result.z1 == 0)
        assert simplify(result.z2 == 0)
        assert simplify(result.z3 == 0)

    def test_add_multi_limb_carry(self):
        """多 limb 进位：2^128 - 1 + 1 = 2^128"""
        val1 = Uint256(
            BitVecVal(0xFFFFFFFFFFFFFFFF, 64),
            BitVecVal(0xFFFFFFFFFFFFFFFF, 64),
            BitVecVal(0, 64),
            BitVecVal(0, 64)
        )
        val2 = Uint256.from_int(1)
        result = val1.add_semantics(val2)

        # 结果应该是 [0, 0, 1, 0]
        assert simplify(result.z0 == 0)
        assert simplify(result.z1 == 0)
        assert simplify(result.z2 == 1)
        assert simplify(result.z3 == 0)


class TestUint256SubSemantics:
    """测试 sub_semantics() 方法。"""

    def test_sub_simple(self):
        """简单减法（无借位）：5 - 3 = 2"""
        val1 = Uint256.from_int(5)
        val2 = Uint256.from_int(3)
        result = val1.sub_semantics(val2)
        expected = Uint256.from_int(2)
        assert simplify(result.z0 == expected.z0)

    def test_sub_cross_limb_borrow(self):
        """跨 limb 减法（有借位）：2^64 - 1"""
        # 2^64 表示为 [0, 1, 0, 0]
        val1 = Uint256(
            BitVecVal(0, 64),
            BitVecVal(1, 64),
            BitVecVal(0, 64),
            BitVecVal(0, 64)
        )
        val2 = Uint256.from_int(1)
        result = val1.sub_semantics(val2)

        # 结果应该是 2^64 - 1 = [0xFFFFFFFFFFFFFFFF, 0, 0, 0]
        expected = Uint256.from_int(0xFFFFFFFFFFFFFFFF)
        assert simplify(result.z0 == expected.z0)
        assert simplify(result.z1 == expected.z1)

    def test_sub_zeros(self):
        """全 0 减法：0 - 0 = 0"""
        val1 = Uint256.from_int(0)
        val2 = Uint256.from_int(0)
        result = val1.sub_semantics(val2)
        expected = Uint256.from_int(0)
        assert simplify(result.z0 == expected.z0)

    def test_sub_underflow(self):
        """下溢（借位传播）：0 - 1 = 2^256 - 1"""
        val1 = Uint256.from_int(0)
        val2 = Uint256.from_int(1)
        result = val1.sub_semantics(val2)

        # 结果应该是 2^256 - 1（全 1）
        assert simplify(result.z0 == 0xFFFFFFFFFFFFFFFF)
        assert simplify(result.z1 == 0xFFFFFFFFFFFFFFFF)
        assert simplify(result.z2 == 0xFFFFFFFFFFFFFFFF)
        assert simplify(result.z3 == 0xFFFFFFFFFFFFFFFF)

    def test_sub_multi_limb_borrow(self):
        """多 limb 借位：1 - 2^64"""
        # 1 = [1, 0, 0, 0], 2^64 = [0, 1, 0, 0]
        val1 = Uint256.from_int(1)
        val2 = Uint256(
            BitVecVal(0, 64),
            BitVecVal(1, 64),
            BitVecVal(0, 64),
            BitVecVal(0, 64)
        )
        result = val1.sub_semantics(val2)

        # 结果应该是 1 - 2^64 = 2^256 - 2^64 + 1
        # 即 [1, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF]
        assert simplify(result.z0 == 1)
        assert simplify(result.z1 == 0xFFFFFFFFFFFFFFFF)
        assert simplify(result.z2 == 0xFFFFFFFFFFFFFFFF)
        assert simplify(result.z3 == 0xFFFFFFFFFFFFFFFF)

    def test_sub_boundary(self):
        """边界情况：2^128 - 2^64 = 2^64 * (2^64 - 1)"""
        val1 = Uint256(
            BitVecVal(0, 64),
            BitVecVal(0, 64),
            BitVecVal(1, 64),
            BitVecVal(0, 64)
        )
        val2 = Uint256(
            BitVecVal(0, 64),
            BitVecVal(1, 64),
            BitVecVal(0, 64),
            BitVecVal(0, 64)
        )
        result = val1.sub_semantics(val2)

        # 结果应该是 [0, 0xFFFFFFFFFFFFFFFF, 0, 0]
        assert simplify(result.z0 == 0)
        assert simplify(result.z1 == 0xFFFFFFFFFFFFFFFF)
        assert simplify(result.z2 == 0)
        assert simplify(result.z3 == 0)


class TestUint256MulSemantics:
    """测试 mul_semantics() 方法。"""

    def test_mul_simple(self):
        """简单乘法：2 * 3 = 6"""
        val1 = Uint256.from_int(2)
        val2 = Uint256.from_int(3)
        result = val1.mul_semantics(val2)
        expected = Uint256.from_int(6)
        assert simplify(result.z0 == expected.z0)

    def test_mul_large_numbers(self):
        """大数乘法：2^32 * 2^32 = 2^64"""
        val1 = Uint256.from_int(2**32)
        val2 = Uint256.from_int(2**32)
        result = val1.mul_semantics(val2)

        # 结果应该是 2^64 = [0, 1, 0, 0]
        assert simplify(result.z0 == 0)
        assert simplify(result.z1 == 1)
        assert simplify(result.z2 == 0)
        assert simplify(result.z3 == 0)

    def test_mul_by_zero(self):
        """零乘法：12345 * 0 = 0"""
        val1 = Uint256.from_int(12345)
        val2 = Uint256.from_int(0)
        result = val1.mul_semantics(val2)
        expected = Uint256.from_int(0)
        assert simplify(result.z0 == expected.z0)

    def test_mul_overflow(self):
        """溢出乘法：2^128 * 2^128 结果截断为 0"""
        val1 = Uint256(
            BitVecVal(0, 64),
            BitVecVal(0, 64),
            BitVecVal(1, 64),
            BitVecVal(0, 64)
        )
        val2 = Uint256(
            BitVecVal(0, 64),
            BitVecVal(0, 64),
            BitVecVal(1, 64),
            BitVecVal(0, 64)
        )
        result = val1.mul_semantics(val2)

        # 2^128 * 2^128 = 2^256，模 2^256 后为 0
        assert simplify(result.z0 == 0)
        assert simplify(result.z1 == 0)
        assert simplify(result.z2 == 0)
        assert simplify(result.z3 == 0)

    @pytest.mark.parametrize(
        "left,right",
        [
            ((1 << 64) - 1, (1 << 64) - 1),
            ((1 << 256) - 1, (1 << 256) - 1),
            (
                0x0123456789ABCDEF_FEDCBA9876543210_1111222233334444_5555666677778888,
                0xFFEEDDCCBBAA9988_7766554433221100_0123456789ABCDEF_F0E1D2C3B4A59687,
            ),
            (
                (1 << 192) + (3 << 128) + (5 << 64) + 7,
                (11 << 192) + (13 << 128) + (17 << 64) + 19,
            ),
        ],
    )
    def test_mul_matches_modulo_256_product_across_limbs(self, left, right):
        """多 limb 乘法应等价于 Python 整数乘积截断到 256 位。"""
        result = Uint256.from_int(left).mul_semantics(Uint256.from_int(right))
        assert_uint256_equals_int(result, left * right)


class TestUint256BitwiseSemantics:
    """测试位运算操作。"""

    def test_and_simple(self):
        """AND 操作：0xFF & 0x0F = 0x0F"""
        val1 = Uint256.from_int(0xFF)
        val2 = Uint256.from_int(0x0F)
        result = val1.and_semantics(val2)
        expected = Uint256.from_int(0x0F)
        assert simplify(result.z0 == expected.z0)

    def test_and_zeros(self):
        """AND 全 0：0xFFFFFFFFFFFFFFFF & 0 = 0"""
        val1 = Uint256.from_int(0xFFFFFFFFFFFFFFFF)
        val2 = Uint256.from_int(0)
        result = val1.and_semantics(val2)
        expected = Uint256.from_int(0)
        assert simplify(result.z0 == expected.z0)

    def test_and_ones(self):
        """AND 全 1：x & 0xFFFFFFFFFFFFFFFF = x（对于单个 limb）"""
        val1 = Uint256.from_int(0x123456789ABCDEF0)
        val2 = Uint256.from_int(0xFFFFFFFFFFFFFFFF)
        result = val1.and_semantics(val2)
        assert simplify(result.z0 == val1.z0)

    def test_or_simple(self):
        """OR 操作：0xF0 | 0x0F = 0xFF"""
        val1 = Uint256.from_int(0xF0)
        val2 = Uint256.from_int(0x0F)
        result = val1.or_semantics(val2)
        expected = Uint256.from_int(0xFF)
        assert simplify(result.z0 == expected.z0)

    def test_or_zeros(self):
        """OR 全 0：x | 0 = x"""
        val1 = Uint256.from_int(12345)
        val2 = Uint256.from_int(0)
        result = val1.or_semantics(val2)
        assert simplify(result.z0 == val1.z0)

    def test_or_ones(self):
        """OR 全 1：x | 0xFFFFFFFFFFFFFFFF = 0xFFFFFFFFFFFFFFFF"""
        val1 = Uint256.from_int(0x123456789ABCDEF0)
        val2 = Uint256.from_int(0xFFFFFFFFFFFFFFFF)
        result = val1.or_semantics(val2)
        expected = Uint256.from_int(0xFFFFFFFFFFFFFFFF)
        assert simplify(result.z0 == expected.z0)

    def test_xor_same(self):
        """XOR 相同值：x ^ x = 0"""
        val1 = Uint256.from_int(0x123456789ABCDEF0)
        result = val1.xor_semantics(val1)
        expected = Uint256.from_int(0)
        assert simplify(result.z0 == expected.z0)

    def test_xor_different(self):
        """XOR 不同值：0xFF ^ 0xFF = 0, 0xF0 ^ 0x0F = 0xFF"""
        val1 = Uint256.from_int(0xF0)
        val2 = Uint256.from_int(0x0F)
        result = val1.xor_semantics(val2)
        expected = Uint256.from_int(0xFF)
        assert simplify(result.z0 == expected.z0)

    def test_not_zero(self):
        """NOT 零：~0 = 0xFFFFFFFFFFFFFFFF"""
        val1 = Uint256.from_int(0)
        result = val1.not_semantics()
        expected = Uint256.from_int(0xFFFFFFFFFFFFFFFF)
        assert simplify(result.z0 == expected.z0)

    def test_not_ones(self):
        """NOT 全 1：~0xFFFFFFFFFFFFFFFF = 0"""
        val1 = Uint256.from_int(0xFFFFFFFFFFFFFFFF)
        result = val1.not_semantics()
        expected = Uint256.from_int(0)
        assert simplify(result.z0 == expected.z0)

    def test_not_mixed(self):
        """NOT 混合值：~0x00FF00FF = 0xFFFFFFFFFF00FF00（64位）"""
        val1 = Uint256.from_int(0x00FF00FF)
        result = val1.not_semantics()
        expected = Uint256.from_int(0xFFFFFFFFFF00FF00)
        assert simplify(result.z0 == expected.z0)


class TestUint256ComparisonSemantics:
    """测试比较操作。"""

    def test_lt_less_than(self):
        """LT 小于：1 < 5 为 True"""
        val1 = Uint256.from_int(1)
        val2 = Uint256.from_int(5)
        result = val1.lt_semantics(val2)
        # result 是一个 Z3 Bool 表达式，需要用 simplify 验证
        assert simplify(result)

    def test_lt_equal(self):
        """LT 相等：5 < 5 为 False"""
        val1 = Uint256.from_int(5)
        val2 = Uint256.from_int(5)
        result = val1.lt_semantics(val2)
        assert not simplify(result)

    def test_lt_greater(self):
        """LT 大于：5 < 1 为 False"""
        val1 = Uint256.from_int(5)
        val2 = Uint256.from_int(1)
        result = val1.lt_semantics(val2)
        assert not simplify(result)

    def test_lt_cross_limb_borrow_order(self):
        """LT 跨 limb：低 limb 局部比较不能覆盖高 limb。"""
        assert simplify(Uint256.from_int((1 << 64) - 1).lt_semantics(Uint256.from_int(1 << 64)))
        assert not simplify(Uint256.from_int(1 << 64).lt_semantics(Uint256.from_int((1 << 64) - 1)))

    def test_gt_less_than(self):
        """GT 小于：1 > 5 为 False"""
        val1 = Uint256.from_int(1)
        val2 = Uint256.from_int(5)
        result = val1.gt_semantics(val2)
        assert not simplify(result)

    def test_gt_equal(self):
        """GT 相等：5 > 5 为 False"""
        val1 = Uint256.from_int(5)
        val2 = Uint256.from_int(5)
        result = val1.gt_semantics(val2)
        assert not simplify(result)

    def test_gt_greater(self):
        """GT 大于：5 > 1 为 True"""
        val1 = Uint256.from_int(5)
        val2 = Uint256.from_int(1)
        result = val1.gt_semantics(val2)
        assert simplify(result)

    def test_slt_cross_sign(self):
        """SLT 跨符号：-1 < 1 为 True，1 < -1 为 False。"""
        neg_one = Uint256.from_int(UINT256_MASK)
        pos_one = Uint256.from_int(1)

        assert simplify(neg_one.slt_semantics(pos_one))
        assert not simplify(pos_one.slt_semantics(neg_one))

    def test_slt_same_negative_uses_unsigned_order(self):
        """SLT 同为负数：-2 < -1 为 True。"""
        neg_two = Uint256.from_int(UINT256_MASK - 1)
        neg_one = Uint256.from_int(UINT256_MASK)

        assert simplify(neg_two.slt_semantics(neg_one))
        assert not simplify(neg_one.slt_semantics(neg_two))

    def test_sgt_cross_sign_and_same_negative(self):
        """SGT 跨符号和同负数：1 > -1，-1 > -2。"""
        pos_one = Uint256.from_int(1)
        neg_one = Uint256.from_int(UINT256_MASK)
        neg_two = Uint256.from_int(UINT256_MASK - 1)

        assert simplify(pos_one.sgt_semantics(neg_one))
        assert simplify(neg_one.sgt_semantics(neg_two))
        assert not simplify(neg_two.sgt_semantics(neg_one))

    def test_eq_equal(self):
        """EQ 相等：5 == 5 为 True"""
        val1 = Uint256.from_int(5)
        val2 = Uint256.from_int(5)
        result = val1.eq_semantics(val2)
        assert simplify(result)

    def test_eq_not_equal(self):
        """EQ 不等：5 == 3 为 False"""
        val1 = Uint256.from_int(5)
        val2 = Uint256.from_int(3)
        result = val1.eq_semantics(val2)
        assert not simplify(result)

    def test_eq_different_limbs(self):
        """EQ 不同 limb：比较跨 limb 的值"""
        val1 = Uint256(
            BitVecVal(1, 64),
            BitVecVal(0, 64),
            BitVecVal(0, 64),
            BitVecVal(0, 64)
        )
        val2 = Uint256.from_int(1)
        result = val1.eq_semantics(val2)
        assert simplify(result)

    def test_iszero_zero(self):
        """ISZERO 零：iszero(0) 为 True"""
        val1 = Uint256.from_int(0)
        result = val1.iszero_semantics()
        assert simplify(result)

    def test_iszero_nonzero(self):
        """ISZERO 非零：iszero(1) 为 False"""
        val1 = Uint256.from_int(1)
        result = val1.iszero_semantics()
        assert not simplify(result)

    def test_iszero_large_nonzero(self):
        """ISZERO 大数非零：iszero(2^128) 为 False"""
        val1 = Uint256(
            BitVecVal(0, 64),
            BitVecVal(0, 64),
            BitVecVal(1, 64),
            BitVecVal(0, 64)
        )
        result = val1.iszero_semantics()
        assert not simplify(result)


class TestUint256ComparisonGroundTruth:
    """比较原语对 Z3 原生 BitVec(256) 语义的**全符号**交叉验证（ground truth）。

    上面 TestUint256ComparisonSemantics 是具体值点测，无法排除"自洽的系统性错误"
    （如 limb 显著性整体搞反、却恰好在被测点上正确）。这些 limb 级 borrow-chain 原语
    是 div/mod 分段建模的分支条件、以及 eq_borrow_chain_assumption 的信任基础
    （见 common/arithmetic.py、tests/composition/test_eq_borrow_chain_composition.py），
    属 soundness 敏感代码，必须有独立 ground-truth 锚。

    原生 ULT/UGT/== 对 Z3 不需 bit-blast 除法，全符号秒解（实测 < 0.1s/条）。
    """

    @staticmethod
    def _prove_equiv(claim):
        """证明 claim 对全符号 256-bit 输入恒成立：¬claim 不可满足。"""
        solver = Solver()
        solver.set(timeout=10_000)
        solver.add(Not(claim))
        result = solver.check()
        assert result == unsat, f"comparison primitive diverges from z3 native: {result}"

    def test_lt_matches_native_ult(self):
        """lt_semantics(a,b) ⟺ ULT(a,b)，全符号。"""
        a, b = BitVec("gt_lt_a", 256), BitVec("gt_lt_b", 256)
        x, y = Uint256.from_bv256(a), Uint256.from_bv256(b)
        self._prove_equiv(x.lt_semantics(y) == ULT(a, b))

    def test_gt_matches_native_ugt(self):
        """gt_semantics(a,b) ⟺ UGT(a,b)，全符号。"""
        a, b = BitVec("gt_gt_a", 256), BitVec("gt_gt_b", 256)
        x, y = Uint256.from_bv256(a), Uint256.from_bv256(b)
        self._prove_equiv(x.gt_semantics(y) == UGT(a, b))

    def test_eq_matches_native_eq(self):
        """eq_semantics(a,b) ⟺ (a == b)，全符号。"""
        a, b = BitVec("gt_eq_a", 256), BitVec("gt_eq_b", 256)
        x, y = Uint256.from_bv256(a), Uint256.from_bv256(b)
        self._prove_equiv(x.eq_semantics(y) == (a == b))

    def test_iszero_matches_native_zero(self):
        """iszero_semantics(a) ⟺ (a == 0)，全符号。"""
        a = BitVec("gt_iszero_a", 256)
        x = Uint256.from_bv256(a)
        self._prove_equiv(x.iszero_semantics() == (a == BitVecVal(0, 256)))

    def test_slt_matches_native_slt(self):
        """slt_semantics(a,b) ⟺ (a <s b)（z3 BitVec `<` 默认有符号），全符号。"""
        a, b = BitVec("gt_slt_a", 256), BitVec("gt_slt_b", 256)
        x, y = Uint256.from_bv256(a), Uint256.from_bv256(b)
        self._prove_equiv(x.slt_semantics(y) == (a < b))

    def test_sgt_matches_native_sgt(self):
        """sgt_semantics(a,b) ⟺ (a >s b)（z3 BitVec `>` 默认有符号），全符号。"""
        a, b = BitVec("gt_sgt_a", 256), BitVec("gt_sgt_b", 256)
        x, y = Uint256.from_bv256(a), Uint256.from_bv256(b)
        self._prove_equiv(x.sgt_semantics(y) == (a > b))


class TestUint256Conversions:
    """测试转换方法。"""

    def test_from_int_simple(self):
        """from_int 简单值：from_int(42)"""
        val = Uint256.from_int(42)
        assert simplify(val.z0 == 42)
        assert simplify(val.z1 == 0)
        assert simplify(val.z2 == 0)
        assert simplify(val.z3 == 0)

    def test_from_int_large(self):
        """from_int 大值：from_int(2^64)"""
        val = Uint256.from_int(2**64)
        assert simplify(val.z0 == 0)
        assert simplify(val.z1 == 1)
        assert simplify(val.z2 == 0)
        assert simplify(val.z3 == 0)

    def test_to_bv256_and_from_bv256(self):
        """to_bv256 和 from_bv256 往返转换"""
        original = Uint256.from_int(0x123456789ABCDEF0)
        bv = original.to_bv256()
        restored = Uint256.from_bv256(bv)
        assert simplify(original.z0 == restored.z0)
        assert simplify(original.z1 == restored.z1)

    def test_symbolic(self):
        """symbolic 创建符号变量"""
        val = Uint256.symbolic("x")
        # 符号变量应该有正确的结构
        assert hasattr(val, 'z0')
        assert hasattr(val, 'z1')
        assert hasattr(val, 'z2')
        assert hasattr(val, 'z3')


class TestMulCodegenOrder:
    """EVM MUL 按 compileEVMMul 的项形状建模（2026-09-27 审核）：值必须仍是 a*b mod 2^256。"""

    def test_concrete_matches_product(self):
        import random
        rng = random.Random(11)
        edges = [0, 1, UINT64_MASK, UINT256_MASK, 1 << 64, 1 << 192]
        values = edges + [rng.getrandbits(256) for _ in range(20)]
        for p in values:
            for q in values[:8]:
                assert_uint256_equals_int(Uint256.mul_codegen_order(Uint256.from_int(p), Uint256.from_int(q)), p * q)

    def test_symbolic_equals_holiman_product(self):
        from z3 import Or, SolverFor
        from verification.linear_encoding import lia_query
        a, b = Uint256.symbolic("a"), Uint256.symbolic("b")
        new = Uint256.mul_codegen_order(b, a)
        old = a.mul_semantics(b)
        differ = Or(*[getattr(new, f"z{i}") != getattr(old, f"z{i}") for i in range(4)])
        solver = SolverFor("QF_LIA")
        solver.set("timeout", 60_000)
        solver.add(lia_query(simplify(differ, bv_sort_ac=True)))
        assert solver.check() == unsat
