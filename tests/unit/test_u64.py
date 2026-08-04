"""`common/u64.py` 的直接单测：Go uint256→uint64 转换语义的三种返回形式。

IR 侧与 x86 侧共用这一份实现，"高位非零"的处理一旦分叉就是静默的不健全，
故三个函数各自覆盖：64 位入参、256 位低位入参、高位非零、非法位宽 fail-closed。
"""

import pytest
from z3 import BitVec, BitVecVal, is_false, is_true, simplify

from common.u64 import split_u64, to_u64_with_overflow_max, truncate_to_64

MAX_U64 = (1 << 64) - 1
TWO_200 = BitVecVal(1 << 200, 256)


class TestTruncateTo64:
    def test_64bit_input_is_identity(self):
        v = BitVec("v", 64)
        assert truncate_to_64(v) is v

    def test_256bit_low_word_preserved(self):
        out = simplify(truncate_to_64(BitVecVal(0x1234, 256)))
        assert out.size() == 64
        assert out.eq(BitVecVal(0x1234, 64))

    def test_high_bits_are_dropped(self):
        """截断就是截断——高位信息丢失，调用方必须自己保证高位无意义。"""
        out = simplify(truncate_to_64(BitVecVal((1 << 200) | 7, 256)))
        assert out.eq(BitVecVal(7, 64))

    @pytest.mark.parametrize("width", [8, 32, 128, 256 + 1])
    def test_other_widths_fail_closed(self, width):
        with pytest.raises(ValueError, match="64-bit or 256-bit"):
            truncate_to_64(BitVec("x", width))


class TestToU64WithOverflowMax:
    def test_64bit_input_is_identity(self):
        v = BitVec("v", 64)
        assert to_u64_with_overflow_max(v) is v

    def test_fits_in_u64_returns_low_word(self):
        out = simplify(to_u64_with_overflow_max(BitVecVal(MAX_U64, 256)))
        assert out.eq(BitVecVal(MAX_U64, 64))

    def test_overflow_saturates_to_max_u64(self):
        """镜像 uint256.Uint64WithOverflow：高位非零时给 MaxUint64 而**不是**截断值。"""
        out = simplify(to_u64_with_overflow_max(BitVecVal((1 << 200) | 7, 256)))
        assert out.eq(BitVecVal(MAX_U64, 64))
        assert not out.eq(BitVecVal(7, 64))

    @pytest.mark.parametrize("width", [8, 32, 128])
    def test_other_widths_fail_closed(self, width):
        with pytest.raises(ValueError, match="64-bit or 256-bit"):
            to_u64_with_overflow_max(BitVec("x", width))


class TestSplitU64:
    def test_64bit_input_never_overflows(self):
        v = BitVec("v", 64)
        overflow, low = split_u64(v)
        assert is_false(simplify(overflow)), "64 位入参已在 u64 域内，溢出标志必须恒假"
        assert low is v

    def test_256bit_low_value_has_false_overflow(self):
        overflow, low = split_u64(BitVecVal(0x1234, 256))
        assert is_false(simplify(overflow))
        assert simplify(low).eq(BitVecVal(0x1234, 64))

    def test_256bit_high_nonzero_sets_overflow(self):
        overflow, low = split_u64(TWO_200)
        assert is_true(simplify(overflow)), "高 192 位非零 → 溢出标志为真"
        assert simplify(low).eq(BitVecVal(0, 64)), "低位仍是截断值，由调用方决定用不用"

    def test_overflow_flag_is_symbolic_for_symbolic_input(self):
        """符号输入下溢出标志必须留成真正的分支条件，不能被折成常量。"""
        overflow, _ = split_u64(BitVec("o", 256))
        simplified = simplify(overflow)
        assert not is_true(simplified) and not is_false(simplified)

    @pytest.mark.parametrize("width", [8, 32, 128])
    def test_other_widths_fail_closed(self, width):
        with pytest.raises(ValueError, match="must be 64 or 256 bits"):
            split_u64(BitVec("x", width))
