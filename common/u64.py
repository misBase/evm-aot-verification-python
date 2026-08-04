"""Go `uint256 → uint64` 转换语义的 Z3 镜像。

EVM IR 侧与 x86 侧都要把 256 位栈值降到 64 位域（内存 offset、length、gas 参数），
两边必须用同一份实现，否则"高位非零"的处理一旦分叉就是静默的不健全。
三个函数是同一件事的三种返回形式：

    truncate_to_64            直接截断，调用方已知高位无意义
    to_u64_with_overflow_max  溢出饱和成 MaxUint64（uint256.Uint64WithOverflow 的值）
    split_u64                 (高位非零, 低 64 位)（Uint64WithOverflow 的两个返回值）
"""

from z3 import BitVecRef, BitVecVal, BoolVal, Extract, If


def truncate_to_64(value: BitVecRef) -> BitVecRef:
    """将BitVec偏移量截断到64位。"""
    if value.size() == 64:
        return value
    if value.size() == 256:
        return Extract(63, 0, value)
    raise ValueError(f"Expected 64-bit or 256-bit BitVec, got {value.size()} bits")


def to_u64_with_overflow_max(value: BitVecRef) -> BitVecRef:
    """模拟 uint256.Uint64WithOverflow：溢出时返回 MaxUint64。"""
    if value.size() == 64:
        return value
    if value.size() != 256:
        raise ValueError(f"Expected 64-bit or 256-bit BitVec, got {value.size()} bits")
    high_bits = Extract(255, 64, value)
    low_bits = Extract(63, 0, value)
    return If(
        high_bits == BitVecVal(0, 192),
        low_bits,
        BitVecVal((1 << 64) - 1, 64),
    )


def split_u64(value_bv):
    """拆成 (高位非零, 低 64 位)，镜像 uint256.Uint64WithOverflow 的两个返回值。

    64-bit 入参视为恒不溢出（调用方已在 64 位域内）。其它宽度 fail-closed 抛错，
    静默截断会让溢出分支凭空消失。
    """
    size = value_bv.size()
    if size == 256:
        return Extract(255, 64, value_bv) != BitVecVal(0, 192), Extract(63, 0, value_bv)
    if size == 64:
        return BoolVal(False), value_bv
    raise ValueError(f"offset/length must be 64 or 256 bits, got {size}")
