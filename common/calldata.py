"""EVM IR 与 x86 summary 共享的 calldata word 语义。"""

from typing import Optional

from z3 import (
    BitVecRef,
    BitVecVal,
    BoolRef,
    BoolVal,
    Concat,
    Extract,
    Function,
    If,
    BitVecSort,
    is_bv_value,
    Select,
    simplify,
    ULE,
    ULT,
)


def _offset64_and_overflow(offset_bv: BitVecRef) -> tuple[BitVecRef, BoolRef]:
    if offset_bv.size() == 64:
        return offset_bv, BoolVal(False)
    if offset_bv.size() == 256:
        return (
            Extract(63, 0, offset_bv),
            Extract(255, 64, offset_bv) != BitVecVal(0, 192),
        )
    raise ValueError(f"Offset must be 64 or 256 bits, got {offset_bv.size()}")


def calldataload_no_overflow_assumption(offset_bv: BitVecRef) -> Optional[BoolRef]:
    """返回优化版 IR 语义使用的 offset 不溢出假设。"""
    if offset_bv.size() == 64:
        return None
    if offset_bv.size() == 256:
        return Extract(255, 64, offset_bv) == BitVecVal(0, 192)
    raise ValueError(f"Offset must be 64 or 256 bits, got {offset_bv.size()}")


def calldataload_word(
    calldata,
    calldatasize_64: BitVecRef,
    offset_bv: BitVecRef,
    *,
    omit_overflow_guard: bool = False,
    abstract: bool = False,
) -> BitVecRef:
    """建模 EVM CALLDATALOAD / Go getData(input, offset, 32)。

    返回 word 按 big-endian 排列：``offset`` 处的 byte 进入 bits 255..248。
    若 256-bit offset 放不进 uint64，带 guard 的语义返回 0。调用方如果已经加入
    offset 不溢出的前置条件，可以设置 ``omit_overflow_guard=True``，避免携带死分支。
    """
    if calldatasize_64.size() != 64:
        raise ValueError(
            f"calldatasize context must be 64 bits, got {calldatasize_64.size()}"
        )

    offset_64, offset_overflow = _offset64_and_overflow(offset_bv)
    concrete_offset = None
    try:
        simplified_offset = simplify(offset_64)
        if is_bv_value(simplified_offset):
            concrete_offset = simplified_offset.as_long()
    except Exception:
        concrete_offset = None

    # path-observation 模式下，offset 0 的 dispatcher selector 读取保持 byte 精确；
    # ABI 参数 word 则抽象成 word-level 输入。这样 EVM/x86 仍共享同一个 word-level
    # 输入，但不会把 32 个 byte-level calldata guard 拖进 storage proof。
    # 对具体 ABI offset 来说，这是对补零 concrete word 的 over-approximation；
    # 若能在更大的抽象输入空间证明 refinement，则对具体 calldata 也足够。
    should_abstract = abstract and (
        concrete_offset is None or concrete_offset >= 4
    )
    if should_abstract:
        f = Function(
            "calldataload_word",
            calldata.sort(),
            BitVecSort(64),
            BitVecSort(64),
            BitVecSort(256),
        )
        if concrete_offset is not None:
            # 具体 ABI word 读取有意建模为与 calldata size 无关的 word-level 输入。
            # 如果在这个 UF 里保留 CallDataSize，会把无关的 size 依赖泄漏到 storage
            # key/value 中，迫使后续 refinement 检查按 size 切分。
            symbolic_word = f(calldata, BitVecVal(0, 64), offset_64)
            loaded_data = symbolic_word
        else:
            symbolic_word = f(calldata, calldatasize_64, offset_64)
            loaded_data = If(
                ULE(calldatasize_64, offset_64),
                BitVecVal(0, 256),
                symbolic_word,
            )
        if omit_overflow_guard or offset_bv.size() == 64:
            return loaded_data
        return If(offset_overflow, BitVecVal(0, 256), loaded_data)

    if concrete_offset is not None:
        uint64_limit = (1 << 64) - 1
        bytes_list = []
        for i in range(32):
            addr = concrete_offset + i
            if addr > uint64_limit:
                bytes_list.append(BitVecVal(0, 8))
                continue
            addr_bv = BitVecVal(addr, 64)
            bytes_list.append(
                If(
                    ULT(addr_bv, calldatasize_64),
                    Select(calldata, addr_bv),
                    BitVecVal(0, 8),
                )
            )
    else:
        effective_start = If(ULT(calldatasize_64, offset_64), calldatasize_64, offset_64)
        remaining = calldatasize_64 - effective_start
        bytes_list = [
            If(
                ULT(BitVecVal(i, 64), remaining),
                Select(calldata, effective_start + BitVecVal(i, 64)),
                BitVecVal(0, 8),
            )
            for i in range(32)
        ]
    loaded_data = Concat(*bytes_list)
    if omit_overflow_guard or offset_bv.size() == 64:
        return loaded_data
    return If(offset_overflow, BitVecVal(0, 256), loaded_data)
