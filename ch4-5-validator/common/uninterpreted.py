"""EVM host function 的 Z3 未解释函数（uninterpreted function）语义。

相同的函数名确保 EVM IR 侧和 x86 侧生成相同的 Z3 符号，从而允许 Z3 证明等价性。
SHA3 只把规范化的 byte slice 作为 UF 参数，避免无关 memory store 污染 hash identity；
CALL / CREATE 系列仍接受 memory array 参数。
"""
from typing import Optional

from z3 import (
    BitVec,
    BitVecRef,
    BitVecSort,
    BitVecVal,
    BoolRef,
    BoolSort,
    Concat,
    Extract,
    Function,
    If,
    Lambda,
    Select,
    ULT,
    ZeroExt,
    is_bv_value,
    simplify,
)


SHA3_FAST_PATH_MAX_BYTES = 256


def _to_bv64(value: BitVecRef) -> BitVecRef:
    if value.size() == 64:
        return value
    if value.size() == 256:
        return Extract(63, 0, value)
    raise ValueError(f"Expected 64-bit or 256-bit BitVec, got {value.size()} bits")


def _to_bv256(value: BitVecRef) -> BitVecRef:
    if value.size() == 256:
        return value
    if value.size() == 64:
        return ZeroExt(192, value)
    raise ValueError(f"Expected 64-bit or 256-bit BitVec, got {value.size()} bits")


def sha3_semantics(memory, base: BitVecRef, offset: BitVecRef,
                   length: BitVecRef) -> BitVecRef:
    """SHA3: uninterpreted hash of memory[base+offset : +length).

    The hash identity depends on the selected byte slice and the original
    256-bit length.  The whole memory Array is intentionally not an argument.
    """
    base_64 = _to_bv64(base)
    offset_64 = _to_bv64(offset)
    length_256 = _to_bv256(length)
    length_id = simplify(length_256)
    start = simplify(base_64 + offset_64)

    if is_bv_value(length_id):
        concrete_length = length_id.as_long()
        if 0 <= concrete_length <= SHA3_FAST_PATH_MAX_BYTES:
            bytes_list = []
            for i in range(concrete_length):
                bytes_list.append(Select(memory, start + BitVecVal(i, 64)))
            # z3py Concat needs >= 2 parts: one byte is its own 8-bit argument
            # (keccak256 of a single byte, e.g. abi.encodePacked(bytes1)).
            if len(bytes_list) >= 2:
                data_arg = Concat(*bytes_list)
            else:
                data_arg = bytes_list[0] if bytes_list else BitVecVal(0, 8)
            f = Function(
                f"sha3_bytes_{concrete_length}",
                BitVecSort(data_arg.size()),
                BitVecSort(256),
            )
            return f(data_arg)

    # BV64 length only bounds memory indexing in this model; length_id keeps the
    # original BV256 value in the hash identity.
    length_64 = simplify(_to_bv64(length_id))
    idx = BitVec('sha3_slice_idx', 64)
    slice_array = Lambda(
        [idx],
        If(
            ULT(idx, length_64),
            Select(memory, start + idx),
            BitVecVal(0, 8),
        ),
    )
    f = Function('sha3_slice', slice_array.sort(), BitVecSort(256), BitVecSort(256))
    return f(slice_array, length_id)


def balance_semantics(addr: BitVecRef) -> BitVecRef:
    """BALANCE: uninterpreted balance of address。"""
    f = Function('evm_balance', BitVecSort(256), BitVecSort(256))
    return f(addr)


def self_balance_semantics() -> BitVecRef:
    """SELFBALANCE: uninterpreted balance of current contract。"""
    f = Function('evm_self_balance', BitVecSort(256))
    return f()


def ext_code_size_semantics(addr: BitVecRef) -> BitVecRef:
    """EXTCODESIZE: uninterpreted size of code at address。"""
    f = Function('evm_ext_code_size', BitVecSort(256), BitVecSort(256))
    return f(addr)


def ext_code_hash_semantics(addr: BitVecRef) -> BitVecRef:
    """EXTCODEHASH: uninterpreted code hash at address。"""
    f = Function('evm_ext_code_hash', BitVecSort(256), BitVecSort(256))
    return f(addr)


def block_hash_semantics(block_number: BitVecRef) -> BitVecRef:
    """BLOCKHASH: uninterpreted hash of historical block。"""
    f = Function('evm_block_hash', BitVecSort(256), BitVecSort(256))
    return f(block_number)


def blob_hash_semantics(index: BitVecRef) -> BitVecRef:
    """BLOBHASH: uninterpreted blob versioned hash by index。"""
    f = Function('evm_blob_hash', BitVecSort(256), BitVecSort(256))
    return f(index)


def _scoped_name(base_name: str, effect_id: Optional[int]) -> str:
    """为需要结构化 identity 的 host effect 构造作用域化名字。"""
    if effect_id is None:
        return base_name
    return f"{base_name}_{effect_id}"


def ext_code_copy_byte(addr: BitVecRef, offset: BitVecRef,
                       byte_index: BitVecRef,
                       effect_id: Optional[int] = None) -> BitVecRef:
    """EXTCODECOPY: uninterpreted byte from external code[offset + byte_index]。"""
    f = Function(_scoped_name('evm_ext_code_copy_byte', effect_id),
                 BitVecSort(256), BitVecSort(256), BitVecSort(64),
                 BitVecSort(8))
    return f(addr, offset, byte_index)


def create_semantics(value: BitVecRef, offset: BitVecRef, size: BitVecRef,
                     memory, effect_id: Optional[int] = None) -> BitVecRef:
    """CREATE: uninterpreted new contract address。"""
    f = Function(_scoped_name('evm_create', effect_id),
                 BitVecSort(256), BitVecSort(256), BitVecSort(256),
                 memory.sort(),
                 BitVecSort(256))
    return f(value, offset, size, memory)


def create2_semantics(value: BitVecRef, offset: BitVecRef, size: BitVecRef,
                      salt: BitVecRef, memory, effect_id: Optional[int] = None) -> BitVecRef:
    """CREATE2: uninterpreted new contract address (deterministic)。"""
    f = Function(_scoped_name('evm_create2', effect_id),
                 BitVecSort(256), BitVecSort(256), BitVecSort(256), BitVecSort(256),
                 memory.sort(),
                 BitVecSort(256))
    return f(value, offset, size, salt, memory)


def _constrain_to_boolean(raw: BitVecRef) -> BitVecRef:
    """将UF原始结果约束为{0, 1}。

    Go runtime的CALL系列函数只push 0（失败）或 1（成功）。
    使用 If(raw == 0, 0, 1) 将任意256-bit UF结果映射到{0, 1}。
    """
    return If(raw == BitVecVal(0, 256), BitVecVal(0, 256), BitVecVal(1, 256))


def call_semantics(gas: BitVecRef, addr: BitVecRef, value: BitVecRef,
                   args_offset: BitVecRef, args_size: BitVecRef,
                   ret_offset: BitVecRef, ret_size: BitVecRef,
                   memory, effect_id: Optional[int] = None) -> BitVecRef:
    """CALL: uninterpreted success flag, constrained to {0, 1}。"""
    f = Function(_scoped_name('evm_call', effect_id),
                 BitVecSort(256), BitVecSort(256), BitVecSort(256),
                 BitVecSort(256), BitVecSort(256), BitVecSort(256), BitVecSort(256),
                 memory.sort(),
                 BitVecSort(256))
    raw = f(gas, addr, value, args_offset, args_size, ret_offset, ret_size, memory)
    return _constrain_to_boolean(raw)


def call_should_copy_return_data(gas: BitVecRef, addr: BitVecRef, value: BitVecRef,
                                 args_offset: BitVecRef, args_size: BitVecRef,
                                 ret_offset: BitVecRef, ret_size: BitVecRef,
                                 memory, effect_id: Optional[int] = None) -> BoolRef:
    """CALL: whether return-data should be copied back to memory."""
    f = Function(_scoped_name('evm_call_copy', effect_id),
                 BitVecSort(256), BitVecSort(256), BitVecSort(256),
                 BitVecSort(256), BitVecSort(256), BitVecSort(256), BitVecSort(256),
                 memory.sort(),
                 BoolSort())
    return f(gas, addr, value, args_offset, args_size, ret_offset, ret_size, memory)


def call_return_byte(gas: BitVecRef, addr: BitVecRef, value: BitVecRef,
                     args_offset: BitVecRef, args_size: BitVecRef,
                     ret_offset: BitVecRef, ret_size: BitVecRef,
                     memory, byte_index: BitVecRef,
                     effect_id: Optional[int] = None) -> BitVecRef:
    """CALL: uninterpreted return-data byte at byte_index."""
    f = Function(_scoped_name('evm_call_ret_byte', effect_id),
                 BitVecSort(256), BitVecSort(256), BitVecSort(256),
                 BitVecSort(256), BitVecSort(256), BitVecSort(256), BitVecSort(256),
                 memory.sort(), BitVecSort(64),
                 BitVecSort(8))
    return f(gas, addr, value, args_offset, args_size, ret_offset, ret_size, memory, byte_index)


def callcode_semantics(gas: BitVecRef, addr: BitVecRef, value: BitVecRef,
                       args_offset: BitVecRef, args_size: BitVecRef,
                       ret_offset: BitVecRef, ret_size: BitVecRef,
                       memory, effect_id: Optional[int] = None) -> BitVecRef:
    """CALLCODE: uninterpreted success flag, constrained to {0, 1}。"""
    f = Function(_scoped_name('evm_callcode', effect_id),
                 BitVecSort(256), BitVecSort(256), BitVecSort(256),
                 BitVecSort(256), BitVecSort(256), BitVecSort(256), BitVecSort(256),
                 memory.sort(),
                 BitVecSort(256))
    raw = f(gas, addr, value, args_offset, args_size, ret_offset, ret_size, memory)
    return _constrain_to_boolean(raw)


def callcode_should_copy_return_data(gas: BitVecRef, addr: BitVecRef, value: BitVecRef,
                                     args_offset: BitVecRef, args_size: BitVecRef,
                                     ret_offset: BitVecRef, ret_size: BitVecRef,
                                     memory, effect_id: Optional[int] = None) -> BoolRef:
    """CALLCODE: whether return-data should be copied back to memory."""
    f = Function(_scoped_name('evm_callcode_copy', effect_id),
                 BitVecSort(256), BitVecSort(256), BitVecSort(256),
                 BitVecSort(256), BitVecSort(256), BitVecSort(256), BitVecSort(256),
                 memory.sort(),
                 BoolSort())
    return f(gas, addr, value, args_offset, args_size, ret_offset, ret_size, memory)


def callcode_return_byte(gas: BitVecRef, addr: BitVecRef, value: BitVecRef,
                         args_offset: BitVecRef, args_size: BitVecRef,
                         ret_offset: BitVecRef, ret_size: BitVecRef,
                         memory, byte_index: BitVecRef,
                         effect_id: Optional[int] = None) -> BitVecRef:
    """CALLCODE: uninterpreted return-data byte at byte_index."""
    f = Function(_scoped_name('evm_callcode_ret_byte', effect_id),
                 BitVecSort(256), BitVecSort(256), BitVecSort(256),
                 BitVecSort(256), BitVecSort(256), BitVecSort(256), BitVecSort(256),
                 memory.sort(), BitVecSort(64),
                 BitVecSort(8))
    return f(gas, addr, value, args_offset, args_size, ret_offset, ret_size, memory, byte_index)


def delegate_call_semantics(gas: BitVecRef, addr: BitVecRef,
                            args_offset: BitVecRef, args_size: BitVecRef,
                            ret_offset: BitVecRef, ret_size: BitVecRef,
                            memory, effect_id: Optional[int] = None) -> BitVecRef:
    """DELEGATECALL: uninterpreted success flag, constrained to {0, 1}。"""
    f = Function(_scoped_name('evm_delegate_call', effect_id),
                 BitVecSort(256), BitVecSort(256),
                 BitVecSort(256), BitVecSort(256), BitVecSort(256), BitVecSort(256),
                 memory.sort(),
                 BitVecSort(256))
    raw = f(gas, addr, args_offset, args_size, ret_offset, ret_size, memory)
    return _constrain_to_boolean(raw)


def delegate_call_should_copy_return_data(gas: BitVecRef, addr: BitVecRef,
                                          args_offset: BitVecRef, args_size: BitVecRef,
                                          ret_offset: BitVecRef, ret_size: BitVecRef,
                                          memory, effect_id: Optional[int] = None) -> BoolRef:
    """DELEGATECALL: whether return-data should be copied back to memory."""
    f = Function(_scoped_name('evm_delegate_call_copy', effect_id),
                 BitVecSort(256), BitVecSort(256),
                 BitVecSort(256), BitVecSort(256), BitVecSort(256), BitVecSort(256),
                 memory.sort(),
                 BoolSort())
    return f(gas, addr, args_offset, args_size, ret_offset, ret_size, memory)


def delegate_call_return_byte(gas: BitVecRef, addr: BitVecRef,
                              args_offset: BitVecRef, args_size: BitVecRef,
                              ret_offset: BitVecRef, ret_size: BitVecRef,
                              memory, byte_index: BitVecRef,
                              effect_id: Optional[int] = None) -> BitVecRef:
    """DELEGATECALL: uninterpreted return-data byte at byte_index."""
    f = Function(_scoped_name('evm_delegate_call_ret_byte', effect_id),
                 BitVecSort(256), BitVecSort(256),
                 BitVecSort(256), BitVecSort(256), BitVecSort(256), BitVecSort(256),
                 memory.sort(), BitVecSort(64),
                 BitVecSort(8))
    return f(gas, addr, args_offset, args_size, ret_offset, ret_size, memory, byte_index)


def static_call_semantics(gas: BitVecRef, addr: BitVecRef,
                          args_offset: BitVecRef, args_size: BitVecRef,
                          ret_offset: BitVecRef, ret_size: BitVecRef,
                          memory, effect_id: Optional[int] = None) -> BitVecRef:
    """STATICCALL: uninterpreted success flag, constrained to {0, 1}。"""
    f = Function(_scoped_name('evm_static_call', effect_id),
                 BitVecSort(256), BitVecSort(256),
                 BitVecSort(256), BitVecSort(256), BitVecSort(256), BitVecSort(256),
                 memory.sort(),
                 BitVecSort(256))
    raw = f(gas, addr, args_offset, args_size, ret_offset, ret_size, memory)
    return _constrain_to_boolean(raw)


def static_call_return_byte(gas: BitVecRef, addr: BitVecRef,
                            args_offset: BitVecRef, args_size: BitVecRef,
                            ret_offset: BitVecRef, ret_size: BitVecRef,
                            memory, byte_index: BitVecRef,
                            effect_id: Optional[int] = None) -> BitVecRef:
    """STATICCALL: uninterpreted return-data byte at byte_index."""
    f = Function(_scoped_name('evm_static_call_ret_byte', effect_id),
                 BitVecSort(256), BitVecSort(256),
                 BitVecSort(256), BitVecSort(256), BitVecSort(256), BitVecSort(256),
                 memory.sort(), BitVecSort(64),
                 BitVecSort(8))
    return f(gas, addr, args_offset, args_size, ret_offset, ret_size, memory, byte_index)


# ---------------------------------------------------------------------------
# host 调用的**实际返回长度**
# ---------------------------------------------------------------------------
#
# 为什么需要独立的 UF：`retSize` 是**调用方给出的输出缓冲区长度**，而 RETURNDATASIZE
# 读到的是**被调用方实际返回的长度** `len(res)`。两者在协议上是不同的量——host 完全
# 可以返回比 retSize 更短或更长的数据（自动拷贝只搬 min(retSize, len(res)) 字节，
# 但 RETURNDATA* 看到的是完整的 len(res)）。
#
# 把 return-data size 钉成 `retSize` 会让"真实返回长度"整个落在量化域之外：两侧模型
# 都只允许 size == retSize，于是一个**混淆返回长度与输出缓冲区长度**的 codegen 缺陷
# 会被两侧的共同错误掩盖 —— 那是假绿。改用同名 UF 后，两侧取到同一个符号值、照常
# 相消，而错误的实现会因为取值不同而被抓住。

def call_return_size(gas: BitVecRef, addr: BitVecRef, value: BitVecRef,
                     args_offset: BitVecRef, args_size: BitVecRef,
                     ret_offset: BitVecRef, ret_size: BitVecRef,
                     memory, effect_id: Optional[int] = None) -> BitVecRef:
    """CALL: host 实际返回的数据长度（`len(res)`），64-bit。"""
    f = Function(_scoped_name('evm_call_ret_size', effect_id),
                 BitVecSort(256), BitVecSort(256), BitVecSort(256),
                 BitVecSort(256), BitVecSort(256), BitVecSort(256), BitVecSort(256),
                 memory.sort(),
                 BitVecSort(64))
    return f(gas, addr, value, args_offset, args_size, ret_offset, ret_size, memory)


def callcode_return_size(gas: BitVecRef, addr: BitVecRef, value: BitVecRef,
                         args_offset: BitVecRef, args_size: BitVecRef,
                         ret_offset: BitVecRef, ret_size: BitVecRef,
                         memory, effect_id: Optional[int] = None) -> BitVecRef:
    """CALLCODE: host 实际返回的数据长度，64-bit。"""
    f = Function(_scoped_name('evm_callcode_ret_size', effect_id),
                 BitVecSort(256), BitVecSort(256), BitVecSort(256),
                 BitVecSort(256), BitVecSort(256), BitVecSort(256), BitVecSort(256),
                 memory.sort(),
                 BitVecSort(64))
    return f(gas, addr, value, args_offset, args_size, ret_offset, ret_size, memory)


def delegate_call_return_size(gas: BitVecRef, addr: BitVecRef,
                              args_offset: BitVecRef, args_size: BitVecRef,
                              ret_offset: BitVecRef, ret_size: BitVecRef,
                              memory, effect_id: Optional[int] = None) -> BitVecRef:
    """DELEGATECALL: host 实际返回的数据长度，64-bit。"""
    f = Function(_scoped_name('evm_delegatecall_ret_size', effect_id),
                 BitVecSort(256), BitVecSort(256),
                 BitVecSort(256), BitVecSort(256), BitVecSort(256), BitVecSort(256),
                 memory.sort(),
                 BitVecSort(64))
    return f(gas, addr, args_offset, args_size, ret_offset, ret_size, memory)


def static_call_return_size(gas: BitVecRef, addr: BitVecRef,
                            args_offset: BitVecRef, args_size: BitVecRef,
                            ret_offset: BitVecRef, ret_size: BitVecRef,
                            memory, effect_id: Optional[int] = None) -> BitVecRef:
    """STATICCALL: host 实际返回的数据长度，64-bit。"""
    f = Function(_scoped_name('evm_staticcall_ret_size', effect_id),
                 BitVecSort(256), BitVecSort(256),
                 BitVecSort(256), BitVecSort(256), BitVecSort(256), BitVecSort(256),
                 memory.sort(),
                 BitVecSort(64))
    return f(gas, addr, args_offset, args_size, ret_offset, ret_size, memory)


# CREATE/CREATE2 同样刷新 returndata：成功时 host 返回 nil、engine 把长度刷成 0
# （engine_evm.go 的 returndata 复位）；失败（revert）时则是 revert reason。
#
# **不把 size 钉成 0**：那只覆盖成功路径，会把 revert 路径排除在量化域外。用 UF
# 表示"CREATE 之后的 returndata"同时覆盖两种情况，两侧同名同参 ⇒ 相消。相比之下
# "什么都不做"（保留旧 returndata）是**不可能的真实状态**——真实执行中 CREATE 必然
# 刷新它，保留旧值会让"错误保留旧 returndata"的编译产物被判等价。

def create_return_size(value: BitVecRef, offset: BitVecRef, size: BitVecRef,
                       memory, effect_id: Optional[int] = None) -> BitVecRef:
    """CREATE: 调用后 returndata 的长度，64-bit。"""
    f = Function(_scoped_name('evm_create_ret_size', effect_id),
                 BitVecSort(256), BitVecSort(256), BitVecSort(256),
                 memory.sort(),
                 BitVecSort(64))
    return f(value, offset, size, memory)


def create_return_byte(value: BitVecRef, offset: BitVecRef, size: BitVecRef,
                       memory, byte_index: BitVecRef,
                       effect_id: Optional[int] = None) -> BitVecRef:
    """CREATE: 调用后 returndata 在 byte_index 处的字节。"""
    f = Function(_scoped_name('evm_create_ret_byte', effect_id),
                 BitVecSort(256), BitVecSort(256), BitVecSort(256),
                 memory.sort(), BitVecSort(64),
                 BitVecSort(8))
    return f(value, offset, size, memory, byte_index)


def create2_return_size(value: BitVecRef, offset: BitVecRef, size: BitVecRef,
                        salt: BitVecRef, memory,
                        effect_id: Optional[int] = None) -> BitVecRef:
    """CREATE2: 调用后 returndata 的长度，64-bit。"""
    f = Function(_scoped_name('evm_create2_ret_size', effect_id),
                 BitVecSort(256), BitVecSort(256), BitVecSort(256),
                 BitVecSort(256), memory.sort(),
                 BitVecSort(64))
    return f(value, offset, size, salt, memory)


def create2_return_byte(value: BitVecRef, offset: BitVecRef, size: BitVecRef,
                        salt: BitVecRef, memory, byte_index: BitVecRef,
                        effect_id: Optional[int] = None) -> BitVecRef:
    """CREATE2: 调用后 returndata 在 byte_index 处的字节。"""
    f = Function(_scoped_name('evm_create2_ret_byte', effect_id),
                 BitVecSort(256), BitVecSort(256), BitVecSort(256),
                 BitVecSort(256), memory.sort(), BitVecSort(64),
                 BitVecSort(8))
    return f(value, offset, size, salt, memory, byte_index)
