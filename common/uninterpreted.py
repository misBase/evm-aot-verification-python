"""EVM host function 的 Z3 未解释函数（uninterpreted function）语义。

相同的函数名确保 EVM IR 侧和 x86 侧生成相同的 Z3 符号，从而允许 Z3 证明等价性。
涉及 memory 的函数（sha3、call 系列、create 系列）接受 memory array 参数，
两侧传入同一个 SMTState 里的 memory array（共享 Z3 Array）。
"""
from typing import Optional

from z3 import (
    BitVecRef,
    BitVecSort,
    BitVecVal,
    BoolRef,
    BoolSort,
    Function,
    If,
)


def sha3_semantics(memory, offset: BitVecRef, length: BitVecRef) -> BitVecRef:
    """SHA3: uninterpreted hash of memory[offset..offset+length)。"""
    f = Function('sha3', memory.sort(), offset.sort(), length.sort(), BitVecSort(256))
    return f(memory, offset, length)


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
