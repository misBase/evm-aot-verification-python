"""EVM 算术操作的 Z3 语义函数。

操作 BitVec(256)，无状态，供 evm_ir 和 x86_64 两侧共用。
"""
from z3 import BitVecVal, Extract, Function, BitVecSort, If, UDiv, URem, ZeroExt


def div_semantics(a, b):
    """EVM DIV: a / b，b==0时返回0。"""
    return If(b == BitVecVal(0, 256), BitVecVal(0, 256), UDiv(a, b))


def mod_semantics(a, b):
    """EVM MOD: a % b，b==0时返回0。"""
    return If(b == BitVecVal(0, 256), BitVecVal(0, 256), URem(a, b))


def exp_semantics(base, exponent):
    """EVM EXP: base^exponent，使用未解释函数。"""
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
