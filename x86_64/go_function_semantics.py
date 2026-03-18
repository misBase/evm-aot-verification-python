"""
Go函数Z3语义建模。

通过x86内存的Store/Select操作建模Go host/builtin函数的Pop/Push效果。
x86侧的EVM栈数据存放在[R14 + sp * 8]处，每个Uint256占4个64-bit limb。

Go runtime的StackHolder接口：
  Pop:  sp_new = sp - 4; value = load_256bit(R14 + sp_new * 8)
  Push: store_256bit(R14 + sp * 8, value); sp_new = sp + 4
"""

import logging
from typing import Optional, Tuple

from z3 import BitVec, BitVecVal, BitVecSort, Function, Select

from .aot_profile import X86AOTProfile
from state.smt_state import SMTState

logger = logging.getLogger(__name__)

# Each Uint256 occupies 4 limbs * 8 bytes = 32 bytes
LIMBS_PER_UINT256 = 4


class GoFunctionSemantics:
    """通过x86内存操作建模Go host/builtin函数的语义效果。"""

    def __init__(self, aot_profile: X86AOTProfile):
        self.aot_profile = aot_profile

    def _pop_uint256(self, sp: int, mstate: SMTState) -> Tuple[BitVec, int, SMTState]:
        """从x86内存中弹出一个Uint256值。

        Go runtime的PopUint256: sp -= 4, value = mem[R14 + sp*8 .. +32]

        Args:
            sp: 当前栈指针（以limb为单位）
            mstate: 当前SMT状态

        Returns:
            (value_256bit, new_sp, mstate)
        """
        from x86_64.models import Register

        new_sp = sp - LIMBS_PER_UINT256
        r14 = mstate.x86_registers.get_register(Register.R14)
        base_offset = r14 + BitVecVal(new_sp * 8, 64)
        value = mstate.x86_memory.load_256bit(base_offset)
        return value, new_sp, mstate

    def _push_uint256(self, sp: int, value: BitVec, mstate: SMTState) -> Tuple[int, SMTState]:
        """将一个Uint256值推送到x86内存。

        Go runtime的PushUint256: mem[R14 + sp*8 .. +32] = value, sp += 4

        Args:
            sp: 当前栈指针（以limb为单位）
            value: 要推送的256位值
            mstate: 当前SMT状态

        Returns:
            (new_sp, mstate)
        """
        from x86_64.models import Register

        r14 = mstate.x86_registers.get_register(Register.R14)
        base_offset = r14 + BitVecVal(sp * 8, 64)
        mstate.x86_memory = mstate.x86_memory.store_256bit(base_offset, value)
        new_sp = sp + LIMBS_PER_UINT256
        return new_sp, mstate

    def _update_sp_in_memory(self, sp: int, mstate: SMTState) -> SMTState:
        """更新callEngine中的stack_pointer字段。

        将新的SP值写回 [R13 + stack_pointer_offset]。

        Args:
            sp: 新的栈指针值
            mstate: 当前SMT状态

        Returns:
            更新后的mstate
        """
        from x86_64.models import Register

        r13 = mstate.x86_registers.get_register(Register.R13)
        sp_offset = BitVecVal(self.aot_profile.offsets["stack_pointer"], 64)
        mstate.x86_memory = mstate.x86_memory.store_64bit(
            r13 + sp_offset, BitVecVal(sp, 64)
        )
        return mstate

    def apply(self, status_code: int, func_index: Optional[int],
              sp: int, mstate: SMTState) -> SMTState:
        """分发并应用Go函数的语义效果。

        Args:
            status_code: 状态码（4=host, 5=builtin）
            func_index: 函数索引
            sp: 栈指针（从x86指令流中提取的立即数）
            mstate: 当前SMT状态

        Returns:
            应用Go函数效果后的mstate
        """
        if status_code == self.aot_profile.status_codes["call_go_host_function"]:
            return self._dispatch_host_function(func_index, sp, mstate)
        elif status_code == self.aot_profile.status_codes["call_builtin_function"]:
            return self._dispatch_builtin_function(func_index, sp, mstate)
        else:
            logger.warning(
                "GoFunctionSemantics: unknown status_code=%d, skipping",
                status_code,
            )
            return mstate

    # ---- Host函数分发 (statusCode=4) ----

    def _dispatch_host_function(self, func_index: Optional[int],
                                sp: int, mstate: SMTState) -> SMTState:
        """分发host函数调用。

        host函数的func_index映射依赖于编译时注册顺序，
        需要通过aot_profile.host_functions查找。
        """
        host_functions = getattr(self.aot_profile, 'host_functions', {})
        func_name = host_functions.get(func_index)

        if func_name is None:
            logger.warning(
                "GoFunctionSemantics: unknown host func_index=%s, skipping",
                func_index,
            )
            return mstate

        handler = {
            "sload": self._handle_sload,
            "sstore": self._handle_sstore,
            "sha3": self._handle_sha3,
        }.get(func_name)

        if handler is None:
            logger.warning(
                "GoFunctionSemantics: unimplemented host function '%s', skipping",
                func_name,
            )
            return mstate

        return handler(sp, mstate)

    def _handle_sload(self, sp: int, mstate: SMTState) -> SMTState:
        """SLOAD: pop key, push Select(Storage, key)。"""
        key, sp, mstate = self._pop_uint256(sp, mstate)
        val = mstate.evm_storage.sload(key)
        sp, mstate = self._push_uint256(sp, val, mstate)
        mstate = self._update_sp_in_memory(sp, mstate)
        return mstate

    def _handle_sstore(self, sp: int, mstate: SMTState) -> SMTState:
        """SSTORE: pop key, pop value, Store(Storage, key, value)。"""
        key, sp, mstate = self._pop_uint256(sp, mstate)
        val, sp, mstate = self._pop_uint256(sp, mstate)
        mstate.evm_storage = mstate.evm_storage.sstore(key, val)
        mstate = self._update_sp_in_memory(sp, mstate)
        return mstate

    def _handle_sha3(self, sp: int, mstate: SMTState) -> SMTState:
        """SHA3: pop offset, pop length, push sha3(memory, offset, length)。

        使用与IR侧相同的未解释函数。
        """
        offset_bv, sp, mstate = self._pop_uint256(sp, mstate)
        length_bv, sp, mstate = self._pop_uint256(sp, mstate)

        sha3_func = Function(
            'sha3',
            mstate.evm_memory.Memory.sort(),
            offset_bv.sort(),
            length_bv.sort(),
            BitVecSort(256),
        )
        hash_val = sha3_func(mstate.evm_memory.Memory, offset_bv, length_bv)

        sp, mstate = self._push_uint256(sp, hash_val, mstate)
        mstate = self._update_sp_in_memory(sp, mstate)
        return mstate

    # ---- Builtin函数分发 (statusCode=5) ----

    def _dispatch_builtin_function(self, func_index: Optional[int],
                                   sp: int, mstate: SMTState) -> SMTState:
        """分发builtin函数调用。"""
        builtin_functions = getattr(self.aot_profile, 'builtin_functions', {})
        func_name = builtin_functions.get(func_index)

        if func_name is None:
            logger.warning(
                "GoFunctionSemantics: unknown builtin func_index=%s, skipping",
                func_index,
            )
            return mstate

        handler = {
            "div": self._handle_builtin_div,
            "mod": self._handle_builtin_mod,
            "exp": self._handle_builtin_exp,
            "addmod": self._handle_builtin_addmod,
            "mulmod": self._handle_builtin_mulmod,
        }.get(func_name)

        if handler is None:
            logger.warning(
                "GoFunctionSemantics: unimplemented builtin function '%s', skipping",
                func_name,
            )
            return mstate

        return handler(sp, mstate)

    def _handle_builtin_div(self, sp: int, mstate: SMTState) -> SMTState:
        """DIV builtin: pop a, pop b, push a/b (EVM semantics: 0 if b==0)。"""
        from z3 import If, UDiv

        a, sp, mstate = self._pop_uint256(sp, mstate)
        b, sp, mstate = self._pop_uint256(sp, mstate)
        result = If(b == BitVecVal(0, 256), BitVecVal(0, 256), UDiv(a, b))
        sp, mstate = self._push_uint256(sp, result, mstate)
        mstate = self._update_sp_in_memory(sp, mstate)
        return mstate

    def _handle_builtin_mod(self, sp: int, mstate: SMTState) -> SMTState:
        """MOD builtin: pop a, pop b, push a%b (EVM semantics: 0 if b==0)。"""
        from z3 import If, URem

        a, sp, mstate = self._pop_uint256(sp, mstate)
        b, sp, mstate = self._pop_uint256(sp, mstate)
        result = If(b == BitVecVal(0, 256), BitVecVal(0, 256), URem(a, b))
        sp, mstate = self._push_uint256(sp, result, mstate)
        mstate = self._update_sp_in_memory(sp, mstate)
        return mstate

    def _handle_builtin_exp(self, sp: int, mstate: SMTState) -> SMTState:
        """EXP builtin: pop base, pop exponent, push base^exponent。

        使用与IR侧相同的未解释函数。
        """
        base, sp, mstate = self._pop_uint256(sp, mstate)
        exponent, sp, mstate = self._pop_uint256(sp, mstate)
        exp_func = Function('evm_exp', BitVecSort(256), BitVecSort(256), BitVecSort(256))
        result = exp_func(base, exponent)
        sp, mstate = self._push_uint256(sp, result, mstate)
        mstate = self._update_sp_in_memory(sp, mstate)
        return mstate

    def _handle_builtin_addmod(self, sp: int, mstate: SMTState) -> SMTState:
        """ADDMOD builtin: pop a, pop b, pop mod, push (a+b)%mod。"""
        from z3 import If, URem, ZeroExt, Extract

        a, sp, mstate = self._pop_uint256(sp, mstate)
        b, sp, mstate = self._pop_uint256(sp, mstate)
        mod, sp, mstate = self._pop_uint256(sp, mstate)
        zero = BitVecVal(0, 256)
        a_ext = ZeroExt(1, a)
        b_ext = ZeroExt(1, b)
        mod_ext = ZeroExt(1, mod)
        res_ext = URem(a_ext + b_ext, mod_ext)
        result = If(mod == zero, zero, Extract(255, 0, res_ext))
        sp, mstate = self._push_uint256(sp, result, mstate)
        mstate = self._update_sp_in_memory(sp, mstate)
        return mstate

    def _handle_builtin_mulmod(self, sp: int, mstate: SMTState) -> SMTState:
        """MULMOD builtin: pop a, pop b, pop mod, push (a*b)%mod。"""
        from z3 import If, URem, ZeroExt, Extract

        a, sp, mstate = self._pop_uint256(sp, mstate)
        b, sp, mstate = self._pop_uint256(sp, mstate)
        mod, sp, mstate = self._pop_uint256(sp, mstate)
        zero = BitVecVal(0, 256)
        a_ext = ZeroExt(256, a)
        b_ext = ZeroExt(256, b)
        mod_ext = ZeroExt(256, mod)
        res_ext = URem(a_ext * b_ext, mod_ext)
        result = If(mod == zero, zero, Extract(255, 0, res_ext))
        sp, mstate = self._push_uint256(sp, result, mstate)
        mstate = self._update_sp_in_memory(sp, mstate)
        return mstate
