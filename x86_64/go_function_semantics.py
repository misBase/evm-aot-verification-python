"""
Go函数Z3语义建模。

通过x86内存的Store/Select操作建模Go host/builtin函数的Pop/Push效果。
x86侧的EVM栈数据存放在[R14 + sp * 8]处，每个Uint256占4个64-bit limb。

Go runtime的StackHolder接口：
  Pop:  sp_new = sp - 4; value = load_256bit(R14 + sp_new * 8)
  Push: store_256bit(R14 + sp * 8, value); sp_new = sp + 4

⚠️ 栈地址对齐警告 ⚠️
Go runtime的sp以limb为单位（sp=1表示[R14+8]），而EVM验证映射
（verification/memory_mapping.py）使用 R14-0x40 作为stack[0]的基址，
元素间距0x20。

这意味着：
- Go runtime sp=0 → R14（地址 R14+0）
- memory_mapping stack[0] → R14-0x40（地址 R14-0x40）

两者相差 0x40（64字节 = 8 limbs = 2 Uint256s）。

如果Go compiler初始化sp=8，则：
- Go sp=8 → R14+0x40
- memory_mapping stack[4] → R14-0x40+4*0x20=R14+0x40 ✓ 对齐

所以对齐前提是：Go runtime的sp初始化值必须是8（或任何使得
[R14+sp*8]等于[R14-0x40+stack_index*0x20]的固定偏移）。

如果sp初始化不同，会导致栈读写出错位！
"""

import logging
from typing import Optional, Tuple

from z3 import BitVec, BitVecVal, BitVecSort, Function

from .aot_profile import X86AOTProfile
from state.smt_state import SMTState
from common import evm_ops

logger = logging.getLogger(__name__)

# Each Uint256 occupies 4 limbs * 8 bytes = 32 bytes
LIMBS_PER_UINT256 = 4

# Stack address alignment constants
# These must match the Go compiler's actual initialization
# verification/memory_mapping.py uses R14-0x40 as stack[0] base with 0x20 spacing
STACK_BASE_OFFSET = -0x40  # from memory_mapping.py
STACK_ELEMENT_SIZE = 0x20  # from memory_mapping.py

# Stack address alignment with memory_mapping
#
# Two different address formulas are in use:
#
# 1. Go's StackHolder model: addr = R14 + sp * 8
#    - sp is in limbs (1 limb = 8 bytes)
#    - Stack grows upward from R14
#    - sp represents bytes used / 8
#
# 2. memory_mapping (verification): addr = R14 - 0x40 + stack_index * 0x20
#    - stack_index is 0=top, 1=second, etc.
#    - Stack grows downward from R14-0x40
#    - Each element is 0x20 bytes (4 limbs = 1 Uint256)
#
# RELATIONSHIP:
#   Go's "top of stack" is at address (sp - 4) * 8 from R14 (after sp increment for push)
#   memory_mapping's stack[0] is at R14 - 0x40
#
#   For Go sp=N with a single value pushed:
#     Go view: value at [sp-4] = [N-4]
#     memory_mapping view: value at stack[0] = R14 - 0x40
#
#   Setting R14 + (sp-4)*8 = R14 - 0x40 + stack_index*0x20:
#     (sp-4)*8 = -0x40 + stack_index*0x20
#     stack_index = (sp*8 + 0x40) / 0x20 = (sp + 4) / 4
#
# KEY INSIGHT: Go sp and memory_mapping stack_index are related by:
#   stack_index = (sp + 4) / 4  (integer division)
#
# Verified: sp=4 -> stack_index=2, sp=8 -> stack_index=3, sp=12 -> stack_index=4
#
# This means Go's StackHolder and memory_mapping describe the SAME memory layout
# but with different indexing conventions!


class GoFunctionSemanticsError(Exception):
    """Go函数语义建模过程中的错误。"""
    pass


class StackAlignmentError(Exception):
    """栈地址与验证映射不对齐。"""
    pass


def validate_sp_alignment(sp: int) -> bool:
    """验证 sp 值是否与 memory_mapping 对齐。

    Go: addr = R14 + sp * 8 (sp in limbs)
    EVM verification: addr = R14 + (-0x40 + stack_index * 0x20)

    对齐条件: R14 + sp*8 = R14 + (-0x40 + stack_index*0x20)
    即: sp*8 + 0x40 = stack_index * 0x20
    即: (sp*8 + 0x40) % 0x20 == 0
    即: (sp + 4) % 4 == 0 (简化后)

    Args:
        sp: 栈指针值（limbs）

    Returns:
        True if aligned
    """
    # Check if (sp + 4) is divisible by 4, which means sp*8 + 0x40 is divisible by 0x20
    return (sp + 4) % 4 == 0


def get_aligned_sp_for_address(address_offset: int) -> int:
    """获取使得地址为指定偏移的最小 sp 值。

    Args:
        address_offset: 相对于 R14 的字节偏移

    Returns:
        对齐的 sp 值（limbs）
    """
    # address_offset = sp * 8 + 0x40 (to align with memory_mapping)
    # So: sp = (address_offset - 0x40) / 8
    # But we need the result to be a limb index
    return (address_offset - STACK_BASE_OFFSET) // 8


class GoFunctionSemantics:
    """通过x86内存操作建模Go host/builtin函数的语义效果。"""

    def __init__(self, aot_profile: X86AOTProfile):
        self.aot_profile = aot_profile

    def _compute_stack_address(self, sp: int) -> int:
        """将 Go 的 sp 转换为 memory_mapping 的栈地址。

        Go sp: addr = R14 + sp * 8
        memory_mapping: addr = R14 - 0x40 + stack_index * 0x20

        关系: sp * 8 = -0x40 + stack_index * 0x20
             stack_index = (sp * 8 + 0x40) / 0x20 = (sp + 8) / 4
        验证: sp=8 → stack_index=(8+8)//4=4 → addr=R14-0x40+4*0x20=R14+0x40 ✓
              sp=12 → stack_index=(12+8)//4=5 → addr=R14-0x40+5*0x20=R14+0x60 ✓

        如果 aot_profile.stack_sp_bias_limbs 不为 0，使用:
        stack_index = (sp + 8 + bias) // 4

        Args:
            sp: Go 栈指针（limbs）

        Returns:
            相对于 R14 的字节偏移
        """
        bias = getattr(self.aot_profile, 'stack_sp_bias_limbs', 0)
        stack_index = (sp + 8 + bias) // 4
        return STACK_BASE_OFFSET + stack_index * STACK_ELEMENT_SIZE

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

        # 先递减 sp（Go 的 Pop: sp -= 4, then read at [sp]）
        new_sp = sp - LIMBS_PER_UINT256

        # 使用 memory_mapping 的公式计算地址
        addr_offset = self._compute_stack_address(new_sp)
        r14 = mstate.x86_registers.get_register(Register.R14)
        base_offset = r14 + BitVecVal(addr_offset, 64)
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

        # 使用 memory_mapping 的公式计算地址
        addr_offset = self._compute_stack_address(sp)
        r14 = mstate.x86_registers.get_register(Register.R14)
        base_offset = r14 + BitVecVal(addr_offset, 64)
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

        Raises:
            StackAlignmentError: 当 sp 不满足对齐要求时
        """
        # 验证 sp 对齐：sp 必须是 4 的倍数，以确保与 memory_mapping 对齐
        # stack_index = (sp + 4) // 4 要求 sp + 4 能被 4 整除
        # 这等价于 sp % 4 == 0
        if not validate_sp_alignment(sp):
            raise StackAlignmentError(
                f"Go sp={sp} is not aligned with memory_mapping. "
                f"Expected sp % 4 == 0 (i.e., sp in {{0, 4, 8, 12, ...}}). "
                f"Current sp may cause incorrect stack address calculation."
            )

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

        Raises:
            GoFunctionSemanticsError: 当func_index为已知但映射到未知函数时
        """
        if func_index is None:
            # func_index not found in block - this can happen in test scenarios
            # or when CFG is being built without full metadata
            logger.warning(
                "GoFunctionSemantics: host func_index not found in block, skipping semantics"
            )
            return mstate

        host_functions = getattr(self.aot_profile, 'host_functions', {})
        func_name = host_functions.get(func_index)

        if func_name is None:
            raise GoFunctionSemanticsError(
                f"unknown host func_index={func_index}. "
                f"Ensure host_functions mapping includes this index."
            )

        handler = {
            "sload": self._handle_sload,
            "sstore": self._handle_sstore,
            "sha3": self._handle_sha3,
        }.get(func_name)

        if handler is None:
            raise GoFunctionSemanticsError(
                f"unimplemented host function '{func_name}'"
            )

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

        使用x86_memory建模，因为x86指令（MSTORE等）只更新x86_memory。
        这确保与EVM IR侧的SHA3语义等价（两侧都基于同一内存模型）。
        """
        offset_bv, sp, mstate = self._pop_uint256(sp, mstate)
        length_bv, sp, mstate = self._pop_uint256(sp, mstate)

        sha3_func = Function(
            'sha3',
            mstate.x86_memory.Memory.sort(),
            offset_bv.sort(),
            length_bv.sort(),
            BitVecSort(256),
        )
        hash_val = sha3_func(mstate.x86_memory.Memory, offset_bv, length_bv)

        sp, mstate = self._push_uint256(sp, hash_val, mstate)
        mstate = self._update_sp_in_memory(sp, mstate)
        return mstate

    # ---- Builtin函数分发 (statusCode=5) ----

    def _dispatch_builtin_function(self, func_index: Optional[int],
                                   sp: int, mstate: SMTState) -> SMTState:
        """分发builtin函数调用。

        Raises:
            GoFunctionSemanticsError: 当func_index为已知但映射到未知函数时
        """
        if func_index is None:
            # func_index not found in block - this can happen in test scenarios
            # or when CFG is being built without full metadata
            logger.warning(
                "GoFunctionSemantics: builtin func_index not found in block, skipping semantics"
            )
            return mstate

        builtin_functions = getattr(self.aot_profile, 'builtin_functions', {})
        func_name = builtin_functions.get(func_index)

        if func_name is None:
            raise GoFunctionSemanticsError(
                f"unknown builtin func_index={func_index}. "
                f"Ensure builtin_functions mapping includes this index."
            )

        handler = {
            "div": self._handle_builtin_div,
            "mod": self._handle_builtin_mod,
            "exp": self._handle_builtin_exp,
            "addmod": self._handle_builtin_addmod,
            "mulmod": self._handle_builtin_mulmod,
            "memory_grow": self._handle_builtin_memory_grow,
            "gas_cost": self._handle_builtin_gas_cost,
        }.get(func_name)

        if handler is None:
            raise GoFunctionSemanticsError(
                f"unimplemented builtin function '{func_name}'"
            )

        return handler(sp, mstate)

    def _handle_builtin_div(self, sp: int, mstate: SMTState) -> SMTState:
        """DIV builtin: pop a, pop b, push a/b (EVM semantics: 0 if b==0)。"""
        a, sp, mstate = self._pop_uint256(sp, mstate)
        b, sp, mstate = self._pop_uint256(sp, mstate)
        result = evm_ops.div_semantics(a, b)
        sp, mstate = self._push_uint256(sp, result, mstate)
        mstate = self._update_sp_in_memory(sp, mstate)
        return mstate

    def _handle_builtin_mod(self, sp: int, mstate: SMTState) -> SMTState:
        """MOD builtin: pop a, pop b, push a%b (EVM semantics: 0 if b==0)。"""
        a, sp, mstate = self._pop_uint256(sp, mstate)
        b, sp, mstate = self._pop_uint256(sp, mstate)
        result = evm_ops.mod_semantics(a, b)
        sp, mstate = self._push_uint256(sp, result, mstate)
        mstate = self._update_sp_in_memory(sp, mstate)
        return mstate

    def _handle_builtin_exp(self, sp: int, mstate: SMTState) -> SMTState:
        """EXP builtin: pop base, pop exponent, push base^exponent。

        使用与IR侧相同的未解释函数。
        """
        base, sp, mstate = self._pop_uint256(sp, mstate)
        exponent, sp, mstate = self._pop_uint256(sp, mstate)
        result = evm_ops.exp_semantics(base, exponent)
        sp, mstate = self._push_uint256(sp, result, mstate)
        mstate = self._update_sp_in_memory(sp, mstate)
        return mstate

    def _handle_builtin_addmod(self, sp: int, mstate: SMTState) -> SMTState:
        """ADDMOD builtin: pop a, pop b, pop mod, push (a+b)%mod。"""
        a, sp, mstate = self._pop_uint256(sp, mstate)
        b, sp, mstate = self._pop_uint256(sp, mstate)
        mod, sp, mstate = self._pop_uint256(sp, mstate)
        result = evm_ops.addmod_semantics(a, b, mod)
        sp, mstate = self._push_uint256(sp, result, mstate)
        mstate = self._update_sp_in_memory(sp, mstate)
        return mstate

    def _handle_builtin_mulmod(self, sp: int, mstate: SMTState) -> SMTState:
        """MULMOD builtin: pop a, pop b, pop mod, push (a*b)%mod。"""
        a, sp, mstate = self._pop_uint256(sp, mstate)
        b, sp, mstate = self._pop_uint256(sp, mstate)
        mod, sp, mstate = self._pop_uint256(sp, mstate)
        result = evm_ops.mulmod_semantics(a, b, mod)
        sp, mstate = self._push_uint256(sp, result, mstate)
        mstate = self._update_sp_in_memory(sp, mstate)
        return mstate

    def _handle_builtin_memory_grow(self, sp: int, mstate: SMTState) -> SMTState:
        """MEMORYGROW builtin: pop num_words, push previous_memory_size。

        EVM memory_grow takes the number of words to expand and returns
        the previous memory size in words. Since we don't track actual
        memory size in this symbolic model, we use an uninterpreted function.
        """
        num_words, sp, mstate = self._pop_uint256(sp, mstate)

        memory_grow_func = Function(
            'evm_memory_grow',
            BitVecSort(256),
            BitVecSort(256),
        )
        result = memory_grow_func(num_words)

        sp, mstate = self._push_uint256(sp, result, mstate)
        mstate = self._update_sp_in_memory(sp, mstate)
        return mstate

    def _handle_builtin_gas_cost(self, sp: int, mstate: SMTState) -> SMTState:
        """GAS builtin: push remaining gas.

        EVM GAS opcode returns the amount of gas available in the current
        execution context. Since gas tracking is complex and not the focus
        of our semantic equivalence verification, we use an uninterpreted
        function that returns a symbolic gas value.

        Note: GAS is special - it doesn't consume stack arguments.
        """
        gas_func = Function('evm_gas', BitVecSort(256))
        result = gas_func()  # no arguments, returns BitVec(256)

        sp, mstate = self._push_uint256(sp, result, mstate)
        mstate = self._update_sp_in_memory(sp, mstate)
        return mstate
