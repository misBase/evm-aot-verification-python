"""
Go host/builtin 函数的 Z3 语义建模。

本文件通过 x86 内存读写模拟 Go runtime 的 Uint256 Pop/Push 效果。
这里的 `R14` 表示当前 block 的栈基准，Go runtime 按 `R14 + sp * 8`
访问栈，其中 `sp` 以 limb 为单位（1 limb = 8 字节，1 Uint256 = 4 limbs）。
逻辑栈顶不是固定地址，而是当前 `R14 + (sp-4) * 8` 处的值。
具体地址换算规则以 `_compute_stack_address()` 和 Pop/Push 语义为准。
"""

import logging
from typing import Optional, Tuple

from z3 import And, BitVec, BitVecVal, If, Lambda, Select, UGE, ULT

from .aot_profile import X86AOTProfile
from state.smt_state import SMTState, MemoryDomain
from common import uninterpreted
from common import arithmetic
from x86_64.models import Register

logger = logging.getLogger(__name__)

# 每个 Uint256 占 4 个 limb，每个 limb 为 8 字节，共 32 字节
LIMBS_PER_UINT256 = 4
LIMB_SIZE_BYTES = 8

# 栈地址对齐常量
# 这里的地址偏移相对于当前 block 的 R14 栈基准
STACK_BASE_OFFSET = 0
STACK_ELEMENT_SIZE = 0x20

# 当前 block 栈窗口中的地址关系
#
# Go 物理栈地址：R14 + sp * 8
# 当前逻辑栈顶 stack[0] 的基址是 R14 + (sp-4) * 8，
# stack[1] 的基址是 R14 + (sp-8) * 8。
# 只有在 block 入口且 sp=0 的预置栈窗口中，才会退化为：
#   stack[0] -> R14 - 0x20
#   stack[1] -> R14 - 0x40


class GoFunctionSemanticsError(Exception):
    """Go函数语义建模过程中的错误。"""
    pass


class StackAlignmentError(Exception):
    """栈地址与验证映射不对齐。"""
    pass


def validate_sp_alignment(sp: int) -> bool:
    """验证 sp 是否对齐到 Uint256 槽位边界。

    Args:
        sp: 栈指针值（limbs）

    Returns:
        若对齐则返回 True
    """
    # 一个 Uint256 占 4 个 limb，因此 sp 必须落在 4-limb 边界上。
    return sp % LIMBS_PER_UINT256 == 0


def get_aligned_sp_for_address(address_offset: int) -> int:
    """获取使得地址为指定偏移的最小 sp 值。

    Args:
        address_offset: 相对于 R14 的字节偏移

    Returns:
        对齐的 sp 值（limbs）
    """
    # 当前 block 栈窗口地址满足：address_offset = sp * 8
    # 因此：sp = address_offset / 8
    # 结果仍以 limb 为单位
    return (address_offset - STACK_BASE_OFFSET) // 8


class GoFunctionSemantics:
    """通过x86内存操作建模Go host/builtin函数的语义效果。"""

    def __init__(self, aot_profile: X86AOTProfile):
        self.aot_profile = aot_profile

    def _compute_stack_address(self, sp: int) -> int:
        """将 Go 的 sp 转换为当前 block 栈窗口中的地址偏移。

        如果 aot_profile.stack_sp_bias_limbs 不为 0，使用:
        addr = R14 + (sp + bias) * 8

        Args:
            sp: Go 栈指针（limbs）

        Returns:
            相对于 R14 的字节偏移
        """
        bias = getattr(self.aot_profile, 'stack_sp_bias_limbs', 0)
        return STACK_BASE_OFFSET + (sp + bias) * LIMB_SIZE_BYTES

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

        # 按当前 block 栈窗口布局计算地址
        addr_offset = self._compute_stack_address(new_sp)
        r14 = mstate.x86_registers.get_register(Register.R14)
        base_offset = r14 + BitVecVal(addr_offset, 64)
        value = mstate.x86_memory.load_256bit(base_offset, domain=MemoryDomain.STACK)
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

        # 按当前 block 栈窗口布局计算地址
        addr_offset = self._compute_stack_address(sp)
        r14 = mstate.x86_registers.get_register(Register.R14)
        base_offset = r14 + BitVecVal(addr_offset, 64)
        mstate.x86_memory = mstate.x86_memory.store_256bit(base_offset, value, domain=MemoryDomain.STACK)
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
        sp_bv = BitVecVal(sp, 64)
        mstate.x86_memory = mstate.x86_memory.store_64bit(
            r13 + sp_offset, sp_bv, domain=MemoryDomain.CALLENGINE)
        # 同步 callEngine side-channel（保持与 x86 mov [r13+0x28], ... 的路径一致）
        mstate.callengine_stack_pointer_limbs = sp_bv
        return mstate

    def _sync_callengine_u64_field(self, mstate: SMTState, offset_name: str,
                                   side_channel_name: str, value: BitVec) -> None:
        r13 = mstate.x86_registers.get_register(Register.R13)
        offset = BitVecVal(self.aot_profile.offsets[offset_name], 64)
        setattr(mstate, side_channel_name, value)
        mstate.x86_memory = mstate.x86_memory.store_64bit(
            r13 + offset,
            value,
            domain=MemoryDomain.CALLENGINE,
        )

    def _clear_caller_saved_pointer_tags(self, mstate: SMTState) -> None:
        for reg in (
            Register.RAX, Register.RCX, Register.RDX, Register.RSI, Register.RDI,
            Register.R8, Register.R9, Register.R10, Register.R11,
        ):
            mstate.x86_registers.clear_pointer_tag(reg)

    def _update_return_data_source(self, mstate: SMTState, ret_size: BitVec,
                                   byte_fn, effect_tag: str) -> SMTState:
        size_64 = self._truncate_to_64(ret_size)
        idx = BitVec(f"{effect_tag}_returndata_idx", 64)
        old_return_data = mstate.return_data
        mstate.return_data = Lambda(
            idx,
            If(ULT(idx, size_64), byte_fn(idx), Select(old_return_data, idx)),
        )

        return_data_ptr = BitVec(f"{effect_tag}_returndata_ptr", 64)
        self._sync_callengine_u64_field(
            mstate,
            "return_data_pointer",
            "callengine_return_data_pointer",
            return_data_ptr,
        )
        self._sync_callengine_u64_field(
            mstate,
            "return_data_size",
            "callengine_return_data_size_bytes",
            size_64,
        )
        return mstate

    def apply(self, status_code: int, func_index: Optional[int],
              sp: int, mstate: SMTState, evm_pc: Optional[int] = None) -> SMTState:
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
        # 验证 sp 对齐：一个 Uint256 占 4 个 limb，因此 sp 必须是 4 的倍数
        if not validate_sp_alignment(sp):
            raise StackAlignmentError(
                f"Go sp={sp} is not aligned to Uint256 stack slots. "
                f"Expected sp % 4 == 0 (i.e., sp in {{0, 4, 8, 12, ...}}). "
                f"Current sp may cause incorrect stack address calculation."
            )

        if status_code == self.aot_profile.status_codes["call_go_host_function"]:
            result = self._dispatch_host_function(func_index, sp, mstate, evm_pc=evm_pc)
            self._clear_caller_saved_pointer_tags(result)
            return result
        elif status_code == self.aot_profile.status_codes["call_builtin_function"]:
            result = self._dispatch_builtin_function(func_index, sp, mstate)
            self._clear_caller_saved_pointer_tags(result)
            return result
        else:
            logger.warning(
                "GoFunctionSemantics: unknown status_code=%d, skipping",
                status_code,
            )
            return mstate

    # ---- Host函数分发 (statusCode=4) ----

    def _dispatch_host_function(self, func_index: Optional[int],
                                sp: int, mstate: SMTState,
                                evm_pc: Optional[int] = None) -> SMTState:
        """分发host函数调用。

        go-hpc-evm 的 host func_index 采用固定 ABI，
        需要通过 aot_profile 的 host 函数表解析。

        Raises:
            GoFunctionSemanticsError: 当func_index为已知但映射到未知函数时
        """
        if func_index is None:
            # block 中未找到 func_index。
            # 这可能出现在测试场景，或 CFG 构建时缺少完整元数据。
            logger.warning(
                "GoFunctionSemantics: host func_index not found in block, skipping semantics"
            )
            return mstate

        func_name = self.aot_profile.resolve_host_function_name(func_index)

        if func_name is None:
            raise GoFunctionSemanticsError(
                f"unknown host func_index={func_index}. "
                "This index is not defined by the active go-hpc-evm host ABI table."
            )

        scoped_handler = {
            "create": self._handle_create,
            "create2": self._handle_create2,
            "call": self._handle_call,
            "callCode": self._handle_call_code,
            "delegateCall": self._handle_delegate_call,
            "staticCall": self._handle_static_call,
            "extCodeCopy": self._handle_ext_code_copy,
        }.get(func_name)
        if scoped_handler is not None:
            return scoped_handler(sp, mstate, evm_pc)

        handler = {
            "sload": self._handle_sload,
            "sstore": self._handle_sstore,
            "sha3": self._handle_sha3,
            "balance": self._handle_balance,
            "selfBalance": self._handle_self_balance,
            "extCodeSize": self._handle_ext_code_size,
            "extCodeHash": self._handle_ext_code_hash,
            "blockHash": self._handle_block_hash,
            "selfDestruct": self._handle_self_destruct,
            "log": self._handle_log,
            "tload": self._handle_tload,
            "tstore": self._handle_tstore,
        }.get(func_name)

        if handler is None:
            raise GoFunctionSemanticsError(
                f"unimplemented host function '{func_name}'"
            )

        return handler(sp, mstate)

    def _truncate_to_64(self, value: BitVec) -> BitVec:
        """将256位偏移量截断到64位。"""
        from z3 import Extract

        if value.size() == 64:
            return value
        if value.size() == 256:
            return Extract(63, 0, value)
        raise ValueError(f"Expected 64-bit or 256-bit BitVec, got {value.size()} bits")

    def _write_call_return_data(self, mstate: SMTState, ret_offset: BitVec, ret_size: BitVec,
                                return_byte_fn, effect_id: int,
                                should_copy=None) -> SMTState:
        """将符号化的调用返回数据写入 x86 内存。"""
        return self._write_symbolic_memory_slice(
            mstate,
            ret_offset,
            ret_size,
            return_byte_fn,
            effect_tag=f"call_ret_idx_{effect_id}",
            should_copy=should_copy,
        )

    def _write_symbolic_memory_slice(self, mstate: SMTState, dest_offset: BitVec, size: BitVec,
                                     byte_fn, effect_tag: str,
                                     should_copy=None) -> SMTState:
        """将一个符号化字节切片写入 x86 内存（EVM 256-bit memory，R15 域）。"""
        from x86_64.models import Register

        dest_offset_64 = self._truncate_to_64(dest_offset)
        size_64 = self._truncate_to_64(size)
        zero_64 = BitVecVal(0, 64)
        r15 = mstate.x86_registers.get_register(Register.R15)
        base_addr = r15 + dest_offset_64

        idx = BitVec(effect_tag, 64)
        relative = idx - base_addr
        in_range = And(
            size_64 != zero_64,
            UGE(idx, base_addr),
            ULT(relative, size_64),
        )
        write_cond = in_range if should_copy is None else And(should_copy, in_range)
        new_evm_array = Lambda(
            idx,
            If(write_cond, byte_fn(relative), Select(mstate.x86_memory.evm_mem, idx)),
        )
        mstate.x86_memory = mstate.x86_memory._with_array(MemoryDomain.EVM, new_evm_array)
        return mstate

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
        """SHA3: pop offset, pop length, push sha3(memory, offset, length)。"""
        offset_bv, sp, mstate = self._pop_uint256(sp, mstate)
        length_bv, sp, mstate = self._pop_uint256(sp, mstate)
        hash_val = uninterpreted.sha3_semantics(mstate.x86_memory.evm_mem, offset_bv, length_bv)
        sp, mstate = self._push_uint256(sp, hash_val, mstate)
        mstate = self._update_sp_in_memory(sp, mstate)
        return mstate

    def _handle_balance(self, sp: int, mstate: SMTState) -> SMTState:
        """BALANCE: pop address, push balance(address)。"""
        addr, sp, mstate = self._pop_uint256(sp, mstate)
        result = uninterpreted.balance_semantics(addr)
        sp, mstate = self._push_uint256(sp, result, mstate)
        mstate = self._update_sp_in_memory(sp, mstate)
        return mstate

    def _handle_self_balance(self, sp: int, mstate: SMTState) -> SMTState:
        """SELFBALANCE: 压入当前合约余额（无栈输入）。"""
        result = uninterpreted.self_balance_semantics()
        sp, mstate = self._push_uint256(sp, result, mstate)
        mstate = self._update_sp_in_memory(sp, mstate)
        return mstate

    def _handle_ext_code_size(self, sp: int, mstate: SMTState) -> SMTState:
        """EXTCODESIZE: pop address, push extcodesize(address)。"""
        addr, sp, mstate = self._pop_uint256(sp, mstate)
        result = uninterpreted.ext_code_size_semantics(addr)
        sp, mstate = self._push_uint256(sp, result, mstate)
        mstate = self._update_sp_in_memory(sp, mstate)
        return mstate

    def _handle_ext_code_copy(self, sp: int, mstate: SMTState,
                              evm_pc: Optional[int] = None) -> SMTState:
        """EXTCODECOPY: 弹出 address、destOffset、offset、size，并符号化写入 x86 内存。"""
        addr, sp, mstate = self._pop_uint256(sp, mstate)
        dest_offset, sp, mstate = self._pop_uint256(sp, mstate)
        offset, sp, mstate = self._pop_uint256(sp, mstate)
        size, sp, mstate = self._pop_uint256(sp, mstate)
        effect_suffix = evm_pc if evm_pc is not None else "global"
        mstate = self._write_symbolic_memory_slice(
            mstate,
            dest_offset,
            size,
            lambda byte_index: uninterpreted.ext_code_copy_byte(
                addr, offset, byte_index, effect_id=evm_pc,
            ),
            effect_tag=f"extcodecopy_idx_{effect_suffix}",
        )
        mstate = self._update_sp_in_memory(sp, mstate)
        return mstate

    def _handle_ext_code_hash(self, sp: int, mstate: SMTState) -> SMTState:
        """EXTCODEHASH: pop address, push extcodehash(address)。"""
        addr, sp, mstate = self._pop_uint256(sp, mstate)
        result = uninterpreted.ext_code_hash_semantics(addr)
        sp, mstate = self._push_uint256(sp, result, mstate)
        mstate = self._update_sp_in_memory(sp, mstate)
        return mstate

    def _handle_block_hash(self, sp: int, mstate: SMTState) -> SMTState:
        """BLOCKHASH: pop blockNumber, push blockhash(blockNumber)。"""
        block_number, sp, mstate = self._pop_uint256(sp, mstate)
        result = uninterpreted.block_hash_semantics(block_number)
        sp, mstate = self._push_uint256(sp, result, mstate)
        mstate = self._update_sp_in_memory(sp, mstate)
        return mstate

    def _handle_self_destruct(self, sp: int, mstate: SMTState) -> SMTState:
        """SELFDESTRUCT: 弹出 address（终止执行，无返回值）。"""
        _addr, sp, mstate = self._pop_uint256(sp, mstate)
        mstate = self._update_sp_in_memory(sp, mstate)
        return mstate

    def _handle_log(self, sp: int, mstate: SMTState) -> SMTState:
        """LOG: 先弹出 n_topics、mStart、mSize，再弹出 n_topics 个 topic。

        Go 的 host.Log() 语义大致为：
          size := c.PopUint256()  // N = topic 数量
          mStart := c.PopUint256()
          mSize := c.PopUint256()
          for i := 0; i < N; i++ { topics[i] = c.PopUint256() }

        AOT 编译器会在调用 host bridge 前把 N 压栈。
        因此总计弹栈 N + 3 次，不压回结果。

        这里虽然从栈中读取 n_topics，但在 AOT 场景下它应始终是常量
        （LOG0..LOG4），所以验证时通常可被 Z3 直接化简。
        为安全起见，最多只弹 4 个 topic。
        """
        from z3 import is_bv_value
        n_topics_bv, sp, mstate = self._pop_uint256(sp, mstate)
        _mstart, sp, mstate = self._pop_uint256(sp, mstate)
        _msize, sp, mstate = self._pop_uint256(sp, mstate)

        # 确定需要额外弹出的 topic 数量
        # AOT 编译器压入的是常量 N（0-4），这里可以直接提取
        if is_bv_value(n_topics_bv):
            n = n_topics_bv.as_long()
            if n > 4:
                n = 4  # EVM 最多 4 个 topic
        else:
            # 如果这里是符号值，则保守地按 0 个 topic 处理
            # 按 AOT 约定这在实践中不应发生
            logger.warning("LOG: n_topics is symbolic, cannot determine topic count")
            n = 0

        for _ in range(n):
            _topic, sp, mstate = self._pop_uint256(sp, mstate)

        mstate = self._update_sp_in_memory(sp, mstate)
        return mstate

    def _handle_create(self, sp: int, mstate: SMTState, evm_pc: Optional[int] = None) -> SMTState:
        """CREATE: pop value, offset, size; push new_address。"""
        value, sp, mstate = self._pop_uint256(sp, mstate)
        offset, sp, mstate = self._pop_uint256(sp, mstate)
        size, sp, mstate = self._pop_uint256(sp, mstate)
        result = uninterpreted.create_semantics(value, offset, size, mstate.x86_memory.evm_mem, effect_id=evm_pc)
        sp, mstate = self._push_uint256(sp, result, mstate)
        mstate = self._update_sp_in_memory(sp, mstate)
        return mstate

    def _handle_create2(self, sp: int, mstate: SMTState, evm_pc: Optional[int] = None) -> SMTState:
        """CREATE2: pop value, offset, size, salt; push new_address。"""
        value, sp, mstate = self._pop_uint256(sp, mstate)
        offset, sp, mstate = self._pop_uint256(sp, mstate)
        size, sp, mstate = self._pop_uint256(sp, mstate)
        salt, sp, mstate = self._pop_uint256(sp, mstate)
        result = uninterpreted.create2_semantics(
            value, offset, size, salt, mstate.x86_memory.evm_mem, effect_id=evm_pc
        )
        sp, mstate = self._push_uint256(sp, result, mstate)
        mstate = self._update_sp_in_memory(sp, mstate)
        return mstate

    def _handle_call(self, sp: int, mstate: SMTState, evm_pc: Optional[int] = None) -> SMTState:
        """CALL: pop gas, addr, value, argsOffset, argsSize, retOffset, retSize; push success。"""
        gas, sp, mstate = self._pop_uint256(sp, mstate)
        addr, sp, mstate = self._pop_uint256(sp, mstate)
        value, sp, mstate = self._pop_uint256(sp, mstate)
        args_offset, sp, mstate = self._pop_uint256(sp, mstate)
        args_size, sp, mstate = self._pop_uint256(sp, mstate)
        ret_offset, sp, mstate = self._pop_uint256(sp, mstate)
        ret_size, sp, mstate = self._pop_uint256(sp, mstate)
        old_memory = mstate.x86_memory.evm_mem
        result = uninterpreted.call_semantics(
            gas, addr, value, args_offset, args_size, ret_offset, ret_size,
            old_memory, effect_id=evm_pc)
        effect_suffix = evm_pc if evm_pc is not None else "global"
        mstate = self._update_return_data_source(
            mstate,
            ret_size,
            lambda byte_index: uninterpreted.call_return_byte(
                gas, addr, value, args_offset, args_size, ret_offset, ret_size,
                old_memory, byte_index, effect_id=evm_pc,
            ),
            effect_tag=f"call_{effect_suffix}",
        )
        if evm_pc is not None:
            should_copy = uninterpreted.call_should_copy_return_data(
                gas, addr, value, args_offset, args_size, ret_offset, ret_size,
                old_memory, effect_id=evm_pc,
            )
            mstate = self._write_call_return_data(
                mstate,
                ret_offset,
                ret_size,
                lambda byte_index: uninterpreted.call_return_byte(
                    gas, addr, value, args_offset, args_size, ret_offset, ret_size,
                    old_memory, byte_index, effect_id=evm_pc,
                ),
                effect_id=evm_pc,
                should_copy=should_copy,
            )
        sp, mstate = self._push_uint256(sp, result, mstate)
        mstate = self._update_sp_in_memory(sp, mstate)
        return mstate

    def _handle_call_code(self, sp: int, mstate: SMTState, evm_pc: Optional[int] = None) -> SMTState:
        """CALLCODE: 与 CALL 的参数签名相同，压入 success。"""
        gas, sp, mstate = self._pop_uint256(sp, mstate)
        addr, sp, mstate = self._pop_uint256(sp, mstate)
        value, sp, mstate = self._pop_uint256(sp, mstate)
        args_offset, sp, mstate = self._pop_uint256(sp, mstate)
        args_size, sp, mstate = self._pop_uint256(sp, mstate)
        ret_offset, sp, mstate = self._pop_uint256(sp, mstate)
        ret_size, sp, mstate = self._pop_uint256(sp, mstate)
        old_memory = mstate.x86_memory.evm_mem
        result = uninterpreted.callcode_semantics(
            gas, addr, value, args_offset, args_size, ret_offset, ret_size,
            old_memory, effect_id=evm_pc)
        effect_suffix = evm_pc if evm_pc is not None else "global"
        mstate = self._update_return_data_source(
            mstate,
            ret_size,
            lambda byte_index: uninterpreted.callcode_return_byte(
                gas, addr, value, args_offset, args_size, ret_offset, ret_size,
                old_memory, byte_index, effect_id=evm_pc,
            ),
            effect_tag=f"callcode_{effect_suffix}",
        )
        if evm_pc is not None:
            should_copy = uninterpreted.callcode_should_copy_return_data(
                gas, addr, value, args_offset, args_size, ret_offset, ret_size,
                old_memory, effect_id=evm_pc,
            )
            mstate = self._write_call_return_data(
                mstate,
                ret_offset,
                ret_size,
                lambda byte_index: uninterpreted.callcode_return_byte(
                    gas, addr, value, args_offset, args_size, ret_offset, ret_size,
                    old_memory, byte_index, effect_id=evm_pc,
                ),
                effect_id=evm_pc,
                should_copy=should_copy,
            )
        sp, mstate = self._push_uint256(sp, result, mstate)
        mstate = self._update_sp_in_memory(sp, mstate)
        return mstate

    def _handle_delegate_call(self, sp: int, mstate: SMTState, evm_pc: Optional[int] = None) -> SMTState:
        """DELEGATECALL: 弹出 gas、addr、argsOffset、argsSize、retOffset、retSize，压入 success。"""
        gas, sp, mstate = self._pop_uint256(sp, mstate)
        addr, sp, mstate = self._pop_uint256(sp, mstate)
        args_offset, sp, mstate = self._pop_uint256(sp, mstate)
        args_size, sp, mstate = self._pop_uint256(sp, mstate)
        ret_offset, sp, mstate = self._pop_uint256(sp, mstate)
        ret_size, sp, mstate = self._pop_uint256(sp, mstate)
        old_memory = mstate.x86_memory.evm_mem
        result = uninterpreted.delegate_call_semantics(
            gas, addr, args_offset, args_size, ret_offset, ret_size,
            old_memory, effect_id=evm_pc)
        effect_suffix = evm_pc if evm_pc is not None else "global"
        mstate = self._update_return_data_source(
            mstate,
            ret_size,
            lambda byte_index: uninterpreted.delegate_call_return_byte(
                gas, addr, args_offset, args_size, ret_offset, ret_size,
                old_memory, byte_index, effect_id=evm_pc,
            ),
            effect_tag=f"delegatecall_{effect_suffix}",
        )
        if evm_pc is not None:
            should_copy = uninterpreted.delegate_call_should_copy_return_data(
                gas, addr, args_offset, args_size, ret_offset, ret_size,
                old_memory, effect_id=evm_pc,
            )
            mstate = self._write_call_return_data(
                mstate,
                ret_offset,
                ret_size,
                lambda byte_index: uninterpreted.delegate_call_return_byte(
                    gas, addr, args_offset, args_size, ret_offset, ret_size,
                    old_memory, byte_index, effect_id=evm_pc,
                ),
                effect_id=evm_pc,
                should_copy=should_copy,
            )
        sp, mstate = self._push_uint256(sp, result, mstate)
        mstate = self._update_sp_in_memory(sp, mstate)
        return mstate

    def _handle_static_call(self, sp: int, mstate: SMTState, evm_pc: Optional[int] = None) -> SMTState:
        """STATICCALL: 弹出 gas、addr、argsOffset、argsSize、retOffset、retSize，压入 success。"""
        gas, sp, mstate = self._pop_uint256(sp, mstate)
        addr, sp, mstate = self._pop_uint256(sp, mstate)
        args_offset, sp, mstate = self._pop_uint256(sp, mstate)
        args_size, sp, mstate = self._pop_uint256(sp, mstate)
        ret_offset, sp, mstate = self._pop_uint256(sp, mstate)
        ret_size, sp, mstate = self._pop_uint256(sp, mstate)
        old_memory = mstate.x86_memory.evm_mem
        result = uninterpreted.static_call_semantics(
            gas, addr, args_offset, args_size, ret_offset, ret_size,
            old_memory, effect_id=evm_pc)
        effect_suffix = evm_pc if evm_pc is not None else "global"
        mstate = self._update_return_data_source(
            mstate,
            ret_size,
            lambda byte_index: uninterpreted.static_call_return_byte(
                gas, addr, args_offset, args_size, ret_offset, ret_size,
                old_memory, byte_index, effect_id=evm_pc,
            ),
            effect_tag=f"staticcall_{effect_suffix}",
        )
        if evm_pc is not None:
            mstate = self._write_call_return_data(
                mstate,
                ret_offset,
                ret_size,
                lambda byte_index: uninterpreted.static_call_return_byte(
                    gas, addr, args_offset, args_size, ret_offset, ret_size,
                    old_memory, byte_index, effect_id=evm_pc,
                ),
                effect_id=evm_pc,
            )
        sp, mstate = self._push_uint256(sp, result, mstate)
        mstate = self._update_sp_in_memory(sp, mstate)
        return mstate

    def _handle_tload(self, sp: int, mstate: SMTState) -> SMTState:
        """TLOAD: pop key, push transient_storage[key]。"""
        key, sp, mstate = self._pop_uint256(sp, mstate)
        result = mstate.evm_transient_storage.tload(key)
        sp, mstate = self._push_uint256(sp, result, mstate)
        mstate = self._update_sp_in_memory(sp, mstate)
        return mstate

    def _handle_tstore(self, sp: int, mstate: SMTState) -> SMTState:
        """TSTORE: pop key, pop value, store to transient storage。"""
        key, sp, mstate = self._pop_uint256(sp, mstate)
        val, sp, mstate = self._pop_uint256(sp, mstate)
        mstate.evm_transient_storage = mstate.evm_transient_storage.tstore(key, val)
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
            # block 中未找到 func_index。
            # 这可能出现在测试场景，或 CFG 构建时缺少完整元数据。
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
            "memory_grow": self._handle_builtin_memory_grow,
            "stack_grow": self._handle_builtin_noop,      # 当前 amd64 AOT 未实际使用
            "calldatacopy": self._handle_builtin_noop,    # 拷贝语义由编译出的 x86 指令实现
            "returndatacopy": self._handle_builtin_noop,  # 拷贝语义由编译出的 x86 指令实现
            "div": self._handle_builtin_div,
            "mod": self._handle_builtin_mod,
            "addmod": self._handle_builtin_addmod,
            "mulmod": self._handle_builtin_mulmod,
            "exp": self._handle_builtin_exp,
            "gas_cost": self._handle_builtin_gas_cost,
        }.get(func_name)

        if handler is None:
            raise GoFunctionSemanticsError(
                f"unimplemented builtin function '{func_name}'"
            )

        return handler(sp, mstate)

    def _handle_builtin_noop(self, sp: int, mstate: SMTState) -> SMTState:  # noqa: ARG002
        """当前按空操作处理的 builtin。

        - stack_grow: 当前 amd64 AOT 未实际走到这里。
        - calldatacopy / returndatacopy: 真正的拷贝效果在编译出的 x86 指令中完成，
          这里不再重复建模。
        """
        return mstate

    def _handle_builtin_div(self, sp: int, mstate: SMTState) -> SMTState:
        """DIV builtin: 弹出 a、b，压入 a/b（按 EVM 语义，b==0 时返回 0）。"""
        a, sp, mstate = self._pop_uint256(sp, mstate)
        b, sp, mstate = self._pop_uint256(sp, mstate)
        result = arithmetic.div_semantics(a, b)
        sp, mstate = self._push_uint256(sp, result, mstate)
        mstate = self._update_sp_in_memory(sp, mstate)
        return mstate

    def _handle_builtin_mod(self, sp: int, mstate: SMTState) -> SMTState:
        """MOD builtin: 弹出 a、b，压入 a%b（按 EVM 语义，b==0 时返回 0）。"""
        a, sp, mstate = self._pop_uint256(sp, mstate)
        b, sp, mstate = self._pop_uint256(sp, mstate)
        result = arithmetic.mod_semantics(a, b)
        sp, mstate = self._push_uint256(sp, result, mstate)
        mstate = self._update_sp_in_memory(sp, mstate)
        return mstate

    def _handle_builtin_exp(self, sp: int, mstate: SMTState) -> SMTState:
        """EXP builtin: 弹出 base、exponent，压入 base^exponent。

        使用与IR侧相同的未解释函数。
        """
        base, sp, mstate = self._pop_uint256(sp, mstate)
        exponent, sp, mstate = self._pop_uint256(sp, mstate)
        result = arithmetic.exp_semantics(base, exponent)
        sp, mstate = self._push_uint256(sp, result, mstate)
        mstate = self._update_sp_in_memory(sp, mstate)
        return mstate

    def _handle_builtin_addmod(self, sp: int, mstate: SMTState) -> SMTState:
        """ADDMOD builtin: 弹出 a、b、mod，压入 (a+b)%mod。"""
        a, sp, mstate = self._pop_uint256(sp, mstate)
        b, sp, mstate = self._pop_uint256(sp, mstate)
        mod, sp, mstate = self._pop_uint256(sp, mstate)
        result = arithmetic.addmod_semantics(a, b, mod)
        sp, mstate = self._push_uint256(sp, result, mstate)
        mstate = self._update_sp_in_memory(sp, mstate)
        return mstate

    def _handle_builtin_mulmod(self, sp: int, mstate: SMTState) -> SMTState:
        """MULMOD builtin: 弹出 a、b、mod，压入 (a*b)%mod。"""
        a, sp, mstate = self._pop_uint256(sp, mstate)
        b, sp, mstate = self._pop_uint256(sp, mstate)
        mod, sp, mstate = self._pop_uint256(sp, mstate)
        result = arithmetic.mulmod_semantics(a, b, mod)
        sp, mstate = self._push_uint256(sp, result, mstate)
        mstate = self._update_sp_in_memory(sp, mstate)
        return mstate

    def _handle_builtin_memory_grow(self, sp: int, mstate: SMTState) -> SMTState:
        """处理 MEMORYGROW builtin。

        当前验证模型将它抽象为空操作，原因如下：

        1. 真实的 go-hpc-evm AOT 实现中，memory_grow 不是从 EVM 栈取参数，
           而是从 callEngine / evmArchContext 中读取 growNumber。
        2. 该 builtin 的主要副作用是扩展内存 buffer，并更新
           memoryElement0Address / memorySliceLen 这类运行时元数据。
        3. 本项目当前主要验证的是“栈效果”和“内存内容”的等价性，x86 内存也被
           建模为一个可按地址读写的无限 Z3 Array，因此不会显式验证 buffer 扩容、
           长度变化或扩容后的基址重定位。

        因此，这里不做栈 pop/push，也不修改 SMT 状态中的内存元数据。

        TODO:
        后续如果要更精确地贴近 go-hpc-evm AOT，需要补充对 callEngine 中
        growNumber、memoryElement0Address、memorySliceLen 等字段的建模，
        并在 memory_grow 后同步更新这些可观察状态，以验证内存扩容相关语义。
        """
        from z3 import BitVecVal
        from x86_64.models import Register

        new_page_count = mstate.callengine_builtin_arg0
        new_size_bytes = new_page_count << BitVecVal(5, 64)
        mstate.callengine_memory_size_bytes = new_size_bytes

        # 保持 x86_memory 中的 callEngine 元数据同步，避免慢路径读到旧值。
        r13 = mstate.x86_registers.get_register(Register.R13)
        mstate.x86_memory = mstate.x86_memory.store_64bit(
            r13 + BitVecVal(0x18, 64),
            new_size_bytes,
            domain=MemoryDomain.CALLENGINE,
        )
        return mstate

    def _handle_builtin_gas_cost(self, sp: int, mstate: SMTState) -> SMTState:
        """GAS_COST builtin: 弹出 gas 数值（Go: c.PopUint256().Uint64()，随后扣减 gasLimit）。

        Go runtime 的 dealWithGasCost 会弹出 1 个值，不压回结果。
        这里不对 gas 余额做等价性建模。
        """
        _gas, sp, mstate = self._pop_uint256(sp, mstate)
        mstate = self._update_sp_in_memory(sp, mstate)
        return mstate
