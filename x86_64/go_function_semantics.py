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

from z3 import And, BitVec, BitVecVal, If, Lambda, Select, UGE, ULT, simplify
from common.store_forwarding import memory_as_offset_view

from .aot_profile import X86AOTProfile
from state.smt_state import SMTState, MemoryDomain
from common import uninterpreted
from common import arithmetic
from common.u64 import truncate_to_64
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
        value = simplify(
            mstate.x86_memory.load_256bit(base_offset, domain=MemoryDomain.STACK)
        )
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
        mstate.x86_memory = mstate.x86_memory.store_256bit(
            base_offset,
            simplify(value),
            domain=MemoryDomain.STACK,
        )
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

    def _deduct_host_gas_uf(self, mstate: SMTState, opcode: str,
                            stack_args) -> None:
        """x86 侧扣 host-gas UF（与 EVM 侧 charge_host_gas_uf 同名相消）。

        stack_args 必须是该调用点刚 pop 出的、与 EVM 侧同序的栈值（两侧栈已由功能
        等价证明相等 → UF 同参相消）。仅 host_gas_uf_enabled 生效，且必须与 EVM 侧
        charge_host_gas_uf 同开同关。原理见 state/host_gas.py。
        """
        from state.host_gas import deduct_host_gas_uf_x86
        deduct_host_gas_uf_x86(
            mstate,
            opcode,
            stack_args,
            offsets=self.aot_profile.offsets,
            store_64bit=lambda addr, val, dom: mstate.x86_memory.store_64bit(
                addr, val, domain=dom
            ),
            callengine_domain=MemoryDomain.CALLENGINE,
        )

    def _clear_caller_saved_pointer_tags(self, mstate: SMTState) -> None:
        for reg in (
            Register.RAX, Register.RCX, Register.RDX, Register.RSI, Register.RDI,
            Register.R8, Register.R9, Register.R10, Register.R11,
        ):
            mstate.x86_registers.clear_pointer_tag(reg)

    def _update_return_data_source(self, mstate: SMTState, return_size: BitVec,
                                   byte_fn, effect_tag: str) -> SMTState:
        """host 调用后刷新 RETURNDATA 源（内容 + pointer + size）。

        `return_size` 必须是 host **实际返回的数据长度**（`len(res)`），**不是**
        调用方给出的输出缓冲区长度 `retSize`。两者在协议上是不同的量：自动拷贝
        只搬 min(retSize, len(res)) 字节，而 RETURNDATASIZE/RETURNDATACOPY 看到
        的是完整的 len(res)。

        曾经这里直接传 `ret_size`，于是两侧模型都只允许 size == retSize，真实
        返回长度整个落在量化域之外——一个混淆这两个量的 codegen 缺陷会被两侧的
        共同错误掩盖（假绿）。现在两侧改传同名的 `*_return_size` UF，取值相同
        故照常相消，而错误实现会因取值不同被抓住。
        """
        size_64 = truncate_to_64(return_size)
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

    def apply(
        self,
        status_code: int,
        func_index: Optional[int],
        sp: int,
        mstate: SMTState,
        evm_pc: Optional[int] = None,
        evm_immediate: Optional[int] = None,
    ) -> SMTState:
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
            result = self._dispatch_host_function(
                func_index,
                sp,
                mstate,
                evm_pc=evm_pc,
                evm_immediate=evm_immediate,
            )
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
                                evm_pc: Optional[int] = None,
                                evm_immediate: Optional[int] = None) -> SMTState:
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

        if func_name == "log":
            return self._handle_log(sp, mstate, evm_immediate=evm_immediate)

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
            "tload": self._handle_tload,
            "tstore": self._handle_tstore,
        }.get(func_name)

        if handler is None:
            raise GoFunctionSemanticsError(
                f"unimplemented host function '{func_name}'"
            )

        return handler(sp, mstate)

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
        """将一个符号化字节切片写入 x86 内存（EVM 256-bit memory，R15 域）。

        区间判定在 **offset 空间**（o = idx - R15）做，与 EVM 侧
        `evm_ir.semantics._write_symbolic_memory_slice` 逐字对齐：host 函数按 Go
        `Memory.Set(offset, size, …)` 的切片下标写入，本来就是 offset 语义。
        旧版在绝对地址空间比较 `UGE(idx, R15 + off)`，R15+off 回绕 2^64 时与 EVM
        侧判定不同（Safe 2586 / CErc20 4236 的 H2 memory 分量真 SAT，
        retOffset = 2^64-31）。R15+off+size 不回绕时（所有真实的成功写入）新旧
        语义相同。2026-10-03 经用户确认。
        """
        from x86_64.models import Register

        dest_offset_64 = truncate_to_64(dest_offset)
        size_64 = truncate_to_64(size)
        zero_64 = BitVecVal(0, 64)
        r15 = mstate.x86_registers.get_register(Register.R15)

        idx = BitVec(effect_tag, 64)
        offset = idx - r15
        relative = offset - dest_offset_64
        in_range = And(
            size_64 != zero_64,
            UGE(offset, dest_offset_64),
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
        # host gas UF，与 EVM 侧同参 [key] 相消。
        self._deduct_host_gas_uf(mstate, "SLOAD", [key])
        return mstate

    def _handle_sstore(self, sp: int, mstate: SMTState) -> SMTState:
        """SSTORE: pop key, pop value, Store(Storage, key, value)。"""
        key, sp, mstate = self._pop_uint256(sp, mstate)
        val, sp, mstate = self._pop_uint256(sp, mstate)
        # 与 EVM 侧同序：slot 原值必须在 sstore 之前取（gasSStoreEIP2929 的档位取决于
        # current 值），写完再取拿到的就是 val 本身。
        old_val = mstate.evm_storage.sload(key)
        mstate.evm_storage = mstate.evm_storage.sstore(key, val)
        mstate = self._update_sp_in_memory(sp, mstate)
        # host gas UF，与 EVM 侧同参 [key, val, old_val] 相消。
        self._deduct_host_gas_uf(mstate, "SSTORE", [key, val, old_val])
        return mstate

    def _handle_sha3(self, sp: int, mstate: SMTState) -> SMTState:
        """SHA3: pop offset, pop length, push sha3(memory, R15+offset, length)。"""
        offset_bv, sp, mstate = self._pop_uint256(sp, mstate)
        length_bv, sp, mstate = self._pop_uint256(sp, mstate)
        r15 = mstate.x86_registers.get_register(Register.R15)
        hash_val = uninterpreted.sha3_semantics(
            mstate.x86_memory.evm_mem,
            r15,
            offset_bv,
            length_bv,
        )
        sp, mstate = self._push_uint256(sp, hash_val, mstate)
        mstate = self._update_sp_in_memory(sp, mstate)
        return mstate

    def _handle_balance(self, sp: int, mstate: SMTState) -> SMTState:
        """BALANCE: pop address, push balance(address)。"""
        addr, sp, mstate = self._pop_uint256(sp, mstate)
        result = uninterpreted.balance_semantics(addr)
        sp, mstate = self._push_uint256(sp, result, mstate)
        mstate = self._update_sp_in_memory(sp, mstate)
        # host gas UF，与 EVM 侧同参 [addr] 相消。
        self._deduct_host_gas_uf(mstate, "BALANCE", [addr])
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
        # host gas UF，与 EVM 侧同参 [addr] 相消。
        self._deduct_host_gas_uf(mstate, "EXTCODESIZE", [addr])
        return mstate

    def _handle_ext_code_copy(self, sp: int, mstate: SMTState,
                              evm_pc: Optional[int] = None) -> SMTState:
        """EXTCODECOPY: 弹出 address、destOffset、offset、size，并符号化写入 x86 内存。"""
        addr, sp, mstate = self._pop_uint256(sp, mstate)
        dest_offset, sp, mstate = self._pop_uint256(sp, mstate)
        offset, sp, mstate = self._pop_uint256(sp, mstate)
        size, sp, mstate = self._pop_uint256(sp, mstate)
        effect_id = evm_pc if evm_pc is not None else 0
        mstate = self._write_symbolic_memory_slice(
            mstate,
            dest_offset,
            size,
            lambda byte_index: uninterpreted.ext_code_copy_byte(
                addr, offset, byte_index, effect_id=effect_id,
            ),
            effect_tag=f"extcodecopy_idx_{effect_id}",
        )
        mstate = self._update_sp_in_memory(sp, mstate)
        # host gas UF，与 EVM 侧同参 [addr, size] 相消。可见的内存扩展 + copy word
        # gas 由反汇编建模（checkMemoryAndCalcDynamicGasExtCodeCopy 是 compileEVM-
        # EXTCODECOPY 的第一条语句），两部分合起来使 EXTCODECOPY 在 gas 检查范围内。
        self._deduct_host_gas_uf(mstate, "EXTCODECOPY", [addr, size])
        return mstate

    def _handle_ext_code_hash(self, sp: int, mstate: SMTState) -> SMTState:
        """EXTCODEHASH: pop address, push extcodehash(address)。"""
        addr, sp, mstate = self._pop_uint256(sp, mstate)
        result = uninterpreted.ext_code_hash_semantics(addr)
        sp, mstate = self._push_uint256(sp, result, mstate)
        mstate = self._update_sp_in_memory(sp, mstate)
        # host gas UF，与 EVM 侧同参 [addr] 相消。
        self._deduct_host_gas_uf(mstate, "EXTCODEHASH", [addr])
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
        beneficiary, sp, mstate = self._pop_uint256(sp, mstate)
        mstate = self._update_sp_in_memory(sp, mstate)
        # host gas UF，与 EVM 侧同参 [beneficiary] 相消。
        self._deduct_host_gas_uf(mstate, "SELFDESTRUCT", [beneficiary])
        return mstate

    def _handle_log(
        self,
        sp: int,
        mstate: SMTState,
        evm_immediate: Optional[int] = None,
    ) -> SMTState:
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
        from z3 import is_bv_value, simplify
        n_topics_bv, sp, mstate = self._pop_uint256(sp, mstate)
        _mstart, sp, mstate = self._pop_uint256(sp, mstate)
        _msize, sp, mstate = self._pop_uint256(sp, mstate)

        # AOT 编译器只把 LOG topic 数写入低 64-bit limb，Go host.Log()
        # 也通过 Uint64() 读取它；高 limb 可能保留旧栈内容，不能参与比较。
        n_topics_low64 = truncate_to_64(n_topics_bv)
        n_topics_simplified = simplify(n_topics_low64)
        n_topics_from_stack = (
            n_topics_simplified.as_long() if is_bv_value(n_topics_simplified) else None
        )

        if evm_immediate is not None:
            # call-site mapping 顺序错配时，EVM 侧声称的 immediate 可能对应
            # 到错误的 x86 bridge site；两边都能确定时必须一致，否则说明
            # EVM↔x86 host-site 顺序匹配出了问题，fail-closed 报错而不是
            # 静默按 evm_immediate 弹出错误数量的栈元素、破坏 sp。
            if evm_immediate < 0 or evm_immediate > 4:
                raise GoFunctionSemanticsError(
                    f"LOG: invalid evm_immediate topic count {evm_immediate}; "
                    "expected LOG0..LOG4"
                )
            if n_topics_from_stack is None:
                raise GoFunctionSemanticsError(
                    "LOG: x86 stack n_topics low64 is symbolic while evm_immediate "
                    f"claims {evm_immediate}; cannot prove call-site mapping consistency"
                )
            if n_topics_from_stack != evm_immediate:
                raise GoFunctionSemanticsError(
                    "LOG: evm_immediate topic count "
                    f"({evm_immediate}) disagrees with x86 stack n_topics "
                    f"({n_topics_from_stack}); likely call-site mapping mismatch"
                )
            n = evm_immediate
        elif n_topics_from_stack is not None:
            n = n_topics_from_stack
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
        effect_id = evm_pc if evm_pc is not None else 0
        value, sp, mstate = self._pop_uint256(sp, mstate)
        offset, sp, mstate = self._pop_uint256(sp, mstate)
        size, sp, mstate = self._pop_uint256(sp, mstate)
        old_memory = memory_as_offset_view(
            mstate.x86_memory.evm_mem, mstate.x86_registers.get_register(Register.R15))
        result = uninterpreted.create_semantics(value, offset, size, old_memory, effect_id=effect_id)
        sp, mstate = self._push_uint256(sp, result, mstate)
        mstate = self._update_sp_in_memory(sp, mstate)
        # host gas UF，与 EVM 侧同参 [value, offset, size] 相消。returnGas 链与
        # CREATE 内存扩展是另外的可见机器码（已由反汇编建模），此 UF 只承载 host cost。
        self._deduct_host_gas_uf(mstate, "CREATE", [value, offset, size])
        # CREATE 同样刷新 returndata（成功→空，revert→reason）；与 EVM 侧同名
        # 同参 UF 相消。不刷新会保留调用前的旧数据，那是不可能的真实状态。
        mstate = self._update_return_data_source(
            mstate,
            uninterpreted.create_return_size(
                value, offset, size, old_memory, effect_id=effect_id,
            ),
            lambda byte_index: uninterpreted.create_return_byte(
                value, offset, size, old_memory, byte_index, effect_id=effect_id,
            ),
            effect_tag=f"create_{effect_id}",
        )
        return mstate

    def _handle_create2(self, sp: int, mstate: SMTState, evm_pc: Optional[int] = None) -> SMTState:
        """CREATE2: pop value, offset, size, salt; push new_address。"""
        effect_id = evm_pc if evm_pc is not None else 0
        value, sp, mstate = self._pop_uint256(sp, mstate)
        offset, sp, mstate = self._pop_uint256(sp, mstate)
        size, sp, mstate = self._pop_uint256(sp, mstate)
        salt, sp, mstate = self._pop_uint256(sp, mstate)
        old_memory = memory_as_offset_view(
            mstate.x86_memory.evm_mem, mstate.x86_registers.get_register(Register.R15))
        result = uninterpreted.create2_semantics(
            value, offset, size, salt, old_memory, effect_id=effect_id
        )
        sp, mstate = self._push_uint256(sp, result, mstate)
        mstate = self._update_sp_in_memory(sp, mstate)
        # host gas UF，与 EVM 侧同参 [value, offset, size, salt] 相消（同 CREATE）。
        self._deduct_host_gas_uf(mstate, "CREATE2", [value, offset, size, salt])
        mstate = self._update_return_data_source(
            mstate,
            uninterpreted.create2_return_size(
                value, offset, size, salt, old_memory, effect_id=effect_id,
            ),
            lambda byte_index: uninterpreted.create2_return_byte(
                value, offset, size, salt, old_memory, byte_index,
                effect_id=effect_id,
            ),
            effect_tag=f"create2_{effect_id}",
        )
        return mstate

    def _handle_call(self, sp: int, mstate: SMTState, evm_pc: Optional[int] = None) -> SMTState:
        """CALL: pop gas, addr, value, argsOffset, argsSize, retOffset, retSize; push success。"""
        effect_id = evm_pc if evm_pc is not None else 0
        gas, sp, mstate = self._pop_uint256(sp, mstate)
        addr, sp, mstate = self._pop_uint256(sp, mstate)
        value, sp, mstate = self._pop_uint256(sp, mstate)
        args_offset, sp, mstate = self._pop_uint256(sp, mstate)
        args_size, sp, mstate = self._pop_uint256(sp, mstate)
        ret_offset, sp, mstate = self._pop_uint256(sp, mstate)
        ret_size, sp, mstate = self._pop_uint256(sp, mstate)
        old_memory = memory_as_offset_view(
            mstate.x86_memory.evm_mem, mstate.x86_registers.get_register(Register.R15))
        result = uninterpreted.call_semantics(
            gas, addr, value, args_offset, args_size, ret_offset, ret_size,
            old_memory, effect_id=effect_id)
        effect_suffix = effect_id
        mstate = self._update_return_data_source(
            mstate,
            uninterpreted.call_return_size(
                gas, addr, value, args_offset, args_size, ret_offset, ret_size,
                old_memory, effect_id=effect_id,
            ),
            lambda byte_index: uninterpreted.call_return_byte(
                gas, addr, value, args_offset, args_size, ret_offset, ret_size,
                old_memory, byte_index, effect_id=effect_id,
            ),
            effect_tag=f"call_{effect_suffix}",
        )
        should_copy = uninterpreted.call_should_copy_return_data(
            gas, addr, value, args_offset, args_size, ret_offset, ret_size,
            old_memory, effect_id=effect_id,
        )
        mstate = self._write_call_return_data(
            mstate,
            ret_offset,
            ret_size,
            lambda byte_index: uninterpreted.call_return_byte(
                gas, addr, value, args_offset, args_size, ret_offset, ret_size,
                old_memory, byte_index, effect_id=effect_id,
            ),
            effect_id=effect_id,
            should_copy=should_copy,
        )
        sp, mstate = self._push_uint256(sp, result, mstate)
        mstate = self._update_sp_in_memory(sp, mstate)
        # host gas UF，与 EVM 侧同参 7 项相消。returnGas 链是另外的可见机器码（已
        # 建模、净额 0），且 CALL 无可见内存扩展，故此 UF 即全部 host gas。
        self._deduct_host_gas_uf(mstate, "CALL", [
            gas, addr, value, args_offset, args_size, ret_offset, ret_size,
        ])
        return mstate

    def _handle_call_code(self, sp: int, mstate: SMTState, evm_pc: Optional[int] = None) -> SMTState:
        """CALLCODE: 与 CALL 的参数签名相同，压入 success。"""
        effect_id = evm_pc if evm_pc is not None else 0
        gas, sp, mstate = self._pop_uint256(sp, mstate)
        addr, sp, mstate = self._pop_uint256(sp, mstate)
        value, sp, mstate = self._pop_uint256(sp, mstate)
        args_offset, sp, mstate = self._pop_uint256(sp, mstate)
        args_size, sp, mstate = self._pop_uint256(sp, mstate)
        ret_offset, sp, mstate = self._pop_uint256(sp, mstate)
        ret_size, sp, mstate = self._pop_uint256(sp, mstate)
        old_memory = memory_as_offset_view(
            mstate.x86_memory.evm_mem, mstate.x86_registers.get_register(Register.R15))
        result = uninterpreted.callcode_semantics(
            gas, addr, value, args_offset, args_size, ret_offset, ret_size,
            old_memory, effect_id=effect_id)
        effect_suffix = effect_id
        mstate = self._update_return_data_source(
            mstate,
            uninterpreted.callcode_return_size(
                gas, addr, value, args_offset, args_size, ret_offset, ret_size,
                old_memory, effect_id=effect_id,
            ),
            lambda byte_index: uninterpreted.callcode_return_byte(
                gas, addr, value, args_offset, args_size, ret_offset, ret_size,
                old_memory, byte_index, effect_id=effect_id,
            ),
            effect_tag=f"callcode_{effect_suffix}",
        )
        should_copy = uninterpreted.callcode_should_copy_return_data(
            gas, addr, value, args_offset, args_size, ret_offset, ret_size,
            old_memory, effect_id=effect_id,
        )
        mstate = self._write_call_return_data(
            mstate,
            ret_offset,
            ret_size,
            lambda byte_index: uninterpreted.callcode_return_byte(
                gas, addr, value, args_offset, args_size, ret_offset, ret_size,
                old_memory, byte_index, effect_id=effect_id,
            ),
            effect_id=effect_id,
            should_copy=should_copy,
        )
        sp, mstate = self._push_uint256(sp, result, mstate)
        mstate = self._update_sp_in_memory(sp, mstate)
        # host gas UF，与 EVM 侧同参 7 项相消（同 CALL）。
        self._deduct_host_gas_uf(mstate, "CALLCODE", [
            gas, addr, value, args_offset, args_size, ret_offset, ret_size,
        ])
        return mstate

    def _handle_delegate_call(self, sp: int, mstate: SMTState, evm_pc: Optional[int] = None) -> SMTState:
        """DELEGATECALL: 弹出 gas、addr、argsOffset、argsSize、retOffset、retSize，压入 success。"""
        effect_id = evm_pc if evm_pc is not None else 0
        gas, sp, mstate = self._pop_uint256(sp, mstate)
        addr, sp, mstate = self._pop_uint256(sp, mstate)
        args_offset, sp, mstate = self._pop_uint256(sp, mstate)
        args_size, sp, mstate = self._pop_uint256(sp, mstate)
        ret_offset, sp, mstate = self._pop_uint256(sp, mstate)
        ret_size, sp, mstate = self._pop_uint256(sp, mstate)
        old_memory = memory_as_offset_view(
            mstate.x86_memory.evm_mem, mstate.x86_registers.get_register(Register.R15))
        result = uninterpreted.delegate_call_semantics(
            gas, addr, args_offset, args_size, ret_offset, ret_size,
            old_memory, effect_id=effect_id)
        effect_suffix = effect_id
        mstate = self._update_return_data_source(
            mstate,
            uninterpreted.delegate_call_return_size(
                gas, addr, args_offset, args_size, ret_offset, ret_size,
                old_memory, effect_id=effect_id,
            ),
            lambda byte_index: uninterpreted.delegate_call_return_byte(
                gas, addr, args_offset, args_size, ret_offset, ret_size,
                old_memory, byte_index, effect_id=effect_id,
            ),
            effect_tag=f"delegatecall_{effect_suffix}",
        )
        should_copy = uninterpreted.delegate_call_should_copy_return_data(
            gas, addr, args_offset, args_size, ret_offset, ret_size,
            old_memory, effect_id=effect_id,
        )
        mstate = self._write_call_return_data(
            mstate,
            ret_offset,
            ret_size,
            lambda byte_index: uninterpreted.delegate_call_return_byte(
                gas, addr, args_offset, args_size, ret_offset, ret_size,
                old_memory, byte_index, effect_id=effect_id,
            ),
            effect_id=effect_id,
            should_copy=should_copy,
        )
        sp, mstate = self._push_uint256(sp, result, mstate)
        mstate = self._update_sp_in_memory(sp, mstate)
        # host gas UF，与 EVM 侧同参 6 项相消（无 value）。
        self._deduct_host_gas_uf(mstate, "DELEGATECALL", [
            gas, addr, args_offset, args_size, ret_offset, ret_size,
        ])
        return mstate

    def _handle_static_call(self, sp: int, mstate: SMTState, evm_pc: Optional[int] = None) -> SMTState:
        """STATICCALL: 弹出 gas、addr、argsOffset、argsSize、retOffset、retSize，压入 success。"""
        effect_id = evm_pc if evm_pc is not None else 0
        gas, sp, mstate = self._pop_uint256(sp, mstate)
        addr, sp, mstate = self._pop_uint256(sp, mstate)
        args_offset, sp, mstate = self._pop_uint256(sp, mstate)
        args_size, sp, mstate = self._pop_uint256(sp, mstate)
        ret_offset, sp, mstate = self._pop_uint256(sp, mstate)
        ret_size, sp, mstate = self._pop_uint256(sp, mstate)
        old_memory = memory_as_offset_view(
            mstate.x86_memory.evm_mem, mstate.x86_registers.get_register(Register.R15))
        result = uninterpreted.static_call_semantics(
            gas, addr, args_offset, args_size, ret_offset, ret_size,
            old_memory, effect_id=effect_id)
        effect_suffix = effect_id
        mstate = self._update_return_data_source(
            mstate,
            uninterpreted.static_call_return_size(
                gas, addr, args_offset, args_size, ret_offset, ret_size,
                old_memory, effect_id=effect_id,
            ),
            lambda byte_index: uninterpreted.static_call_return_byte(
                gas, addr, args_offset, args_size, ret_offset, ret_size,
                old_memory, byte_index, effect_id=effect_id,
            ),
            effect_tag=f"staticcall_{effect_suffix}",
        )
        mstate = self._write_call_return_data(
            mstate,
            ret_offset,
            ret_size,
            lambda byte_index: uninterpreted.static_call_return_byte(
                gas, addr, args_offset, args_size, ret_offset, ret_size,
                old_memory, byte_index, effect_id=effect_id,
            ),
            effect_id=effect_id,
        )
        sp, mstate = self._push_uint256(sp, result, mstate)
        mstate = self._update_sp_in_memory(sp, mstate)
        # host gas UF，与 EVM 侧同参 6 项相消（无 value）。
        self._deduct_host_gas_uf(mstate, "STATICCALL", [
            gas, addr, args_offset, args_size, ret_offset, ret_size,
        ])
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
        # 注入恒真的相等借位链桥接 lemma 实例（见 common/arithmetic 与
        # tests/composition/test_eq_borrow_chain_composition.py）：soundness 中性、
        # 纯提速。x86 侧 a/b 与 EVM 侧是不同符号，两侧各自挂，主路径
        # _collect_assumptions 会一并收集。
        mstate.add_assumption(arithmetic.eq_borrow_chain_assumption(a, b))
        # x86 `div r64` quotient_fits guard 的恒真 hint；仅用于 等价性检查提速。
        mstate.add_assumption(arithmetic.x86_div64_quotient_fits_assumption(a, b))
        mstate = self._update_sp_in_memory(sp, mstate)
        return mstate

    def _handle_builtin_mod(self, sp: int, mstate: SMTState) -> SMTState:
        """MOD builtin: 弹出 a、b，压入 a%b（按 EVM 语义，b==0 时返回 0）。"""
        a, sp, mstate = self._pop_uint256(sp, mstate)
        b, sp, mstate = self._pop_uint256(sp, mstate)
        result = arithmetic.mod_semantics(a, b)
        sp, mstate = self._push_uint256(sp, result, mstate)
        # 同 DIV：恒真的相等借位链桥接 lemma 实例（soundness 中性、纯提速）。
        mstate.add_assumption(arithmetic.eq_borrow_chain_assumption(a, b))
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
        # host gas UF，与 EVM 侧同参 [exponent] 相消（gas 在 dealWithExp 内，按
        # expByteLen 计费，机器码不可见）。
        self._deduct_host_gas_uf(mstate, "EXP", [exponent])
        return mstate

    def _handle_builtin_addmod(self, sp: int, mstate: SMTState) -> SMTState:
        """ADDMOD builtin: 弹出 a、b、mod，压入 (a+b)%mod。"""
        a, sp, mstate = self._pop_uint256(sp, mstate)
        b, sp, mstate = self._pop_uint256(sp, mstate)
        mod, sp, mstate = self._pop_uint256(sp, mstate)
        result = arithmetic.addmod_semantics(a, b, mod)
        sp, mstate = self._push_uint256(sp, result, mstate)
        # 与 EVM ADDMOD 语义保持同一来源：挂恒真的相等借位链桥接 hint（soundness 中性、
        # 纯提速），用于 ADDMOD 不溢出路径内联 holiman Mod 的对齐。见 _handle_builtin_mod。
        for assumption in arithmetic.addmod_speedup_assumptions(a, b, mod):
            mstate.add_assumption(assumption)
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

        这里同步更新 memory size side-channel [R13+0x18]，镜像 Go dealWithMemoryGrow：

            targetMemSize := c.growNumber        // [R13+0x108]，已是 rounded byte size
            if targetMemSize > memLen { ... }    // 只增不减

        - growNumber **本身就是 rounded byte size**（native code 写的是 memWords<<5），
          直接用、不能再 <<5。曾有个 `gas off` 分支保留 `<<5`（把字节当 word 数、放大
          32 倍），那是遗留 bug：它让 x86 的 [R13+0x18] 与 EVM 侧 bookkeeping 分叉，
          下一次 expansion fee 与 OOG 阈值两侧就不同。
        - 只增不减：无条件覆盖会在 target < memLen 时让内存缩小（重复扣费、
          `newTotal - lastGasCost` 减法下溢），也与 EVM 侧 memory_expansion_fee 的
          `If(rounded>old, rounded, old)` 不对齐。
        """
        from z3 import If, UGT

        # growNumber 已是 rounded byte size（target memory size）。
        target = mstate.callengine_builtin_arg0
        old_size = mstate.callengine_memory_size_bytes
        new_size_bytes = If(UGT(target, old_size), target, old_size)

        # 保持 x86_memory 中的 callEngine 元数据同步，避免慢路径读到旧值。
        self._sync_callengine_u64_field(
            mstate,
            "memory_size",
            "callengine_memory_size_bytes",
            new_size_bytes,
        )
        return mstate

    def _handle_builtin_gas_cost(self, sp: int, mstate: SMTState) -> SMTState:
        """GAS_COST builtin: 弹出 gas 数值（Go: c.PopUint256().Uint64()，随后扣减 gasLimit）。

        Go runtime 的 dealWithGasCost 会弹出 1 个值，不压回结果。
        这里不对 gas 余额做等价性建模。

        已知 gap：本 builtin 不扣 host-gas UF。当前没有指令经它路由 gas，故无影响。

        若将来 codegen 改走 dealWithGasCost，风险分两种，只有后者是静默的：

        - 该指令**已登记**进 program_verifier._DYNAMIC_GAS_KINDS：EVM 侧照扣（UF 或真实
          公式）、x86 侧不扣 ⟹ 两侧 gas 不等 ⟹ SAT，**fail-loud**，不会假绿。
        - 该指令**未登记**：两侧都不扣，静默不验。这才是要防的，也是登记表存在的理由。

        补救：在此补 UF；若一时补不了，把该指令加进
        program_verifier._MANUAL_REJECT_KINDS 挡回门外（拒绝集是
        `(_DYNAMIC_GAS_KINDS - _MODELED_DYNAMIC_GAS_KINDS) | _MANUAL_REJECT_KINDS`）。
        """
        _gas, sp, mstate = self._pop_uint256(sp, mstate)
        mstate = self._update_sp_in_memory(sp, mstate)
        return mstate
