"""
EVM IR语义建模。

本模块使用Z3为EVM IR操作提供语义建模。
"""

from z3 import BitVec, BitVecRef, BitVecVal, Extract, If, UGE, ULT, And, Not, Or, LShR, ZeroExt, Lambda, Select, is_false, is_true, simplify
from typing import List, Optional, Dict, Any, Tuple
from . import semantics_gas
from .models import EVMBlock, EvmOperator
from evm_ir.status_code import EvmStatusCode, set_terminal_status
from common.uint256 import Uint256
from common import uninterpreted
from common.calldata import calldataload_no_overflow_assumption, calldataload_word
from common.u64 import truncate_to_64, to_u64_with_overflow_max
from common.arithmetic import (
    addmod_semantics as _addmod_semantics,
    addmod_speedup_assumptions as _addmod_speedup_assumptions,
    div_semantics as _div_semantics,
    eq_borrow_chain_assumption,
    exp_semantics as _exp_semantics,
    mod_semantics as _mod_semantics,
    mulmod_semantics as _mulmod_semantics,
    sdiv_semantics as _sdiv_semantics,
    sdiv_speedup_assumptions as _sdiv_speedup_assumptions,
    smod_semantics as _smod_semantics,
    smod_speedup_assumptions as _smod_speedup_assumptions,
    x86_div64_quotient_fits_assumption,
)
from state.smt_state import SMTState, EVMStackState, EVMMemoryState, PendingErrorBranch
from state.evm_gas_state import CREATE2_WORD_GAS, INIT_CODE_WORD_GAS

# RETURN指令的常量
MAX_RETURN_DATA_SIZE = 256  # 最大返回数据大小（字节）（256字节 = 2048位）


def _go_getdata_byte(byte_array,
                     start_64: BitVecRef,
                     source_size_64: BitVecRef,
                     relative_64: BitVecRef) -> BitVecRef:
    """Model one byte of Go getData(data, start, size)'s padded result."""
    if start_64.size() != 64:
        raise ValueError(f"getData start must be 64 bits, got {start_64.size()}")
    if source_size_64.size() != 64:
        raise ValueError(f"getData source size must be 64 bits, got {source_size_64.size()}")
    if relative_64.size() != 64:
        raise ValueError(f"getData relative index must be 64 bits, got {relative_64.size()}")

    effective_start = If(ULT(source_size_64, start_64), source_size_64, start_64)
    remaining = source_size_64 - effective_start
    return If(
        ULT(relative_64, remaining),
        Select(byte_array, effective_start + relative_64),
        BitVecVal(0, 8),
    )


def _write_call_return_data(memory_state: EVMMemoryState,
                            ret_offset_bv: BitVecRef,
                            ret_size_bv: BitVecRef,
                            return_byte_fn,
                            effect_id: int,
                            should_copy=None) -> EVMMemoryState:
    """Apply symbolic call return-data writes without changing MSize.

    当前模型不包含 host 内部的 CALL 内存扩展，因此两侧均保持 MSize；
    将 host 内存副作用纳入验证时必须同步更新这里。
    """
    return _write_symbolic_memory_slice(
        memory_state,
        ret_offset_bv,
        ret_size_bv,
        return_byte_fn,
        effect_tag=f"call_ret_idx_{effect_id}",
        should_copy=should_copy,
    )


def _update_call_return_data_source(state: SMTState,
                                    return_size_bv: BitVecRef,
                                    return_byte_fn,
                                    effect_tag: str) -> None:
    """CALL 族执行后更新 RETURNDATA **源**（内容 Array + pointer + size）。

    与 x86 侧 `go_function_semantics._update_return_data_source` 逐字对应：同一个
    return-byte UF、同一个 `effect_tag` ⇒ 两侧 Lambda 体与 `*_returndata_ptr` 自由
    符号同名同参，Z3 里相消。

    **为什么必须有**：`_write_call_return_data` 只把返回字节拷进 `evm_memory` 的
    `[retOffset, retOffset+retSize)`，那是 CALL 的自动拷贝语义；而 RETURNDATASIZE
    与 RETURNDATACOPY 读的是 `callengine_return_data_size_bytes` / `state.return_data`
    这一对**独立**字段。x86 侧四个 host-call handler 都更新它们，EVM 侧此前完全不更新
    ——于是 `CALL; RETURNDATASIZE` 两侧分叉（EVM 停在初始值，x86 已更新）。现有
    fixture 都用 `create_initial_state(return_data_size_bytes=…)` 预设初值、没有
    "CALL 之后再读" 的组合，所以这条缺口一直没被测到。

    与 `_write_call_return_data` 的分工：那个写 **memory**（拷贝目的地），这个写
    **return-data 源**（后续 RETURNDATA* 的读取对象），两者都要做。

    **`return_size_bv` 必须是 host 实际返回的长度 `len(res)`，不是调用方给的
    `retSize`**：自动拷贝只搬 min(retSize, len(res)) 字节，而 RETURNDATASIZE
    看到的是完整的 len(res)。直接用 retSize 会让两侧同时把真实返回长度排除在
    量化域外，混淆这两个量的 codegen 缺陷就会被共同错误掩盖。两侧取同名
    `uninterpreted.*_return_size` UF ⇒ 取值相同、照常相消。
    """
    size_64 = truncate_to_64(return_size_bv)
    idx = BitVec(f"{effect_tag}_returndata_idx", 64)
    old_return_data = state.return_data
    state.return_data = Lambda(
        idx,
        If(ULT(idx, size_64), return_byte_fn(idx), Select(old_return_data, idx)),
    )
    # pointer 是 host 返回的不透明地址：两侧取同名自由符号即可相等，语义上不被读。
    state.callengine_return_data_pointer = BitVec(
        f"{effect_tag}_returndata_ptr", 64
    )
    state.callengine_return_data_size_bytes = size_64


def _write_symbolic_memory_slice(memory_state: EVMMemoryState,
                                 dest_offset_bv: BitVecRef,
                                 size_bv: BitVecRef,
                                 byte_fn,
                                 effect_tag: str,
                                 should_copy=None) -> EVMMemoryState:
    """Apply a symbolic byte-slice write while preserving MSize.

    内存扩展由调用方负责建模。
    """
    dest_offset_64 = truncate_to_64(dest_offset_bv)
    size_64 = truncate_to_64(size_bv)
    zero_64 = BitVecVal(0, 64)
    idx = BitVec(effect_tag, 64)
    relative = idx - dest_offset_64
    in_range = And(
        size_64 != zero_64,
        UGE(idx, dest_offset_64),
        ULT(relative, size_64),
    )
    write_cond = in_range if should_copy is None else And(should_copy, in_range)
    updated_memory = Lambda(idx, If(write_cond, byte_fn(relative), Select(memory_state.Memory, idx)))

    return EVMMemoryState(memory_array=updated_memory, msize=memory_state.MSize)


class EVMOperationSemantics:
    """单个EVM操作的语义建模。"""
    
    def _to_uint256(self, a: Any) -> Uint256:
        """将输入转换为Uint256。"""
        if isinstance(a, BitVecRef) and a.size() == 256:
            return Uint256.from_bv256(a)
        elif isinstance(a, Uint256):
            return a
        elif hasattr(a, 'to_bv256'):
            return Uint256.from_bv256(a.to_bv256())
        elif isinstance(a, int):
            return Uint256.from_int(a)
        else:
            raise ValueError(f"Unsupported type for operand: {type(a)}")

    def _to_bv256(self, a: Any) -> BitVecRef:
        """将输入转换为256位BitVec。"""
        if isinstance(a, BitVecRef) and a.size() == 256:
            return a
        return self._to_uint256(a).to_bv256()

    def add_semantics(self, a: BitVec, b: BitVec) -> BitVec:
        """构建EVM ADD操作的逻辑公式。"""
        a_uint = self._to_uint256(a)
        b_uint = self._to_uint256(b)
        result_uint = a_uint.add_semantics(b_uint)
        return result_uint.to_bv256()

    def sub_semantics(self, a: BitVec, b: BitVec) -> BitVec:
        """构建EVM SUB操作的逻辑公式。"""
        a_uint = self._to_uint256(a)
        b_uint = self._to_uint256(b)
        result_uint = a_uint.sub_semantics(b_uint)
        return result_uint.to_bv256()

    def mul_semantics(self, a: BitVec, b: BitVec) -> BitVec:
        """构建EVM MUL操作的逻辑公式。"""
        a_uint = self._to_uint256(a)
        b_uint = self._to_uint256(b)
        result_uint = a_uint.mul_semantics(b_uint)
        return result_uint.to_bv256()

    def div_semantics(self, a: BitVec, b: BitVec) -> BitVec:
        """构建EVM DIV操作的逻辑公式 (a / b)。"""
        return _div_semantics(self._to_bv256(a), self._to_bv256(b))

    def mod_semantics(self, a: BitVec, b: BitVec) -> BitVec:
        """构建EVM MOD操作的逻辑公式 (a % b)。"""
        return _mod_semantics(self._to_bv256(a), self._to_bv256(b))

    def sdiv_semantics(self, a: BitVec, b: BitVec) -> BitVec:
        """构建EVM SDIV操作的逻辑公式 (a sdiv b)。

        镜像 holiman 符号分段（复用已转正的 unsigned div_semantics），避免裸 bvsdiv
        让 Z3 bit-blast 256-bit 有符号除法而超时。
        """
        return _sdiv_semantics(self._to_bv256(a), self._to_bv256(b))

    def smod_semantics(self, a: BitVec, b: BitVec) -> BitVec:
        """构建EVM SMOD操作的逻辑公式。

        镜像 holiman 符号分段（复用已转正的 unsigned mod_semantics）。
        """
        return _smod_semantics(self._to_bv256(a), self._to_bv256(b))

    def lt_semantics(self, a: BitVec, b: BitVec) -> BitVec:
        """构建EVM LT操作的逻辑公式 (a < b)。"""
        a_uint = self._to_uint256(a)
        b_uint = self._to_uint256(b)
        # Uint256.lt_semantics returns BoolRef, need to convert to BitVec(0/1)
        return If(a_uint.lt_semantics(b_uint), BitVecVal(1, 256), BitVecVal(0, 256))

    def gt_semantics(self, a: BitVec, b: BitVec) -> BitVec:
        """构建EVM GT操作的逻辑公式 (a > b)。"""
        a_uint = self._to_uint256(a)
        b_uint = self._to_uint256(b)
        return If(a_uint.gt_semantics(b_uint), BitVecVal(1, 256), BitVecVal(0, 256))

    def slt_semantics(self, a: BitVec, b: BitVec) -> BitVec:
        """构建EVM SLT操作的逻辑公式 (a < b, signed)。"""
        a_uint = self._to_uint256(a)
        b_uint = self._to_uint256(b)
        return If(a_uint.slt_semantics(b_uint), BitVecVal(1, 256), BitVecVal(0, 256))

    def sgt_semantics(self, a: BitVec, b: BitVec) -> BitVec:
        """构建EVM SGT操作的逻辑公式 (a > b, signed)。"""
        a_uint = self._to_uint256(a)
        b_uint = self._to_uint256(b)
        return If(a_uint.sgt_semantics(b_uint), BitVecVal(1, 256), BitVecVal(0, 256))

    def eq_semantics(self, a: BitVec, b: BitVec) -> BitVec:
        """构建EVM EQ操作的逻辑公式 (a == b)。"""
        a_uint = self._to_uint256(a)
        b_uint = self._to_uint256(b)
        return If(a_uint.eq_semantics(b_uint), BitVecVal(1, 256), BitVecVal(0, 256))

    def iszero_semantics(self, a: BitVec) -> BitVec:
        """构建EVM ISZERO操作的逻辑公式 (a == 0)。"""
        a_uint = self._to_uint256(a)
        return If(a_uint.iszero_semantics(), BitVecVal(1, 256), BitVecVal(0, 256))

    def and_semantics(self, a: BitVec, b: BitVec) -> BitVec:
        """构建EVM AND操作的逻辑公式 (a & b)。"""
        a_uint = self._to_uint256(a)
        b_uint = self._to_uint256(b)
        return a_uint.and_semantics(b_uint).to_bv256()

    def or_semantics(self, a: BitVec, b: BitVec) -> BitVec:
        """构建EVM OR操作的逻辑公式 (a | b)。"""
        a_uint = self._to_uint256(a)
        b_uint = self._to_uint256(b)
        return a_uint.or_semantics(b_uint).to_bv256()

    def xor_semantics(self, a: BitVec, b: BitVec) -> BitVec:
        """构建EVM XOR操作的逻辑公式 (a ^ b)。"""
        a_uint = self._to_uint256(a)
        b_uint = self._to_uint256(b)
        return a_uint.xor_semantics(b_uint).to_bv256()

    def not_semantics(self, a: BitVec) -> BitVec:
        """构建EVM NOT操作的逻辑公式 (~a)。"""
        a_uint = self._to_uint256(a)
        return a_uint.not_semantics().to_bv256()

    def exp_semantics(self, base: BitVec, exponent: BitVec) -> BitVec:
        """构建EVM EXP操作的逻辑公式 (base^exponent)。"""
        return _exp_semantics(base, exponent)

    def signextend_semantics(self, index: BitVec, value: BitVec) -> BitVec:
        """构建EVM SIGNEXTEND操作的逻辑公式。"""
        index_bv = self._to_bv256(index)
        value_bv = self._to_bv256(value)
        # index >= 32 时，返回原值
        out_of_range = UGE(index_bv, BitVecVal(32, 256))
        result = value_bv

        # 有限展开 0..31 字节，避免动态 Extract
        for i in range(31, -1, -1):
            bit_index = i * 8 + 7
            low_mask = BitVecVal((1 << (bit_index + 1)) - 1, 256)
            sign_bit = Extract(bit_index, bit_index, value_bv)
            extended = If(
                sign_bit == BitVecVal(1, 1),
                value_bv | (~low_mask),
                value_bv & low_mask
            )
            result = If(index_bv == BitVecVal(i, 256), extended, result)

        return If(out_of_range, value_bv, result)

    def byte_semantics(self, index: BitVec, value: BitVec) -> BitVec:
        """构建EVM BYTE操作的逻辑公式。"""
        index_bv = self._to_bv256(index)
        value_bv = self._to_bv256(value)
        zero_256 = BitVecVal(0, 256)
        result = zero_256

        # index=0 取最高字节（bits[255:248]），index=31 取最低字节
        for i in range(31, -1, -1):
            byte_i = ZeroExt(248, Extract(255 - 8 * i, 248 - 8 * i, value_bv))
            result = If(index_bv == BitVecVal(i, 256), byte_i, result)

        return If(UGE(index_bv, BitVecVal(32, 256)), zero_256, result)

    def addmod_semantics(self, a: BitVec, b: BitVec, mod: BitVec) -> BitVec:
        """构建EVM ADDMOD操作的逻辑公式。"""
        return _addmod_semantics(self._to_bv256(a), self._to_bv256(b), self._to_bv256(mod))

    def mulmod_semantics(self, a: BitVec, b: BitVec, mod: BitVec) -> BitVec:
        """构建EVM MULMOD操作的逻辑公式。"""
        return _mulmod_semantics(self._to_bv256(a), self._to_bv256(b), self._to_bv256(mod))

    def shl_semantics(self, value: BitVec, shift: BitVec) -> BitVec:
        """构建EVM SHL操作的逻辑公式。"""
        value_bv = self._to_bv256(value)
        shift_bv = self._to_bv256(shift)
        return If(
            UGE(shift_bv, BitVecVal(256, 256)),
            BitVecVal(0, 256),
            value_bv << shift_bv
        )

    def shr_semantics(self, value: BitVec, shift: BitVec) -> BitVec:
        """构建EVM SHR操作的逻辑公式。"""
        value_bv = self._to_bv256(value)
        shift_bv = self._to_bv256(shift)
        return If(
            UGE(shift_bv, BitVecVal(256, 256)),
            BitVecVal(0, 256),
            LShR(value_bv, shift_bv)
        )

    def sar_semantics(self, value: BitVec, shift: BitVec) -> BitVec:
        """构建EVM SAR操作的逻辑公式。"""
        value_bv = self._to_bv256(value)
        shift_bv = self._to_bv256(shift)
        zero_256 = BitVecVal(0, 256)
        all_ones = BitVecVal((1 << 256) - 1, 256)
        sign_is_negative = Extract(255, 255, value_bv) == BitVecVal(1, 1)
        return If(
            UGE(shift_bv, BitVecVal(256, 256)),
            If(sign_is_negative, all_ones, zero_256),
            value_bv >> shift_bv
        )

    def push_semantics(self, immediate: int, param: int = 1) -> BitVec:
        """构建EVM PUSH操作的逻辑公式。
        
        Args:
            immediate: 要推送的立即值
            param: 字节数（PUSH1-PUSH32为1-32）
            
        Returns:
            表示推送值的逻辑公式，作为256位BitVec
        """
        # PUSH操作将立即值推送到栈上
        # 立即值右填充到256位
        return BitVecVal(immediate, 256)
    
    def operation_semantics(self, op: EvmOperator, inputs: List[BitVec]) -> BitVec:
        """获取操作的语义公式。
        
        Args:
            op: EVM操作
            inputs: 输入值列表（256位BitVecs）
            
        Returns:
            作为256位BitVec的输出值
        """
        kind = op.kind.upper()
        
        if kind == "ADD":
            if len(inputs) < 2:
                raise ValueError("ADD requires 2 inputs")
            return self.add_semantics(inputs[0], inputs[1])

        elif kind == "SUB":
            if len(inputs) < 2:
                raise ValueError("SUB requires 2 inputs")
            return self.sub_semantics(inputs[0], inputs[1])

        elif kind == "MUL":
            if len(inputs) < 2:
                raise ValueError("MUL requires 2 inputs")
            return self.mul_semantics(inputs[0], inputs[1])

        elif kind == "DIV":
            if len(inputs) < 2:
                raise ValueError("DIV requires 2 inputs")
            return self.div_semantics(inputs[0], inputs[1])

        elif kind == "MOD":
            if len(inputs) < 2:
                raise ValueError("MOD requires 2 inputs")
            return self.mod_semantics(inputs[0], inputs[1])

        elif kind == "SDIV":
            if len(inputs) < 2:
                raise ValueError("SDIV requires 2 inputs")
            return self.sdiv_semantics(inputs[0], inputs[1])

        elif kind == "SMOD":
            if len(inputs) < 2:
                raise ValueError("SMOD requires 2 inputs")
            return self.smod_semantics(inputs[0], inputs[1])

        elif kind == "EXP":
            if len(inputs) < 2:
                raise ValueError("EXP requires 2 inputs")
            return self.exp_semantics(inputs[0], inputs[1])

        elif kind == "SLT":
            if len(inputs) < 2:
                raise ValueError("SLT requires 2 inputs")
            return self.slt_semantics(inputs[0], inputs[1])

        elif kind == "SGT":
            if len(inputs) < 2:
                raise ValueError("SGT requires 2 inputs")
            return self.sgt_semantics(inputs[0], inputs[1])

        elif kind == "LT":
            if len(inputs) < 2:
                raise ValueError("LT requires 2 inputs")
            return self.lt_semantics(inputs[0], inputs[1])

        elif kind == "GT":
            if len(inputs) < 2:
                raise ValueError("GT requires 2 inputs")
            return self.gt_semantics(inputs[0], inputs[1])

        elif kind == "EQ":
            if len(inputs) < 2:
                raise ValueError("EQ requires 2 inputs")
            return self.eq_semantics(inputs[0], inputs[1])

        elif kind == "ISZERO":
            if len(inputs) < 1:
                raise ValueError("ISZERO requires 1 input")
            return self.iszero_semantics(inputs[0])

        elif kind == "AND":
            if len(inputs) < 2:
                raise ValueError("AND requires 2 inputs")
            return self.and_semantics(inputs[0], inputs[1])

        elif kind == "OR":
            if len(inputs) < 2:
                raise ValueError("OR requires 2 inputs")
            return self.or_semantics(inputs[0], inputs[1])

        elif kind == "XOR":
            if len(inputs) < 2:
                raise ValueError("XOR requires 2 inputs")
            return self.xor_semantics(inputs[0], inputs[1])

        elif kind == "NOT":
            if len(inputs) < 1:
                raise ValueError("NOT requires 1 input")
            return self.not_semantics(inputs[0])

        elif kind == "SIGNEXTEND":
            if len(inputs) < 2:
                raise ValueError("SIGNEXTEND requires 2 inputs")
            return self.signextend_semantics(inputs[0], inputs[1])

        elif kind == "BYTE":
            if len(inputs) < 2:
                raise ValueError("BYTE requires 2 inputs")
            return self.byte_semantics(inputs[0], inputs[1])

        elif kind == "ADDMOD":
            if len(inputs) < 3:
                raise ValueError("ADDMOD requires 3 inputs")
            return self.addmod_semantics(inputs[0], inputs[1], inputs[2])

        elif kind == "MULMOD":
            if len(inputs) < 3:
                raise ValueError("MULMOD requires 3 inputs")
            return self.mulmod_semantics(inputs[0], inputs[1], inputs[2])

        elif kind == "SHL":
            if len(inputs) < 2:
                raise ValueError("SHL requires 2 inputs")
            return self.shl_semantics(inputs[0], inputs[1])

        elif kind == "SHR":
            if len(inputs) < 2:
                raise ValueError("SHR requires 2 inputs")
            return self.shr_semantics(inputs[0], inputs[1])

        elif kind == "SAR":
            if len(inputs) < 2:
                raise ValueError("SAR requires 2 inputs")
            return self.sar_semantics(inputs[0], inputs[1])
        
        elif kind.startswith("PUSH"):
            if op.immediate is None:
                raise ValueError("PUSH operation requires immediate value")
            return self.push_semantics(op.immediate, op.param or 1)
        
        else:
            raise NotImplementedError(f"Operation {kind} not yet implemented")


class EVMIRSemantics:
    """EVM IR块的语义建模。"""
    
    def __init__(self):
        """初始化EVM IR语义模型。"""
        self.op_semantics = EVMOperationSemantics()

def _jump_target_candidates(op: EvmOperator, state: "SMTState") -> "Optional[List[int]]":
    """返回本次跳转的合法落地集合，对齐 codegen（impl_amd64.go compileEVMJUMP）。

    三种返回值：

    - **候选列表**：ImmediateSet 即 codegen 逐个 CMPQ 的候选（IR 层已保证元素在
      targetBlocks 内，symbolic_jump_resolver.go:565）；否则取 valid_jump_targets，
      对应 c.jumpTable，覆盖静态 Immediate 形态。
    - **空列表**：一个 JUMPDEST 都没有，比较链为空直接落到 exit(InvalidJump)，
      任何 taken 跳转都非法。
    - **None**：valid_jump_targets 未预填充，调用方不施加校验。

    ``op.immediate_set`` 用 truthiness 对齐 codegen 的 ``len(o.ImmediateSet) > 0``
    （impl_amd64.go:3443/3482）——空 ImmediateSet 在 Go 里走 else 分支，不是
    "零候选全部非法"。真动态跳转由 cfg_executor 以 UnsupportedJumpError 拒绝。
    """
    if op.immediate_set:
        return list(op.immediate_set)

    if state.valid_jump_targets is not None:
        return sorted(state.valid_jump_targets)

    return None


def _apply_jump_destination_check(
    op: EvmOperator,
    state: "SMTState",
    dest_bv: "BitVecRef",
    taken_cond: "Optional[Any]" = None,
) -> None:
    """把 "dest 非法 -> INVALID_JUMP" 追加成一条待分裂的错误路径。

    这是 INVALID_JUMP 的唯一来源：executor 把它分裂成独立终止状态，非法目标走不到
    ``_handle_jump``，那里的 missing_jump_target 异常因此只是 CFG 内部一致性保护。

    - 候选恒小于 2^64，``dest == target`` 已蕴含 codegen 的 compileLocIsUint64 检查。
    - ``taken_cond`` 用于 JUMPI：未跳转路径 codegen 直接 fallthrough，不走比较链。
    - 必须在 dest 弹栈之后调用（对齐 popUint256 在比较链之前），否则错误快照的
      栈状态与 x86 的 exit 时刻不一致。
    - 局限：``valid_jump_targets`` 未预填充时校验**静默跳过**，非 fail-closed
      （见 ``_jump_target_candidates`` 的 None 分支）。全程序路径由
      SymbolicExecutor.__init__ 填全集，单指令测试用 evm_valid_jump_targets。
    """
    targets = _jump_target_candidates(op, state)
    if targets is None:
        return

    is_valid = Or([dest_bv == BitVecVal(t, 256) for t in targets])

    if taken_cond is not None:
        is_valid = Or(Not(taken_cond), is_valid)

    is_valid = simplify(is_valid)
    if is_true(is_valid):
        return

    state.pending_errors.append(
        PendingErrorBranch(
            condition=Not(is_valid),
            status_code=EvmStatusCode.INVALID_JUMP,
            terminal_state=state.snapshot_for_error_branch(),
        )
    )


def evm_operator_to_z3(op: EvmOperator, state: SMTState) -> SMTState:
    """将EVM操作符转换为Z3公式，更新状态。
    
    这是Alive2风格的直接公式构建方法。
    每个操作符直接构建Z3表达式，无需执行模拟。
    
    Args:
        op: 要转换的EVM操作符
        state: 当前SMT状态（将被修改）
        
    Returns:
        更新后的SMT状态
    """
    kind = op.kind.upper()
    op_semantics = EVMOperationSemantics()
    
    if kind == "TAG":
        # TAG 对语义是无操作（仅标记块入口）。
        # 合法跳转目标集合不在这里增量收集：执行到某个 JUMP 时后继块可能尚未被访问，
        # 收到的会是部分集合，据此判定跳转非法会产生假反例。该集合由
        # SymbolicExecutor 在执行前按全部块一次性预填充（见 cfg_executor.py）。
        return state
    
    elif kind == "BLOCKEND":
        # BLOCKEND对语义是无操作（仅标记块结束）
        return state
    
    elif kind == "ADD":
        b, stack_after_pop1 = state.evm_stack.pop()
        a, stack_after_pop2 = stack_after_pop1.pop()
        result = op_semantics.add_semantics(a, b)
        state.evm_stack = stack_after_pop2.push(result)
        return state

    elif kind == "SUB":
        a, stack_after_pop1 = state.evm_stack.pop()
        b, stack_after_pop2 = stack_after_pop1.pop()
        result = op_semantics.sub_semantics(a, b)
        state.evm_stack = stack_after_pop2.push(result)
        return state

    elif kind == "MUL":
        a, stack_after_pop1 = state.evm_stack.pop()
        b, stack_after_pop2 = stack_after_pop1.pop()
        result = op_semantics.mul_semantics(a, b)
        state.evm_stack = stack_after_pop2.push(result)
        return state

    elif kind == "DIV":
        a, stack_after_pop1 = state.evm_stack.pop()
        b, stack_after_pop2 = stack_after_pop1.pop()
        result = op_semantics.div_semantics(a, b)
        state.evm_stack = stack_after_pop2.push(result)
        # 注入相等借位链桥接：a==b ⟺ ¬(a<b)∧¬(b<a)。这是被 composition lemma
        # （tests/composition/test_eq_borrow_chain_composition.py）证明的恒真式，
        # 不限制输入空间、soundness 中性——纯粹给 solver 一个提速 hint，让它把
        # x86 codegen 的借位链条件与忠实参照（eq_semantics）对齐，而无需自己做
        # 256-bit 借位↔limb相等的慢桥接。与 CALLDATALOAD 那种"限制输入"假设不同。
        state.add_assumption(eq_borrow_chain_assumption(a, b))
        # x86 `div r64` quotient_fits guard 的恒真 hint；不是 EVM DIV 语义。
        state.add_assumption(x86_div64_quotient_fits_assumption(a, b))
        return state

    elif kind == "SDIV":
        a, stack_after_pop1 = state.evm_stack.pop()
        b, stack_after_pop2 = stack_after_pop1.pop()
        result = op_semantics.sdiv_semantics(a, b)
        state.evm_stack = stack_after_pop2.push(result)
        # SDIV 内部对 |a|、|b| 跑 unsigned div；恒真提速 hint 须挂在绝对值上（见
        # common/arithmetic.sdiv_speedup_assumptions）。soundness 中性，纯提速。
        for assumption in _sdiv_speedup_assumptions(
            op_semantics._to_bv256(a), op_semantics._to_bv256(b)
        ):
            state.add_assumption(assumption)
        return state

    elif kind == "MOD":
        a, stack_after_pop1 = state.evm_stack.pop()
        b, stack_after_pop2 = stack_after_pop1.pop()
        result = op_semantics.mod_semantics(a, b)
        state.evm_stack = stack_after_pop2.push(result)
        # 同 DIV：注入恒真的相等借位链桥接 lemma 实例（soundness 中性、纯提速）。
        state.add_assumption(eq_borrow_chain_assumption(a, b))
        return state

    elif kind == "SMOD":
        a, stack_after_pop1 = state.evm_stack.pop()
        b, stack_after_pop2 = stack_after_pop1.pop()
        result = op_semantics.smod_semantics(a, b)
        state.evm_stack = stack_after_pop2.push(result)
        # 同 SDIV：恒真提速 hint 挂在 |a|、|b| 上（见 smod_speedup_assumptions）。
        for assumption in _smod_speedup_assumptions(
            op_semantics._to_bv256(a), op_semantics._to_bv256(b)
        ):
            state.add_assumption(assumption)
        return state

    elif kind == "EXP":
        base, stack_after_pop1 = state.evm_stack.pop()
        exponent, stack_after_pop2 = stack_after_pop1.pop()
        result = op_semantics.exp_semantics(base, exponent)
        state.evm_stack = stack_after_pop2.push(result)
        # gas 在 builtin dealWithExp 内、x86 不可见 → host UF（见 state/host_gas.py）。
        # aotGasExpEIP158 按 expByteLen 计费，故 UF 参数取 exponent。
        from state.host_gas import charge_host_gas_uf
        charge_host_gas_uf(state, "EXP", [exponent])
        return state

    elif kind == "LT":
        a, stack_after_pop1 = state.evm_stack.pop()
        b, stack_after_pop2 = stack_after_pop1.pop()
        result = op_semantics.lt_semantics(a, b)
        state.evm_stack = stack_after_pop2.push(result)
        return state

    elif kind == "GT":
        a, stack_after_pop1 = state.evm_stack.pop()
        b, stack_after_pop2 = stack_after_pop1.pop()
        result = op_semantics.gt_semantics(a, b)
        state.evm_stack = stack_after_pop2.push(result)
        return state

    elif kind == "SLT":
        a, stack_after_pop1 = state.evm_stack.pop()
        b, stack_after_pop2 = stack_after_pop1.pop()
        result = op_semantics.slt_semantics(a, b)
        state.evm_stack = stack_after_pop2.push(result)
        return state

    elif kind == "SGT":
        a, stack_after_pop1 = state.evm_stack.pop()
        b, stack_after_pop2 = stack_after_pop1.pop()
        result = op_semantics.sgt_semantics(a, b)
        state.evm_stack = stack_after_pop2.push(result)
        return state

    elif kind == "EQ":
        b, stack_after_pop1 = state.evm_stack.pop()
        a, stack_after_pop2 = stack_after_pop1.pop()
        result = op_semantics.eq_semantics(a, b)
        state.evm_stack = stack_after_pop2.push(result)
        return state

    elif kind == "ISZERO":
        a, stack_after_pop = state.evm_stack.pop()
        result = op_semantics.iszero_semantics(a)
        state.evm_stack = stack_after_pop.push(result)
        return state

    elif kind == "AND":
        b, stack_after_pop1 = state.evm_stack.pop()
        a, stack_after_pop2 = stack_after_pop1.pop()
        result = op_semantics.and_semantics(a, b)
        state.evm_stack = stack_after_pop2.push(result)
        return state

    elif kind == "OR":
        b, stack_after_pop1 = state.evm_stack.pop()
        a, stack_after_pop2 = stack_after_pop1.pop()
        result = op_semantics.or_semantics(a, b)
        state.evm_stack = stack_after_pop2.push(result)
        return state

    elif kind == "XOR":
        b, stack_after_pop1 = state.evm_stack.pop()
        a, stack_after_pop2 = stack_after_pop1.pop()
        result = op_semantics.xor_semantics(a, b)
        state.evm_stack = stack_after_pop2.push(result)
        return state

    elif kind == "NOT":
        a, stack_after_pop = state.evm_stack.pop()
        result = op_semantics.not_semantics(a)
        state.evm_stack = stack_after_pop.push(result)
        return state

    elif kind == "SIGNEXTEND":
        index, stack_after_pop1 = state.evm_stack.pop()
        value, stack_after_pop2 = stack_after_pop1.pop()
        result = op_semantics.signextend_semantics(index, value)
        state.evm_stack = stack_after_pop2.push(result)
        return state

    elif kind == "BYTE":
        index, stack_after_pop1 = state.evm_stack.pop()
        value, stack_after_pop2 = stack_after_pop1.pop()
        result = op_semantics.byte_semantics(index, value)
        state.evm_stack = stack_after_pop2.push(result)
        return state

    elif kind == "ADDMOD":
        a, stack_after_pop1 = state.evm_stack.pop()
        b, stack_after_pop2 = stack_after_pop1.pop()
        mod, stack_after_pop3 = stack_after_pop2.pop()
        result = op_semantics.addmod_semantics(a, b, mod)
        state.evm_stack = stack_after_pop3.push(result)
        # ADDMOD 不溢出路径内联跑 holiman Mod(sum_low, mod)，挂相等借位链桥接 hint
        # （恒真、soundness 中性），让 solver 对齐 x86 sub/sbb 借位链。见 DIV/MOD。
        for assumption in _addmod_speedup_assumptions(
            op_semantics._to_bv256(a),
            op_semantics._to_bv256(b),
            op_semantics._to_bv256(mod),
        ):
            state.add_assumption(assumption)
        return state

    elif kind == "MULMOD":
        a, stack_after_pop1 = state.evm_stack.pop()
        b, stack_after_pop2 = stack_after_pop1.pop()
        mod, stack_after_pop3 = stack_after_pop2.pop()
        result = op_semantics.mulmod_semantics(a, b, mod)
        state.evm_stack = stack_after_pop3.push(result)
        return state

    elif kind == "SHL":
        shift, stack_after_pop1 = state.evm_stack.pop()
        value, stack_after_pop2 = stack_after_pop1.pop()
        result = op_semantics.shl_semantics(value, shift)
        state.evm_stack = stack_after_pop2.push(result)
        return state

    elif kind == "SHR":
        shift, stack_after_pop1 = state.evm_stack.pop()
        value, stack_after_pop2 = stack_after_pop1.pop()
        result = op_semantics.shr_semantics(value, shift)
        state.evm_stack = stack_after_pop2.push(result)
        return state

    elif kind == "SAR":
        shift, stack_after_pop1 = state.evm_stack.pop()
        value, stack_after_pop2 = stack_after_pop1.pop()
        result = op_semantics.sar_semantics(value, shift)
        state.evm_stack = stack_after_pop2.push(result)
        return state

    elif kind == "POP":
        _, stack_after_pop = state.evm_stack.pop()
        state.evm_stack = stack_after_pop
        return state

    elif kind == "DUP":
        if op.param is None:
            raise ValueError(f"DUP operation missing param at pc={op.pc}")
        state.evm_stack = state.evm_stack.dup(op.param)
        return state

    elif kind == "SWAP":
        if op.param is None:
            raise ValueError(f"SWAP operation missing param at pc={op.pc}")
        state.evm_stack = state.evm_stack.swap(op.param)
        return state

    elif kind.startswith("PUSH"):
        # PUSH：将立即值推送到栈上
        if op.immediate is None:
            raise ValueError(f"PUSH operation missing immediate at pc={op.pc}")
        
        value = op_semantics.push_semantics(op.immediate, op.param or 1)
        new_stack_state = state.evm_stack.push(value)
        state.evm_stack = new_stack_state
        return state
    
    elif kind == "MLOAD":
        # MLOAD：从内存加载32字节，推送到栈上
        offset_bv, stack_after_pop = state.evm_stack.pop()
        # 内存扩展动态 gas（阶段 1）：MLOAD 引用 [offset, offset+32)，与 MSTORE
        # 同构（access_size=32）。镜像 x86 先算 gas 再访问内存。
        semantics_gas.charge_memory_gas_for_access(state, offset_bv, 32)
        mem_value, new_memory_state = state.evm_memory.load_256bit(offset_bv)
        state.evm_stack = stack_after_pop.push(mem_value)
        state.evm_memory = new_memory_state
        return state
    
    elif kind == "MSTORE":
        # MSTORE：弹出偏移量和值，将32字节存储到内存
        offset_bv, stack_after_pop1 = state.evm_stack.pop()
        value, stack_after_pop2 = stack_after_pop1.pop()
        # 内存扩展动态 gas（镜像 x86 makeStoreCheck：先算 gas 再 grow）。
        # requested = offset + 32；offset 高 192 位非零、offset+32 进位、cap 超限
        # 都会分叉出各自的错误终态，不再用 assumption 把它们排除在验证域外。
        semantics_gas.charge_memory_gas_for_access(state, offset_bv, 32)
        new_memory_state = state.evm_memory.store_256bit(offset_bv, value)
        state.evm_stack = stack_after_pop2
        state.evm_memory = new_memory_state
        return state

    elif kind == "MSTORE8":
        # MSTORE8：先弹出偏移量，再弹出值；仅写入低8位
        offset_bv, stack_after_pop1 = state.evm_stack.pop()
        value_bv, stack_after_pop2 = stack_after_pop1.pop()
        # 内存扩展动态 gas（阶段 1）：MSTORE8 引用 [offset, offset+1)，access_size=1。
        semantics_gas.charge_memory_gas_for_access(state, offset_bv, 1)
        byte_val = Extract(7, 0, value_bv)
        new_memory_state = state.evm_memory.set_byte(offset_bv, byte_val)
        state.evm_stack = stack_after_pop2
        state.evm_memory = new_memory_state
        return state

    elif kind == "SLOAD":
        # SLOAD: Pop key, push value from storage
        key, stack_after_pop = state.evm_stack.pop()
        val = state.evm_storage.sload(key)
        state.evm_stack = stack_after_pop.push(val)
        # host gas（冷热账户）不可见 → UF，依赖 slot key。
        from state.host_gas import charge_host_gas_uf
        charge_host_gas_uf(state, "SLOAD", [key])
        return state

    elif kind == "SSTORE":
        # SSTORE: Pop key and value, store in storage
        #
        # 没有写保护检查：AOT 的 SSTORE 退出到 Go host，写保护以 Go error 返回
        # （engine_evm.go:652 直接 return err，不回写 native status），
        # 状态码 6 在 AOT 运行时不是可观察量，codegen 也从不发射它。
        key, stack_after_pop1 = state.evm_stack.pop()
        val, stack_after_pop2 = stack_after_pop1.pop()
        # slot 写入前的值：gasSStoreEIP2929 的档位取决于 current 值，必须在 sstore
        # 之前取，写完再取只会拿回 val 本身。x86 侧 _handle_sstore 同序。
        old_val = state.evm_storage.sload(key)
        state.evm_storage = state.evm_storage.sstore(key, val)
        state.evm_stack = stack_after_pop2
        # host gas（冷热 + 退款）不可见 → UF，依赖 key、待写 value 与 slot 原值。
        from state.host_gas import charge_host_gas_uf
        charge_host_gas_uf(state, "SSTORE", [key, val, old_val])
        return state

    elif kind == "CALLDATASIZE":
        # Go: scope.Stack.push(uint256.SetUint64(uint64(len(input)))).
        if state.calldatasize.size() != 64:
            raise ValueError(f"calldatasize context must be 64 bits, got {state.calldatasize.size()}")
        state.evm_stack = state.evm_stack.push(ZeroExt(192, state.calldatasize))
        return state

    elif kind == "CALLDATALOAD":
        # CALLDATALOAD: Pop offset, push 32 bytes from calldata
        offset_bv, stack_after_pop = state.evm_stack.pop()
        # 全符号验证下的可选优化（默认开启）：把 "offset 高 192 bit ≠ 0 时
        # 返回 0" 这条 vacuous-同行为分支用 path-condition 假设掉。两侧语义
        # 在 overflow 时都返回 0，所以剪掉这个分支对 等价性仍成立；
        # 但留着的 If 守卫会让 z3 在 256-bit carry chain 上做大量无用 work。
        # See tests/support/calldataload_analysis/README.md 对此 200× 现象的分析。
        if getattr(state, 'assume_calldata_offset_no_overflow', True) and \
                offset_bv.size() == 256:
            state.add_assumption(calldataload_no_overflow_assumption(offset_bv))
            data_256 = calldataload_word(
                state.calldata,
                state.calldatasize,
                offset_bv,
                omit_overflow_guard=True,
                abstract=getattr(state, 'abstract_calldataload_words', False),
            )
        else:
            data_256 = calldataload_word(
                state.calldata,
                state.calldatasize,
                offset_bv,
                abstract=getattr(state, 'abstract_calldataload_words', False),
            )
        state.evm_stack = stack_after_pop.push(data_256)
        return state

    elif kind == "CALLDATACOPY":
        # 对齐 go-hpc-evm/opCallDataCopy:
        # memOffset = pop(), dataOffset = pop(), length = pop()
        mem_offset_bv, stack_after_pop1 = state.evm_stack.pop()
        data_offset_bv, stack_after_pop2 = stack_after_pop1.pop()
        length_bv, stack_after_pop3 = stack_after_pop2.pop()

        # 动态 gas（阶段 1d）：内存扩展(memOffset+length) + copy word gas(每 word 3)。
        # 镜像 x86 checkMemoryAndCalcDynamicGasCallDataCopy → compileMemoryCopierGasN。
        semantics_gas.charge_memory_and_word_gas(state, mem_offset_bv, length_bv, 3)

        # Go 解释器对 dataOffset 使用 Uint64WithOverflow，溢出时钳到 MaxUint64
        calldata_offset_64 = to_u64_with_overflow_max(data_offset_bv)
        if state.calldatasize.size() != 64:
            raise ValueError(f"calldatasize context must be 64 bits, got {state.calldatasize.size()}")
        calldatasize_64 = state.calldatasize

        state.evm_memory = _write_symbolic_memory_slice(
            state.evm_memory,
            mem_offset_bv,
            length_bv,
            lambda relative_index: _go_getdata_byte(
                state.calldata,
                calldata_offset_64,
                calldatasize_64,
                relative_index,
            ),
            effect_tag=f"calldatacopy_idx_{op.pc}",
        )
        state.evm_stack = stack_after_pop3
        return state

    elif kind == "CODESIZE":
        state.evm_stack = state.evm_stack.push(ZeroExt(192, state.callengine_code_size_bytes))
        return state

    elif kind == "CODECOPY":
        # CODECOPY: memOffset = pop(), codeOffset = pop(), length = pop()
        mem_offset_bv, stack_after_pop1 = state.evm_stack.pop()
        code_offset_bv, stack_after_pop2 = stack_after_pop1.pop()
        length_bv, stack_after_pop3 = stack_after_pop2.pop()

        # 动态 gas（阶段 1d）：内存扩展(memOffset+length) + copy word gas(3)。
        semantics_gas.charge_memory_and_word_gas(state, mem_offset_bv, length_bv, 3)

        code_offset_64 = to_u64_with_overflow_max(code_offset_bv)
        if state.callengine_code_size_bytes.size() != 64:
            raise ValueError(
                f"code size context must be 64 bits, got {state.callengine_code_size_bytes.size()}"
            )
        code_size_64 = state.callengine_code_size_bytes

        def code_byte(relative_index):
            return _go_getdata_byte(state.code, code_offset_64, code_size_64, relative_index)

        state.evm_memory = _write_symbolic_memory_slice(
            state.evm_memory,
            mem_offset_bv,
            length_bv,
            code_byte,
            effect_tag=f"codecopy_idx_{op.pc}",
        )
        state.evm_stack = stack_after_pop3
        return state

    elif kind == "RETURNDATASIZE":
        state.evm_stack = state.evm_stack.push(ZeroExt(192, state.callengine_return_data_size_bytes))
        return state

    elif kind == "RETURNDATACOPY":
        # RETURNDATACOPY: memOffset = pop(), returnDataOffset = pop(), length = pop()
        mem_offset_bv, stack_after_pop1 = state.evm_stack.pop()
        data_offset_bv, stack_after_pop2 = stack_after_pop1.pop()
        length_bv, stack_after_pop3 = stack_after_pop2.pop()

        # 两组错误分支的快照点不同，取决于它们在 codegen 里相对三次 popUint256
        # （impl_amd64.go:3128-3130）的位置：
        #   - gas 前言的 exit（checkMemoryAndCalcDynamicGasReturnDataCopy，:3124）在 pop
        #     **之前** → 快照里参数仍在栈上，所以这里先扣 gas、后写回弹栈结果。
        #   - errPoint 的 ReturnDataOutOfBounds（:3143+）在 pop **之后** → 快照是弹栈后的。
        # 两者共用一个快照会让其中一组的栈深与 x86 的 exit 错位（终态 stack 目前不是
        # 证明 observable，但加入后就会暴露）。
        semantics_gas.charge_memory_and_word_gas(state, mem_offset_bv, length_bv, 3)
        state.evm_stack = stack_after_pop3

        # 越界终态的 gas 已经扣过：gas 前言先于 errPoint 执行。

        # 镜像 compileEVMRETURNDATACOPY（impl_amd64.go:3143-3178）的三条错误分支，
        # 它们都跳到同一个 errPoint 发射 exit(ReturnDataOutOfBounds)：
        #   1. compileLocIsUint64(d1..d4) 失败 —— dataOffset 高 192 位非零
        #   2. ADDQ + ADCQ 0 + TESTQ/JNE   —— dataOffset.z0 + length.z0 的 64 位进位
        #   3. CMPQ reg2, tmpReg + JCS     —— returnDataSize < end（无符号）
        # codegen 只取 length 低 64 位（compileLoadValueToRegister(l1, reg1)），
        # 不检查 length 是否 uint64——不要补 IsUint64(length)。
        # blast_select_store 折叠栈上的 Store/Select 链，具体输入才能化简成字面
        # True/False，否则"必然越界"识别不出来，会白留一条不可满足的正常路径。
        d_low = simplify(Extract(63, 0, data_offset_bv), blast_select_store=True)
        l_low = simplify(Extract(63, 0, length_bv), blast_select_store=True)
        d_hi = simplify(Extract(255, 64, data_offset_bv), blast_select_store=True)
        end = d_low + l_low
        d_hi_nonzero = d_hi != BitVecVal(0, 192)
        carry = ULT(end, d_low)   # 64-bit 无符号回绕即进位
        size_too_small = ULT(state.callengine_return_data_size_bytes, end)
        oob_cond = simplify(Or(d_hi_nonzero, carry, size_too_small))

        if not is_false(oob_cond):
            # 快照：已弹栈、未写内存，对齐 x86 的 exit-before-copy 时刻。
            state.pending_errors.append(
                PendingErrorBranch(
                    condition=oob_cond,
                    status_code=EvmStatusCode.RETURN_DATA_OUT_OF_BOUNDS,
                    terminal_state=state.snapshot_for_error_branch(),
                )
            )
        if is_true(oob_cond):
            return state   # 必然越界，没有正常路径

        data_offset_64 = to_u64_with_overflow_max(data_offset_bv)

        def return_data_byte(relative_index):
            return Select(state.return_data, data_offset_64 + relative_index)

        state.evm_memory = _write_symbolic_memory_slice(
            state.evm_memory,
            mem_offset_bv,
            length_bv,
            return_data_byte,
            effect_tag=f"returndatacopy_idx_{op.pc}",
        )
        return state

    elif kind == "CALLVALUE":
        # CALLVALUE: Push callvalue onto stack
        state.evm_stack = state.evm_stack.push(state.callvalue)
        return state

    elif kind == "SHA3":
        offset_bv, stack_after_pop1 = state.evm_stack.pop()
        length_bv, stack_after_pop2 = stack_after_pop1.pop()
        # 动态 gas（阶段 1d）：内存扩展(offset+length) + SHA3 word gas(每 word 6)。
        # 镜像 x86 checkMemoryAndCalcDynamicGasSha3 → memorySha3GasN，在 host hash 前。
        semantics_gas.charge_memory_and_word_gas(state, offset_bv, length_bv, 6)
        hash_val = uninterpreted.sha3_semantics(
            state.evm_memory.Memory,
            BitVecVal(0, 64),
            offset_bv,
            length_bv,
        )
        state.evm_stack = stack_after_pop2.push(hash_val)
        return state

    elif kind == "MCOPY":
        # MCOPY: memOffset = pop(), srcOffset = pop(), length = pop()
        dst_offset_bv, stack_after_pop1 = state.evm_stack.pop()
        src_offset_bv, stack_after_pop2 = stack_after_pop1.pop()
        length_bv, stack_after_pop3 = stack_after_pop2.pop()

        # 动态 gas（阶段 1d）：MCOPY 内存扩展用 max(dst,src)+length（Go MCOPY 取
        # source/dest 较大者），copy word gas 用 length(CopyGas=3)。
        semantics_gas.charge_mcopy_gas(state, dst_offset_bv, src_offset_bv, length_bv)

        src_offset_64 = truncate_to_64(src_offset_bv)
        old_memory = state.evm_memory.Memory

        # charge_mcopy_gas 已更新取整后的 MSize，并在 length == 0 时保持不变；
        # 这里仅写入 Memory。
        state.evm_memory = _write_symbolic_memory_slice(
            state.evm_memory,
            dst_offset_bv,
            length_bv,
            lambda relative_index: Select(old_memory, src_offset_64 + relative_index),
            effect_tag=f"mcopy_idx_{op.pc}",
        )
        state.evm_stack = stack_after_pop3
        return state

    elif kind == "GASPRICE":
        state.evm_stack = state.evm_stack.push(BitVecVal(0, 256))
        return state

    elif kind == "COINBASE":
        state.evm_stack = state.evm_stack.push(BitVecVal(0, 256))
        return state

    elif kind == "TIMESTAMP":
        state.evm_stack = state.evm_stack.push(ZeroExt(192, state.block_timestamp))
        return state

    elif kind == "NUMBER":
        state.evm_stack = state.evm_stack.push(ZeroExt(192, state.block_number))
        return state

    elif kind == "DIFFICULTY":
        state.evm_stack = state.evm_stack.push(BitVecVal(0, 256))
        return state

    elif kind == "GASLIMIT":
        state.evm_stack = state.evm_stack.push(ZeroExt(192, state.gaslimit))
        return state

    elif kind == "CHAINID":
        state.evm_stack = state.evm_stack.push(BitVecVal(0, 256))
        return state

    elif kind == "BASEFEE":
        state.evm_stack = state.evm_stack.push(state.basefee)
        return state

    elif kind == "BLOBBASEFEE":
        state.evm_stack = state.evm_stack.push(ZeroExt(192, state.blobbasefee))
        return state

    elif kind == "GAS":
        # GAS: Push current gas counter onto stack.
        # 镜像 go-hpc-evm compileEVMGAS:x86 在 block 入口一次性扣完整
        # Blk.StaticGas，GAS 指令再把「本指令之后的静态 gas」加回，压栈
        # G + (Blk.StaticGas - Immediate)。EVM 侧 block 入口同样扣完整
        # static_gas，故此处必须做同样返还，否则压栈值会少 static_gas - imm。
        gas64 = state.evm_gas.Gas
        if op.block is not None and op.immediate is not None:
            after_gas = op.block.static_gas - op.immediate
            gas64 = gas64 + BitVecVal(after_gas, 64)
        # else: 裸 GAS op（无 block/immediate，仅 instruction-level 单测构造）
        #       退回只读 evm_gas.Gas，避免阶段 0 一改炸一片无关单测。
        # Gas is 64-bit, zero-extend to 256-bit for stack
        gas_256 = ZeroExt(192, gas64)
        state.evm_stack = state.evm_stack.push(gas_256)
        return state

    elif kind == "PC":
        state.evm_stack = state.evm_stack.push(BitVecVal(op.pc, 256))
        return state

    elif kind == "MSIZE":
        state.evm_stack = state.evm_stack.push(ZeroExt(192, state.evm_memory.MSize))
        return state

    elif kind == "ADDRESS":
        state.evm_stack = state.evm_stack.push(state.self_address)
        return state

    elif kind == "ORIGIN":
        state.evm_stack = state.evm_stack.push(state.origin_address)
        return state

    elif kind == "CALLER":
        state.evm_stack = state.evm_stack.push(state.caller_address)
        return state

    elif kind == "BALANCE":
        addr_bv, stack1 = state.evm_stack.pop()
        result = uninterpreted.balance_semantics(addr_bv)
        state.evm_stack = stack1.push(result)
        # host gas（冷热账户访问）不可见 → UF，依赖 addr。
        from state.host_gas import charge_host_gas_uf
        charge_host_gas_uf(state, "BALANCE", [addr_bv])
        return state

    elif kind == "SELFBALANCE":
        result = uninterpreted.self_balance_semantics()
        state.evm_stack = state.evm_stack.push(result)
        return state

    elif kind == "EXTCODESIZE":
        addr_bv, stack1 = state.evm_stack.pop()
        result = uninterpreted.ext_code_size_semantics(addr_bv)
        state.evm_stack = stack1.push(result)
        # host gas（冷热账户）不可见 → UF，依赖 addr。
        from state.host_gas import charge_host_gas_uf
        charge_host_gas_uf(state, "EXTCODESIZE", [addr_bv])
        return state

    elif kind == "EXTCODECOPY":
        addr_bv, stack1 = state.evm_stack.pop()
        dest_offset_bv, stack2 = stack1.pop()
        offset_bv, stack3 = stack2.pop()
        size_bv, stack4 = stack3.pop()
        # 可见 fee = memoryCopierGas(3)：memoryExtCodeCopy=calcMemSize64(Back(1),Back(3))
        # = (destOffset, size) + CopyGas word gas。与其它 copy 同形，只是槽位不同。
        # 必须在写内存之前：x86 checkMemoryAndCalcDynamicGasExtCodeCopy 是
        # compileEVMEXTCODECOPY 的第一条语句（impl_amd64.go:3105），错误 exit 早于 copy。
        semantics_gas.charge_memory_and_word_gas(state, dest_offset_bv, size_bv, 3)
        state.evm_memory = _write_symbolic_memory_slice(
            state.evm_memory,
            dest_offset_bv,
            size_bv,
            lambda byte_index: uninterpreted.ext_code_copy_byte(
                addr_bv, offset_bv, byte_index, effect_id=op.pc,
            ),
            effect_tag=f"extcodecopy_idx_{op.pc}",
        )
        state.evm_stack = stack4
        # host gas（冷热账户）不可见 → UF，依赖 addr 与 size。可见的内存扩展 + copy
        # word gas 见上面的 charge_memory_and_word_gas。两部分都已接好，EXTCODECOPY
        # 在 gas 检查范围内（fixture: gas_extcodecopy / gas_extcodecopy_sym）。
        from state.host_gas import charge_host_gas_uf
        charge_host_gas_uf(state, "EXTCODECOPY", [addr_bv, size_bv])
        return state

    elif kind == "EXTCODEHASH":
        addr_bv, stack1 = state.evm_stack.pop()
        result = uninterpreted.ext_code_hash_semantics(addr_bv)
        state.evm_stack = stack1.push(result)
        # host gas（冷热账户）不可见 → UF，依赖 addr。
        from state.host_gas import charge_host_gas_uf
        charge_host_gas_uf(state, "EXTCODEHASH", [addr_bv])
        return state

    elif kind == "BLOCKHASH":
        block_number_bv, stack1 = state.evm_stack.pop()
        result = uninterpreted.block_hash_semantics(block_number_bv)
        state.evm_stack = stack1.push(result)
        return state

    elif kind == "BLOBHASH":
        index_bv, stack1 = state.evm_stack.pop()
        blobhash_count = getattr(state, "blobhash_count", BitVecVal(0, 64))
        result = If(
            ULT(index_bv, ZeroExt(192, blobhash_count)),
            uninterpreted.blob_hash_semantics(index_bv),
            BitVecVal(0, 256),
        )
        state.evm_stack = stack1.push(result)
        return state

    elif kind == "SELFDESTRUCT":
        beneficiary_bv, stack1 = state.evm_stack.pop()
        state.evm_stack = stack1
        # 终止指令：x86 codegen 在 host 调用后发
        # compileExitFromNativeCode(evmNativeCallStatusCodeStopped)。
        set_terminal_status(state, EvmStatusCode.STOPPED)
        # host gas（冷热 + 账户创建）不可见 → UF，依赖受益人地址。
        from state.host_gas import charge_host_gas_uf
        charge_host_gas_uf(state, "SELFDESTRUCT", [beneficiary_bv])
        return state

    elif kind == "CREATE":
        value_bv, stack1 = state.evm_stack.pop()
        offset_bv, stack2 = stack1.pop()
        size_bv, stack3 = stack2.pop()
        # 严格按 compileEVMCREATE（impl_amd64.go:3940-3962）的四段：
        #   dealWithAddGas(rg) → checkMemoryAndCalcDynamicGasCreate → host → dealWithSubGas(rg)
        # 可见 fee 的检查落在 add/sub 窗口**之内**——顺序错了 gas 终值虽相同（加减相消），
        # 但可见 fee 的 OOG 阈值会少算一个 rg：应判 `fee > gas+rg`，错序则判 `fee > gas`。
        # 可见 fee = memoryCreate=calcMemSize64(Back(1),Back(2)) + toWordSize(Back(2))*
        # InitCodeWordGas（x86 memoryCreateGasN，gas_dynamic:429）。
        from state.host_gas import (
            add_return_gas, charge_host_gas_uf, sub_return_gas,
        )
        return_gas = semantics_gas.return_gas_for(op)
        add_return_gas(state, return_gas)
        semantics_gas.charge_memory_and_word_gas(state, offset_bv, size_bv, INIT_CODE_WORD_GAS)
        result = uninterpreted.create_semantics(
            value_bv, offset_bv, size_bv, state.evm_memory.Memory, effect_id=op.pc
        )
        state.evm_stack = stack3.push(result)
        # host gas 仍是 UF；可见 fee 已对齐，CREATE 在 gas 检查范围内
        # （fixture: gas_create / gas_create_returngas / gas_create_sym）。
        #
        # MAX_INIT_CODE_SIZE_EXCEEDED(16) 不需要建模：amd64 codegen **根本不产生**这个
        # 状态码——`evmNativeCallStatusMaxInitCodeSizeExceeded` 在 evm/aot 全包只出现于
        # engine_evm.go:260（枚举）与 :280（error 映射），memoryGasCreate 里那句
        # `// check if codeSize > params.MaxInitCodeSize`（gas_dynamic_amd64.go:444）
        # 下面没有任何比较指令。它与 host gas 耗尽同类：Go host 内 error 终止、不回写
        # native status，没有 x86 行为可以不一致（论证见 state/host_gas.py 模块 docstring）。
        charge_host_gas_uf(state, "CREATE", [value_bv, offset_bv, size_bv])
        # CREATE 同样刷新 returndata（成功→空，revert→reason）。不刷新会保留
        # 调用前的旧数据，那是不可能的真实状态。
        _update_call_return_data_source(
            state,
            uninterpreted.create_return_size(
                value_bv, offset_bv, size_bv,
                state.evm_memory.Memory, effect_id=op.pc,
            ),
            lambda byte_index: uninterpreted.create_return_byte(
                value_bv, offset_bv, size_bv,
                state.evm_memory.Memory, byte_index, effect_id=op.pc,
            ),
            effect_tag=f"create_{op.pc}",
        )
        sub_return_gas(state, return_gas)
        return state

    elif kind == "CREATE2":
        value_bv, stack1 = state.evm_stack.pop()
        offset_bv, stack2 = stack1.pop()
        size_bv, stack3 = stack2.pop()
        salt_bv, stack4 = stack3.pop()
        # 同 CREATE 的四段顺序（compileEVMCREATE2，impl_amd64.go:4046-4071），只是 word
        # 常量是 InitCodeWordGas + Sha3WordGas——memoryCreate2GasN 多算一次 keccak 的
        # word gas（gas_dynamic:433）。
        from state.host_gas import (
            add_return_gas, charge_host_gas_uf, sub_return_gas,
        )
        return_gas = semantics_gas.return_gas_for(op)
        add_return_gas(state, return_gas)
        semantics_gas.charge_memory_and_word_gas(state, offset_bv, size_bv, CREATE2_WORD_GAS)
        result = uninterpreted.create2_semantics(
            value_bv, offset_bv, size_bv, salt_bv, state.evm_memory.Memory, effect_id=op.pc
        )
        state.evm_stack = stack4.push(result)
        # 可见 fee + host UF 的分工同 CREATE（含 MAX_INIT_CODE_SIZE 的核对结论）。
        # fixture: gas_create2。
        charge_host_gas_uf(state, "CREATE2", [value_bv, offset_bv, size_bv, salt_bv])
        _update_call_return_data_source(
            state,
            uninterpreted.create2_return_size(
                value_bv, offset_bv, size_bv, salt_bv,
                state.evm_memory.Memory, effect_id=op.pc,
            ),
            lambda byte_index: uninterpreted.create2_return_byte(
                value_bv, offset_bv, size_bv, salt_bv,
                state.evm_memory.Memory, byte_index, effect_id=op.pc,
            ),
            effect_tag=f"create2_{op.pc}",
        )
        sub_return_gas(state, return_gas)
        return state

    elif kind == "CALL":
        gas_bv, stack1 = state.evm_stack.pop()
        addr_bv, stack2 = stack1.pop()
        value_bv, stack3 = stack2.pop()
        args_offset_bv, stack4 = stack3.pop()
        args_size_bv, stack5 = stack4.pop()
        ret_offset_bv, stack6 = stack5.pop()
        ret_size_bv, stack7 = stack6.pop()
        result = uninterpreted.call_semantics(
            gas_bv, addr_bv, value_bv,
            args_offset_bv, args_size_bv, ret_offset_bv, ret_size_bv,
            state.evm_memory.Memory, effect_id=op.pc)
        old_memory = state.evm_memory
        should_copy = uninterpreted.call_should_copy_return_data(
            gas_bv, addr_bv, value_bv,
            args_offset_bv, args_size_bv, ret_offset_bv, ret_size_bv,
            old_memory.Memory, effect_id=op.pc,
        )
        state.evm_memory = _write_call_return_data(
            old_memory,
            ret_offset_bv,
            ret_size_bv,
            lambda byte_index: uninterpreted.call_return_byte(
                gas_bv, addr_bv, value_bv,
                args_offset_bv, args_size_bv, ret_offset_bv, ret_size_bv,
                old_memory.Memory, byte_index, effect_id=op.pc,
            ),
            effect_id=op.pc,
            should_copy=should_copy,
        )
        # RETURNDATA 源与 memory 拷贝是两件事，两者都要做（见函数 docstring）。
        _update_call_return_data_source(
            state,
            uninterpreted.call_return_size(
                gas_bv, addr_bv, value_bv,
                args_offset_bv, args_size_bv, ret_offset_bv, ret_size_bv,
                old_memory.Memory, effect_id=op.pc,
            ),
            lambda byte_index: uninterpreted.call_return_byte(
                gas_bv, addr_bv, value_bv,
                args_offset_bv, args_size_bv, ret_offset_bv, ret_size_bv,
                old_memory.Memory, byte_index, effect_id=op.pc,
            ),
            effect_tag=f"call_{op.pc}",
        )
        state.evm_stack = stack7.push(result)
        # host UF（依赖 7 个栈参数）+ 镜像 x86 host 调用前后的 dealWithAddGas/SubGas
        # returnGas 链，否则两侧 gas 实参不同、UF 不相消（returnGas≠0 时假 SAT）。
        from state.host_gas import charge_host_gas_uf_with_return_gas
        _rg = semantics_gas.return_gas_for(op)
        charge_host_gas_uf_with_return_gas(state, "CALL", [
            gas_bv, addr_bv, value_bv, args_offset_bv, args_size_bv,
            ret_offset_bv, ret_size_bv,
        ], _rg)
        return state

    elif kind == "CALLCODE":
        gas_bv, stack1 = state.evm_stack.pop()
        addr_bv, stack2 = stack1.pop()
        value_bv, stack3 = stack2.pop()
        args_offset_bv, stack4 = stack3.pop()
        args_size_bv, stack5 = stack4.pop()
        ret_offset_bv, stack6 = stack5.pop()
        ret_size_bv, stack7 = stack6.pop()
        result = uninterpreted.callcode_semantics(
            gas_bv, addr_bv, value_bv,
            args_offset_bv, args_size_bv, ret_offset_bv, ret_size_bv,
            state.evm_memory.Memory, effect_id=op.pc)
        old_memory = state.evm_memory
        should_copy = uninterpreted.callcode_should_copy_return_data(
            gas_bv, addr_bv, value_bv,
            args_offset_bv, args_size_bv, ret_offset_bv, ret_size_bv,
            old_memory.Memory, effect_id=op.pc,
        )
        state.evm_memory = _write_call_return_data(
            old_memory,
            ret_offset_bv,
            ret_size_bv,
            lambda byte_index: uninterpreted.callcode_return_byte(
                gas_bv, addr_bv, value_bv,
                args_offset_bv, args_size_bv, ret_offset_bv, ret_size_bv,
                old_memory.Memory, byte_index, effect_id=op.pc,
            ),
            effect_id=op.pc,
            should_copy=should_copy,
        )
        _update_call_return_data_source(
            state,
            uninterpreted.callcode_return_size(
                gas_bv, addr_bv, value_bv,
                args_offset_bv, args_size_bv, ret_offset_bv, ret_size_bv,
                old_memory.Memory, effect_id=op.pc,
            ),
            lambda byte_index: uninterpreted.callcode_return_byte(
                gas_bv, addr_bv, value_bv,
                args_offset_bv, args_size_bv, ret_offset_bv, ret_size_bv,
                old_memory.Memory, byte_index, effect_id=op.pc,
            ),
            effect_tag=f"callcode_{op.pc}",
        )
        state.evm_stack = stack7.push(result)
        # 同 CALL：host UF（7 个栈参数）+ returnGas 链镜像。
        from state.host_gas import charge_host_gas_uf_with_return_gas
        charge_host_gas_uf_with_return_gas(state, "CALLCODE", [
            gas_bv, addr_bv, value_bv, args_offset_bv, args_size_bv,
            ret_offset_bv, ret_size_bv,
        ], semantics_gas.return_gas_for(op))
        return state

    elif kind == "DELEGATECALL":
        gas_bv, stack1 = state.evm_stack.pop()
        addr_bv, stack2 = stack1.pop()
        args_offset_bv, stack3 = stack2.pop()
        args_size_bv, stack4 = stack3.pop()
        ret_offset_bv, stack5 = stack4.pop()
        ret_size_bv, stack6 = stack5.pop()
        result = uninterpreted.delegate_call_semantics(
            gas_bv, addr_bv,
            args_offset_bv, args_size_bv, ret_offset_bv, ret_size_bv,
            state.evm_memory.Memory, effect_id=op.pc)
        old_memory = state.evm_memory
        should_copy = uninterpreted.delegate_call_should_copy_return_data(
            gas_bv, addr_bv,
            args_offset_bv, args_size_bv, ret_offset_bv, ret_size_bv,
            old_memory.Memory, effect_id=op.pc,
        )
        state.evm_memory = _write_call_return_data(
            old_memory,
            ret_offset_bv,
            ret_size_bv,
            lambda byte_index: uninterpreted.delegate_call_return_byte(
                gas_bv, addr_bv,
                args_offset_bv, args_size_bv, ret_offset_bv, ret_size_bv,
                old_memory.Memory, byte_index, effect_id=op.pc,
            ),
            effect_id=op.pc,
            should_copy=should_copy,
        )
        _update_call_return_data_source(
            state,
            uninterpreted.delegate_call_return_size(
                gas_bv, addr_bv,
                args_offset_bv, args_size_bv, ret_offset_bv, ret_size_bv,
                old_memory.Memory, effect_id=op.pc,
            ),
            lambda byte_index: uninterpreted.delegate_call_return_byte(
                gas_bv, addr_bv,
                args_offset_bv, args_size_bv, ret_offset_bv, ret_size_bv,
                old_memory.Memory, byte_index, effect_id=op.pc,
            ),
            effect_tag=f"delegatecall_{op.pc}",
        )
        state.evm_stack = stack6.push(result)
        # 同 CALL：host UF + returnGas 链镜像，6 个栈参数（无 value）。
        from state.host_gas import charge_host_gas_uf_with_return_gas
        charge_host_gas_uf_with_return_gas(state, "DELEGATECALL", [
            gas_bv, addr_bv, args_offset_bv, args_size_bv,
            ret_offset_bv, ret_size_bv,
        ], semantics_gas.return_gas_for(op))
        return state

    elif kind == "STATICCALL":
        gas_bv, stack1 = state.evm_stack.pop()
        addr_bv, stack2 = stack1.pop()
        args_offset_bv, stack3 = stack2.pop()
        args_size_bv, stack4 = stack3.pop()
        ret_offset_bv, stack5 = stack4.pop()
        ret_size_bv, stack6 = stack5.pop()
        result = uninterpreted.static_call_semantics(
            gas_bv, addr_bv,
            args_offset_bv, args_size_bv, ret_offset_bv, ret_size_bv,
            state.evm_memory.Memory, effect_id=op.pc)
        old_memory = state.evm_memory
        state.evm_memory = _write_call_return_data(
            old_memory,
            ret_offset_bv,
            ret_size_bv,
            lambda byte_index: uninterpreted.static_call_return_byte(
                gas_bv, addr_bv,
                args_offset_bv, args_size_bv, ret_offset_bv, ret_size_bv,
                old_memory.Memory, byte_index, effect_id=op.pc,
            ),
            effect_id=op.pc,
        )
        _update_call_return_data_source(
            state,
            uninterpreted.static_call_return_size(
                gas_bv, addr_bv,
                args_offset_bv, args_size_bv, ret_offset_bv, ret_size_bv,
                old_memory.Memory, effect_id=op.pc,
            ),
            lambda byte_index: uninterpreted.static_call_return_byte(
                gas_bv, addr_bv,
                args_offset_bv, args_size_bv, ret_offset_bv, ret_size_bv,
                old_memory.Memory, byte_index, effect_id=op.pc,
            ),
            effect_tag=f"staticcall_{op.pc}",
        )
        state.evm_stack = stack6.push(result)
        # 同 CALL：host UF + returnGas 链镜像，6 个栈参数（无 value）。
        from state.host_gas import charge_host_gas_uf_with_return_gas
        charge_host_gas_uf_with_return_gas(state, "STATICCALL", [
            gas_bv, addr_bv, args_offset_bv, args_size_bv,
            ret_offset_bv, ret_size_bv,
        ], semantics_gas.return_gas_for(op))
        return state

    elif kind == "TLOAD":
        key_bv, stack1 = state.evm_stack.pop()
        result = state.evm_transient_storage.tload(key_bv)
        state.evm_stack = stack1.push(result)
        return state

    elif kind == "TSTORE":
        key_bv, stack1 = state.evm_stack.pop()
        val_bv, stack2 = stack1.pop()
        state.evm_transient_storage = state.evm_transient_storage.tstore(key_bv, val_bv)
        state.evm_stack = stack2
        return state

    elif kind == "RETURN":
        # RETURN：弹出偏移量和长度，返回memory[offset:offset+length]
        # 从栈中弹出偏移量和长度
        offset_bv, stack_after_pop1 = state.evm_stack.pop()
        length_bv, stack_after_pop2 = stack_after_pop1.pop()
        
        # 将长度截断为64位以便存储
        from z3 import Extract as Z3Extract
        if length_bv.size() == 256:
            return_length_64 = Z3Extract(63, 0, length_bv)
        elif length_bv.size() == 64:
            return_length_64 = length_bv
        else:
            raise ValueError(f"Unexpected length size: {length_bv.size()}")
        
        if offset_bv.size() == 256:
            return_offset_64 = Z3Extract(63, 0, offset_bv)
        elif offset_bv.size() == 64:
            return_offset_64 = offset_bv
        else:
            raise ValueError(f"Unexpected offset size: {offset_bv.size()}")
        
        # 内存扩展动态 gas（阶段 1，镜像 x86 checkMemoryAndCalcDynamicGasReturn）。
        # RETURN 引用 memory[offset:offset+length]：requested = offset + length，
        # 且 length == 0 时 requested = 0（不扩容、不计 gas）。在 scope assumption
        # 下：offset/length 高 192 位为 0，offset + length 不溢出 uint64。
        semantics_gas.charge_memory_gas_for_return(state, offset_bv, length_bv)

        # 在状态中存储返回偏移量和长度
        # 我们不提取数据 - 我们将在EquivalenceChecker中直接比较内存
        # 注意：RETURN只读取内存，不修改内存或MSize
        state.return_offset = return_offset_64
        state.return_length = return_length_64

        # 更新栈（两个值都已弹出）
        state.evm_stack = stack_after_pop2

        set_terminal_status(state, EvmStatusCode.RETURNED)
        return state

    elif kind == "JUMPI":
        # JUMPI: 静态形态（PUSH 折叠）目标在 immediate，只 pop condition；
        # 否则 pop condition 与 dest。栈行为对齐 symbolic_jump_resolver.go 的 JUMPI 分支。
        if op.is_static and op.immediate is not None:
            cond_bv, state.evm_stack = state.evm_stack.pop()
            dest_bv = BitVecVal(op.immediate, 256)
        else:
            cond_bv, stack_after_pop1 = state.evm_stack.pop()
            dest_bv, state.evm_stack = stack_after_pop1.pop()

        # 目标校验只在 cond != 0（真正发生跳转）的路径上生效。
        taken = cond_bv != BitVecVal(0, cond_bv.size())
        _apply_jump_destination_check(op, state, dest_bv, taken_cond=taken)
        return state

    elif kind == "JUMP":
        # JUMP: 静态形态目标已折叠进 immediate，不 pop；否则 pop dest。
        if op.is_static and op.immediate is not None:
            dest_bv = BitVecVal(op.immediate, 256)
        else:
            dest_bv, state.evm_stack = state.evm_stack.pop()

        _apply_jump_destination_check(op, state, dest_bv)
        return state

    elif kind == "REVERT":
        # REVERT: offset, length = pop, pop
        offset_bv, stack_after_pop1 = state.evm_stack.pop()
        length_bv, stack_after_pop2 = stack_after_pop1.pop()

        # 动态 gas（阶段 1d）：REVERT 引用 memory[offset:offset+length]，与 RETURN
        # 同构（仅内存扩展，无 word gas）。
        semantics_gas.charge_memory_gas_for_return(state, offset_bv, length_bv)

        # 与 RETURN 一样，只在状态中记录偏移量和长度；
        # 具体数据内容由后续比较阶段直接从内存读取。
        if length_bv.size() == 256:
            return_length_64 = Extract(63, 0, length_bv)
        elif length_bv.size() == 64:
            return_length_64 = length_bv
        else:
            raise ValueError(f"Unexpected length BitVec size: {length_bv.size()}")

        if offset_bv.size() == 256:
            return_offset_64 = Extract(63, 0, offset_bv)
        elif offset_bv.size() == 64:
            return_offset_64 = offset_bv
        else:
            raise ValueError(f"Unexpected offset BitVec size: {offset_bv.size()}")

        state.return_offset = return_offset_64
        state.return_length = return_length_64
        state.evm_stack = stack_after_pop2
        set_terminal_status(state, EvmStatusCode.REVERTED)
        return state

    elif kind == "STOP":
        # STOP: 对状态无堆栈影响
        set_terminal_status(state, EvmStatusCode.STOPPED)
        return state

    elif kind == "LOG":
        # LOG指令：从栈中弹出参数并记录事件
        # immediate 字段表示主题数量 (0-4)
        # LOG[n] 弹出 (2+n) 个值: offset, size, topic1...topicn
        # TODO: 占位实现：只弹出值，不实际记录事件日志（gas 已建模）

        # 获取主题数量
        num_topics = op.immediate if op.immediate is not None else 0

        # 读 Back(0)=offset、Back(1)=size，但**先不写回 state.evm_stack**：
        # checkMemoryAndCalcDynamicGasLog 是 compileEVMLog 的第一条语句
        # （impl_amd64.go:3908）、早于所有 locationStack.popUint256()，故它的错误 exit
        # 带的是**未弹栈**的 SP。同 MSTORE/RETURN 的既有范式。
        offset_bv, stack_after_pop1 = state.evm_stack.pop()
        size_bv, stack_after_pop2 = stack_after_pop1.pop()

        semantics_gas.charge_log_gas(state, offset_bv, size_bv, num_topics)

        # gas 扣完再提交弹栈：offset、size 与 num_topics 个 topic。
        state.evm_stack = stack_after_pop2
        for _ in range(num_topics):
            _, state.evm_stack = state.evm_stack.pop()

        return state

    elif kind == "INVALID":
        # INVALID: Marks the transaction as invalid / stops execution
        # INVALID is a terminal operation like STOP。
        set_terminal_status(state, EvmStatusCode.INVALID)
        return state

    else:
        # 未知操作 - 返回未更改的状态
        # TODO: 实现更多操作

        # 抛出错误，因为未知操作不应该出现
        raise ValueError(f"Unknown operation: {kind}")
