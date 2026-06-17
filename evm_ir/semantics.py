"""
EVM IR语义建模。

本模块使用Z3为EVM IR操作提供语义建模。
"""

from z3 import BitVec, BitVecRef, BitVecVal, Concat, Extract, If, UGE, ULT, And, Or, UDiv, URem, LShR, SignExt, ZeroExt, Lambda, Select
from typing import List, Optional, Dict, Any, Tuple
from .models import EVMBlock, EvmOperator
from common.uint256 import Uint256
from common import uninterpreted
from common.calldata import calldataload_no_overflow_assumption, calldataload_word
from common.arithmetic import div_semantics as _div_semantics, mod_semantics as _mod_semantics, exp_semantics as _exp_semantics, addmod_semantics as _addmod_semantics, mulmod_semantics as _mulmod_semantics, eq_borrow_chain_assumption
from state.smt_state import SMTState, EVMStackState, EVMMemoryState

# RETURN指令的常量
MAX_RETURN_DATA_SIZE = 256  # 最大返回数据大小（字节）（256字节 = 2048位）


def _truncate_to_64(value: BitVecRef) -> BitVecRef:
    """将BitVec偏移量截断到64位。"""
    if value.size() == 64:
        return value
    if value.size() == 256:
        return Extract(63, 0, value)
    raise ValueError(f"Expected 64-bit or 256-bit BitVec, got {value.size()} bits")


def _uint256_to_u64_with_overflow_max(value: BitVecRef) -> BitVecRef:
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
    """Apply symbolic call return-data writes to EVM memory."""
    return _write_symbolic_memory_slice(
        memory_state,
        ret_offset_bv,
        ret_size_bv,
        return_byte_fn,
        effect_tag=f"call_ret_idx_{effect_id}",
        should_copy=should_copy,
    )


def _write_symbolic_memory_slice(memory_state: EVMMemoryState,
                                 dest_offset_bv: BitVecRef,
                                 size_bv: BitVecRef,
                                 byte_fn,
                                 effect_tag: str,
                                 should_copy=None) -> EVMMemoryState:
    """Apply a symbolic byte slice write to EVM memory."""
    dest_offset_64 = _truncate_to_64(dest_offset_bv)
    size_64 = _truncate_to_64(size_bv)
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

    end_offset = dest_offset_64 + size_64
    grown_msize = If(
        And(size_64 != zero_64, UGE(end_offset, memory_state.MSize)),
        end_offset,
        memory_state.MSize,
    )
    updated_msize = grown_msize if should_copy is None else If(should_copy, grown_msize, memory_state.MSize)
    return EVMMemoryState(memory_array=updated_memory, msize=updated_msize)


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
        """构建EVM SDIV操作的逻辑公式 (a sdiv b)。"""
        a_bv = self._to_bv256(a)
        b_bv = self._to_bv256(b)
        # BitVec 的 / 运算符是有符号除法（bvsdiv）
        return If(b_bv == BitVecVal(0, 256), BitVecVal(0, 256), a_bv / b_bv)

    def smod_semantics(self, a: BitVec, b: BitVec) -> BitVec:
        """构建EVM SMOD操作的逻辑公式。"""
        a_bv = self._to_bv256(a)
        b_bv = self._to_bv256(b)
        zero = BitVecVal(0, 256)
        # SMOD: sign(a) * (abs(a) mod abs(b))
        a_abs = If(a_bv < zero, -a_bv, a_bv)
        b_abs = If(b_bv < zero, -b_bv, b_bv)
        rem_abs = URem(a_abs, b_abs)
        signed_rem = If(a_bv < zero, -rem_abs, rem_abs)
        return If(b_bv == zero, zero, signed_rem)

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
        # TAG对语义是无操作（仅标记块入口）
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
        return state

    elif kind == "SDIV":
        a, stack_after_pop1 = state.evm_stack.pop()
        b, stack_after_pop2 = stack_after_pop1.pop()
        result = op_semantics.sdiv_semantics(a, b)
        state.evm_stack = stack_after_pop2.push(result)
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
        return state

    elif kind == "EXP":
        base, stack_after_pop1 = state.evm_stack.pop()
        exponent, stack_after_pop2 = stack_after_pop1.pop()
        result = op_semantics.exp_semantics(base, exponent)
        state.evm_stack = stack_after_pop2.push(result)
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
        mem_value, new_memory_state = state.evm_memory.load_256bit(offset_bv)
        state.evm_stack = stack_after_pop.push(mem_value)
        state.evm_memory = new_memory_state
        return state
    
    elif kind == "MSTORE":
        # MSTORE：弹出偏移量和值，将32字节存储到内存
        offset_bv, stack_after_pop1 = state.evm_stack.pop()
        value, stack_after_pop2 = stack_after_pop1.pop()
        new_memory_state = state.evm_memory.store_256bit(offset_bv, value)
        state.evm_stack = stack_after_pop2
        state.evm_memory = new_memory_state
        return state

    elif kind == "MSTORE8":
        # MSTORE8：先弹出偏移量，再弹出值；仅写入低8位
        offset_bv, stack_after_pop1 = state.evm_stack.pop()
        value_bv, stack_after_pop2 = stack_after_pop1.pop()
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
        return state

    elif kind == "SSTORE":
        # SSTORE: Pop key and value, store in storage
        key, stack_after_pop1 = state.evm_stack.pop()
        val, stack_after_pop2 = stack_after_pop1.pop()
        state.evm_storage = state.evm_storage.sstore(key, val)
        state.evm_stack = stack_after_pop2
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
        # 在 overflow 时都返回 0，所以剪掉这个分支对 refinement 仍 sound；
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

        # Go 解释器对 dataOffset 使用 Uint64WithOverflow，溢出时钳到 MaxUint64
        calldata_offset_64 = _uint256_to_u64_with_overflow_max(data_offset_bv)
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

        code_offset_64 = _uint256_to_u64_with_overflow_max(code_offset_bv)
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

        data_offset_64 = _uint256_to_u64_with_overflow_max(data_offset_bv)

        def return_data_byte(relative_index):
            return Select(state.return_data, data_offset_64 + relative_index)

        state.evm_memory = _write_symbolic_memory_slice(
            state.evm_memory,
            mem_offset_bv,
            length_bv,
            return_data_byte,
            effect_tag=f"returndatacopy_idx_{op.pc}",
        )
        state.evm_stack = stack_after_pop3
        return state

    elif kind == "CALLVALUE":
        # CALLVALUE: Push callvalue onto stack
        state.evm_stack = state.evm_stack.push(state.callvalue)
        return state

    elif kind == "SHA3":
        offset_bv, stack_after_pop1 = state.evm_stack.pop()
        length_bv, stack_after_pop2 = stack_after_pop1.pop()
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

        dst_offset_64 = _truncate_to_64(dst_offset_bv)
        src_offset_64 = _truncate_to_64(src_offset_bv)
        length_64 = _truncate_to_64(length_bv)
        old_memory = state.evm_memory.Memory

        state.evm_memory = _write_symbolic_memory_slice(
            state.evm_memory,
            dst_offset_bv,
            length_bv,
            lambda relative_index: Select(old_memory, src_offset_64 + relative_index),
            effect_tag=f"mcopy_idx_{op.pc}",
        )
        copied_end = dst_offset_64 + length_64
        state.evm_memory = EVMMemoryState(
            memory_array=state.evm_memory.Memory,
            msize=If(UGE(copied_end, state.evm_memory.MSize), copied_end, state.evm_memory.MSize),
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
        # GAS: Push current gas counter onto stack
        # Gas is 64-bit, zero-extend to 256-bit for stack
        gas_256 = ZeroExt(192, state.evm_gas.Gas)
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
        return state

    elif kind == "SELFBALANCE":
        result = uninterpreted.self_balance_semantics()
        state.evm_stack = state.evm_stack.push(result)
        return state

    elif kind == "EXTCODESIZE":
        addr_bv, stack1 = state.evm_stack.pop()
        result = uninterpreted.ext_code_size_semantics(addr_bv)
        state.evm_stack = stack1.push(result)
        return state

    elif kind == "EXTCODECOPY":
        addr_bv, stack1 = state.evm_stack.pop()
        dest_offset_bv, stack2 = stack1.pop()
        offset_bv, stack3 = stack2.pop()
        size_bv, stack4 = stack3.pop()
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
        return state

    elif kind == "EXTCODEHASH":
        addr_bv, stack1 = state.evm_stack.pop()
        result = uninterpreted.ext_code_hash_semantics(addr_bv)
        state.evm_stack = stack1.push(result)
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
        _, stack1 = state.evm_stack.pop()
        state.evm_stack = stack1
        return state

    elif kind == "CREATE":
        value_bv, stack1 = state.evm_stack.pop()
        offset_bv, stack2 = stack1.pop()
        size_bv, stack3 = stack2.pop()
        result = uninterpreted.create_semantics(
            value_bv, offset_bv, size_bv, state.evm_memory.Memory, effect_id=op.pc
        )
        state.evm_stack = stack3.push(result)
        return state

    elif kind == "CREATE2":
        value_bv, stack1 = state.evm_stack.pop()
        offset_bv, stack2 = stack1.pop()
        size_bv, stack3 = stack2.pop()
        salt_bv, stack4 = stack3.pop()
        result = uninterpreted.create2_semantics(
            value_bv, offset_bv, size_bv, salt_bv, state.evm_memory.Memory, effect_id=op.pc
        )
        state.evm_stack = stack4.push(result)
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
        state.evm_stack = stack7.push(result)
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
        state.evm_stack = stack7.push(result)
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
        state.evm_stack = stack6.push(result)
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
        state.evm_stack = stack6.push(result)
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
        
        # 在状态中存储返回偏移量和长度
        # 我们不提取数据 - 我们将在RefinementChecker中直接比较内存
        # 注意：RETURN只读取内存，不修改内存或MSize
        state.return_offset = return_offset_64
        state.return_length = return_length_64
        
        # 更新栈（两个值都已弹出）
        state.evm_stack = stack_after_pop2
        
        return state
    
    elif kind == "JUMPI":
        # JUMPI: dest, cond = pop, pop
        # 在当前 IR 中，如果 is_static 且有 immediate，则 dest 已被折叠，只需弹出 cond
        if op.is_static and op.immediate is not None:
            _, state.evm_stack = state.evm_stack.pop()
        else:
            # 动态跳转：弹出 dest 和 cond
            _, state.evm_stack = state.evm_stack.pop()
            _, state.evm_stack = state.evm_stack.pop()
        return state

    elif kind == "JUMP":
        # JUMP: dest = pop
        # 如果 is_static 且有 immediate，则 dest 已被折叠，无需弹出
        if not (op.is_static and op.immediate is not None):
            _, state.evm_stack = state.evm_stack.pop()
        return state

    elif kind == "REVERT":
        # REVERT: offset, length = pop, pop
        offset_bv, stack_after_pop1 = state.evm_stack.pop()
        length_bv, stack_after_pop2 = stack_after_pop1.pop()

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
        return state

    elif kind == "STOP":
        # STOP: 对状态无堆栈影响
        return state

    elif kind == "LOG":
        # LOG指令：从栈中弹出参数并记录事件
        # immediate 字段表示主题数量 (0-4)
        # LOG[n] 弹出 (2+n) 个值: offset, size, topic1...topicn
        # TODO: 占位实现：只弹出值，不实际记录事件日志

        # 获取主题数量
        num_topics = op.immediate if op.immediate is not None else 0

        # 弹出 offset 和 size（栈顶两个）
        _, state.evm_stack = state.evm_stack.pop()
        _, state.evm_stack = state.evm_stack.pop()

        # 弹出所有主题
        for _ in range(num_topics):
            _, state.evm_stack = state.evm_stack.pop()

        return state

    elif kind == "INVALID":
        # INVALID: Marks the transaction as invalid / stops execution
        # INVALID is a terminal operation like STOP
        return state

    else:
        # 未知操作 - 返回未更改的状态
        # TODO: 实现更多操作

        # 抛出错误，因为未知操作不应该出现
        raise ValueError(f"Unknown operation: {kind}")


def execute_block_with_tag(block: EVMBlock, state: SMTState) -> Tuple[SMTState, Dict[str, Any]]:
    """使用基于TAG的路径分割执行块（级别1：块级合并）。
    
    TAG指令创建3条路径：
    - 路径1：SP < min_depth -> 错误路径（返回错误状态码）
    - 路径2：SP > max_depth -> 错误路径（返回错误状态码）
    - 路径3：min_depth <= SP <= max_depth -> 正常执行路径
    
    这3条路径使用Z3 If表达式合并。
    
    Args:
        block: 要执行的EVM块
        state: 初始SMT状态
        
    Returns:
        (merged_state, result_dict)元组，其中：
        - merged_state: 包含所有3条路径合并结果的状态
        - result_dict: 包含合并返回值的字典（offset, length, memory, has_return_data）
    """
    from z3 import IntVal
    
    # 获取栈指针作为Int（SP在EVMStackState中是Int类型）
    sp = state.evm_stack.SP
    
    # 将min_depth和max_depth转换为Int以便比较
    min_depth_int = IntVal(block.min_depth)
    max_depth_int = IntVal(block.max_depth)
    
    # 构建路径条件
    # 路径1：SP < min_depth -> 错误
    path1_condition = sp < min_depth_int
    
    # 路径2：SP > max_depth -> 错误
    path2_condition = sp > max_depth_int
    
    # 路径3：min_depth <= SP <= max_depth -> 正常
    path3_condition = And(sp >= min_depth_int, sp <= max_depth_int)
    
    # 执行路径1：SP < min_depth -> 错误路径
    # 错误路径返回错误状态码（当前抽象下不暴露非空 return data）
    from z3 import BitVecVal
    path1_state = state.copy()
    path1_state.return_offset = BitVecVal(0, 64)
    path1_state.return_length = BitVecVal(0, 64)
    # 注意：在实际实现中，我们可能会设置特定的错误状态码。
    # 当前抽象只保留“是否暴露非空 return data”这一外部可观察效果。
    
    # 执行路径2：SP > max_depth -> 错误路径
    path2_state = state.copy()
    path2_state.return_offset = BitVecVal(0, 64)
    path2_state.return_length = BitVecVal(0, 64)
    
    # 执行路径3：min_depth <= SP <= max_depth -> 正常执行
    path3_state = state.copy()
    
    # 执行块中的所有操作（跳过TAG和BLOCKEND）
    for op in block.operations:
        kind = op.kind.upper()
        if kind == "TAG":
            # TAG在块级别处理，这里跳过
            continue
        elif kind == "BLOCKEND":
            # BLOCKEND是标记，跳过
            continue
        else:
            # 执行操作
            path3_state = op.to_z3(path3_state)
    
    # 使用If表达式合并3条路径
    # 结构：If(path1_cond, path1_result, If(path2_cond, path2_result, path3_result))
    merged_state = state.copy()
    
    # 合并return_offset
    merged_state.return_offset = If(
        path1_condition,
        path1_state.return_offset,
        If(
            path2_condition,
            path2_state.return_offset,
            path3_state.return_offset
        )
    )
    
    # 合并return_length
    merged_state.return_length = If(
        path1_condition,
        path1_state.return_length,
        If(
            path2_condition,
            path2_state.return_length,
            path3_state.return_length
        )
    )
    
    # 合并内存（EVM内存Array）
    # 注意：内存合并更复杂，我们需要合并整个Array
    # 目前，我们使用path3的内存（正常路径），因为错误路径不修改内存
    # 在更复杂的实现中，我们可能需要逐元素合并Arrays
    merged_state.evm_memory = path3_state.evm_memory
    
    # 合并栈
    # 类似于内存，我们使用path3的栈进行正常执行
    # 错误路径不会有意义地修改栈
    merged_state.evm_stack = path3_state.evm_stack
    
    # 构建结果字典
    from z3 import BitVecVal
    has_return_data = merged_state.return_length != BitVecVal(0, 64)
    
    result = {
        'offset': merged_state.return_offset,
        'length': merged_state.return_length,
        'memory': merged_state.evm_memory.Memory,
        'base_addr': None,  # EVM内存使用直接偏移量
        'has_return_data': has_return_data
    }
    
    return merged_state, result
