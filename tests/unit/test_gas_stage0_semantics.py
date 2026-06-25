"""阶段0 gas 一致性:EVM 侧 gas 语义单元测试。

覆盖:
- GAS opcode 返还逻辑（镜像 go-hpc-evm compileEVMGAS:afterGas=Blk.StaticGas-Immediate）
- block 入口扣减 static_gas（镜像 makeStaticUseGas）
- GAS opcode 在裸 op（无 block/immediate）下的测试 fallback（兼容现有单测）
"""

from z3 import BitVec, BitVecVal, Extract, simplify

from state.smt_state import SMTState, EVMGasState
from evm_ir.models import EvmOperator, EVMBlock
from evm_ir.semantics import evm_operator_to_z3


def _make_block(static_gas: int) -> EVMBlock:
    return EVMBlock(
        pc=0,
        stack_depth=0,
        min_depth=0,
        max_depth=1024,
        static_gas=static_gas,
        is_jump_target=False,
        is_inner_block=False,
        is_stop=False,
    )


class TestGasOpcodeRefund:
    """GAS opcode 必须返还「本指令之后的静态 gas」。

    go-hpc-evm compileEVMGAS:x86 block 入口已扣完整 Blk.StaticGas，GAS 指令
    再 ADDQ (Blk.StaticGas - Immediate) 把多扣的加回，压栈 G - Immediate。
    """

    def test_gas_pushes_remaining_plus_after_gas(self):
        block = _make_block(static_gas=10)
        op = EvmOperator(kind="GAS", pc=0, immediate=3, block=block)

        state = SMTState()
        g = BitVec("GasRemaining", 64)
        state.evm_gas = EVMGasState(initial_gas=g)

        state = evm_operator_to_z3(op, state)

        top = state.evm_stack.peek(0)
        # 低 64 位应为 evm_gas.Gas + (static_gas - immediate) = G + (10 - 3)
        low64 = simplify(Extract(63, 0, top))
        expected = simplify(g + BitVecVal(10 - 3, 64))
        assert low64.eq(expected), f"got {low64}, expected {expected}"

    def test_gas_high_bits_zero(self):
        block = _make_block(static_gas=5)
        op = EvmOperator(kind="GAS", pc=0, immediate=2, block=block)

        state = SMTState()
        state.evm_gas = EVMGasState(initial_gas=BitVec("GasRemaining", 64))
        state = evm_operator_to_z3(op, state)

        top = state.evm_stack.peek(0)
        high = simplify(Extract(255, 64, top))
        assert high.eq(BitVecVal(0, 192))

    def test_gas_bare_op_fallback(self):
        """裸 GAS op（无 block/immediate）退回只读 evm_gas.Gas，不崩。

        现有单测可能构造没有 block 的 GAS op;阶段 0 不应一改就炸。
        """
        op = EvmOperator(kind="GAS", pc=0)  # block=None, immediate=None
        state = SMTState()
        g = BitVec("GasRemaining", 64)
        state.evm_gas = EVMGasState(initial_gas=g)

        state = evm_operator_to_z3(op, state)

        top = state.evm_stack.peek(0)
        low64 = simplify(Extract(63, 0, top))
        assert low64.eq(simplify(g)), f"bare GAS should push raw gas, got {low64}"
