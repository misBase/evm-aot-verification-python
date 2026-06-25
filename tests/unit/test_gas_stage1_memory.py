"""阶段1 内存扩展动态 gas:memory_grow builtin + memory gas helper 单元测试。"""

from z3 import BitVecVal, simplify, Solver, sat, unsat, is_app, UDiv

from state.smt_state import SMTState
from state.evm_gas_state import charge_memory_expansion_gas
from x86_64.aot_profile import GO_HPC_EVM_PROFILE
from x86_64.go_function_semantics import GoFunctionSemantics


class TestMemoryGrowBuiltin:
    """memory_grow builtin:growNumber([R13+0x108]) 已是 rounded byte size,直接用。

    Go dealWithMemoryGrow: targetMemSize := c.growNumber（不乘任何东西）。
    旧 bug: new_size_bytes = callengine_builtin_arg0 << 5（误把字节当 page 数）。
    """

    def test_memory_grow_uses_byte_size_directly(self):
        # gas 建模分支：growNumber 已是 rounded byte size，不 <<5。
        state = SMTState.create_initial_state(symbolic_gas=True)
        sem = GoFunctionSemantics(GO_HPC_EVM_PROFILE)

        # native code 写入 [R13+0x108] 的是 rounded byte size,例如 MSTORE(0) → 32B。
        state.callengine_builtin_arg0 = BitVecVal(32, 64)
        state = sem._handle_builtin_memory_grow(sp=0, mstate=state)

        got = simplify(state.callengine_memory_size_bytes)
        assert got.eq(BitVecVal(32, 64)), (
            f"memory size should be growNumber(32) directly, not 32<<5=1024; got {got}"
        )

    def test_memory_grow_larger_size(self):
        state = SMTState.create_initial_state(symbolic_gas=True)
        sem = GoFunctionSemantics(GO_HPC_EVM_PROFILE)

        state.callengine_builtin_arg0 = BitVecVal(160, 64)  # 5 words × 32
        state = sem._handle_builtin_memory_grow(sp=0, mstate=state)

        got = simplify(state.callengine_memory_size_bytes)
        assert got.eq(BitVecVal(160, 64)), f"expected 160, got {got}"

    def test_memory_grow_legacy_shift_when_gas_off(self):
        # 功能等价分支（gas off）：保留历史 <<5 行为，避免破坏既有 observable。
        state = SMTState.create_initial_state()  # gas off
        sem = GoFunctionSemantics(GO_HPC_EVM_PROFILE)
        state.callengine_builtin_arg0 = BitVecVal(32, 64)
        state = sem._handle_builtin_memory_grow(sp=0, mstate=state)
        got = simplify(state.callengine_memory_size_bytes)
        assert got.eq(BitVecVal(32 << 5, 64)), f"gas-off keeps legacy <<5; got {got}"


def _find_udiv_sizes(expr):
    """递归收集表达式里所有 UDiv(bvudiv) 节点的位宽。"""
    sizes = set()
    seen = set()

    def walk(node):
        nid = node.get_id()
        if nid in seen:
            return
        seen.add(nid)
        if is_app(node) and node.decl().name() in ("bvudiv", "bvudiv_i"):
            sizes.add(node.size())
        for i in range(node.num_args()):
            walk(node.arg(i))

    walk(expr)
    return sizes


class TestMemoryExpansionGasHelper:
    """charge_memory_expansion_gas 镜像 Go memoryGasCost 的 expansion branch。

    MSTORE(offset=0): requested=32 → mem_words=1 → square=1 → quad=floor(1/512)=0
    → new_total = 1*3 + 0 = 3。首次扩容 fee=3;同范围二次扩容 fee=0。
    """

    def test_first_expansion_charges_gas(self):
        from z3 import UGE
        state = SMTState.create_initial_state(symbolic_gas=True)
        gas_before = state.evm_gas.Gas

        state = charge_memory_expansion_gas(state, BitVecVal(32, 64))

        # fee = new_total(3) - last_gas_cost(0) = 3 → evm_gas = G - 3
        # 在 gas 充足前提下（真实验证由 program_verifier 注入 UGE(G,bound)），
        # consume_dynamic 不钳零，终值应恒为 G-3。
        solver = Solver()
        solver.add(UGE(gas_before, BitVecVal(1000, 64)))  # gas 充足
        solver.add(state.evm_gas.Gas != gas_before - BitVecVal(3, 64))
        assert solver.check() == unsat, "first 32B expansion should charge 3 gas"
        # side-channel: memory size → 32, last_gas_cost → 3
        assert simplify(state.callengine_memory_size_bytes).eq(BitVecVal(32, 64))
        assert simplify(state.callengine_memory_gas_used).eq(BitVecVal(3, 64))

    def test_second_same_range_charges_zero(self):
        state = SMTState.create_initial_state(symbolic_gas=True)
        state = charge_memory_expansion_gas(state, BitVecVal(32, 64))
        gas_after_first = state.evm_gas.Gas

        # 同范围二次访问:rounded(32) > mem_size(32) 为 false → fee=0
        state = charge_memory_expansion_gas(state, BitVecVal(32, 64))

        solver = Solver()
        solver.add(state.evm_gas.Gas != gas_after_first)
        assert solver.check() == unsat, "second same-range expansion should charge 0"

    def test_quad_div_is_128bit_for_bridge(self):
        """二次项除法必须是 128-bit UDiv,才能与 x86 div r64 (size=128) 配对。"""
        state = SMTState.create_initial_state(symbolic_gas=True)
        before = state.evm_gas.Gas
        state = charge_memory_expansion_gas(state, BitVecVal(32, 64))

        # evm_gas 表达式里应含 128-bit UDiv（quad 项），不应是 64-bit。
        sizes = _find_udiv_sizes(state.evm_gas.Gas)
        assert 128 in sizes, f"quad div must be 128-bit for div_bridge, got UDiv sizes {sizes}"
        assert 64 not in sizes, f"no 64-bit UDiv allowed (would miss bridge), got {sizes}"


class TestMloadMstore8GasWiring:
    """MLOAD/MSTORE8 复用 charge_memory_expansion_gas（与已端到端转正的 MSTORE 同源）。

    MLOAD 与 MSTORE access_size 都是 32 → gas 效果应完全一致（MSTORE 已在
    mstore_return 端到端 VERIFIED，故 MLOAD 的 gas 正确性由「同一 helper + 同
    access_size」传递）。MSTORE8 access_size=1。
    """

    def _run_op(self, kind, offset):
        from evm_ir.models import EvmOperator, EVMBlock
        from evm_ir.semantics import evm_operator_to_z3
        block = EVMBlock(pc=0, stack_depth=0, min_depth=0, max_depth=1024,
                         static_gas=0, is_jump_target=False,
                         is_inner_block=False, is_stop=False)
        state = SMTState.create_initial_state(symbolic_gas=True)
        # 压入 MLOAD 需要的 offset / MSTORE 需要的 value+offset
        if kind in ("MSTORE", "MSTORE8"):
            state.evm_stack = state.evm_stack.push(BitVecVal(0xab, 256))  # value
        state.evm_stack = state.evm_stack.push(BitVecVal(offset, 256))     # offset(top)
        op = EvmOperator(kind=kind, pc=0, block=block)
        return evm_operator_to_z3(op, state)

    def test_mload_gas_matches_mstore(self):
        from z3 import Solver, unsat
        s_load = self._run_op("MLOAD", 64)
        s_store = self._run_op("MSTORE", 64)
        solver = Solver()
        solver.add(s_load.evm_gas.Gas != s_store.evm_gas.Gas)
        assert solver.check() == unsat, "MLOAD and MSTORE(same offset) must charge identical memory gas"

    def test_mstore8_charges_smaller_or_equal(self):
        # MSTORE8 access_size=1，offset=0 时 requested=1 → mem_words=1 → 同 MSTORE(32) 的 1 word。
        # 但 offset=32 时:MSTORE8 requested=33→2 words；MSTORE requested=64→2 words（相同）。
        # 这里仅断言 MSTORE8 在 offset=0 扣 3（1 word）。
        from z3 import Solver, unsat, UGE
        s = self._run_op("MSTORE8", 0)
        before = SMTState.create_initial_state(symbolic_gas=True).evm_gas.Gas
        solver = Solver()
        solver.add(UGE(before, BitVecVal(1000, 64)))
        # MSTORE8(offset=0): requested=1 → mem_words=1 → new_total=3 → fee=3
        solver.add(s.evm_gas.Gas != before - BitVecVal(3, 64))
        assert solver.check() == unsat, "MSTORE8(offset=0) should charge 3 (1 word)"
