"""host-gas UF 协议上界：发射规则、两侧 drain、以及派生出的无界集合。

**为什么两侧都要单独验**：EVM 与 x86 用同名 UF，一侧漏加 `H ≤ U` 不会不健全（上界是
关于该 term 的全局事实，一侧断言在联合求解里就够），但两侧的 OOG 剪枝会不对称、路径集
发散，而**最终验证结果看不出来**。所以只能靠这里的本地断言盯住。

⚠️ 本文件**不证明上界数值正确**，也没有任何测试能证明。上界是 assume：写小了两侧仍
共享同一个 UF、仍相消、仍 UNSAT，被排除的真实轨迹在 Python 侧没有任何测试看得见。

数值是**手工同步项**，没有机器防线：依据逐条记在 `HOST_GAS_UPPER_BOUNDS` 的注释里
（Go 函数 + 分支 + 常量行号，照着读源码复核），换编译器版本时按
`docs/关键问题记录.md` #20 的流程主动走一遍。这里曾有一条比对本地 go-hpc-evm HEAD 的
测试，已删——它绑的是开发机工作区状态，与"产出被验 fixture 的那个编译器版本"没有因果
关系，却会因上游任何无关改动变红，而消红最省事的做法恰好就是它想阻止的"不复核直接改
基线"。

**上界确实在剪枝**这件事不在本文件——单元级只能证明约束进了求解器，压不出量级差别。
端到端凭证是 `tests/integration/test_gas_consistency_contracts.py::test_muti_block_gas_fixed_budget`
（曾因 OOG 分支全存活而 >25min skip，加上界后 41s / 路径数回到 30）。
"""

import os

import pytest
from z3 import BitVec, BitVecVal, Solver, ULE, sat, unsat

from evm_ir.json_parser import CompilerEVMResult
from evm_ir.models import EVMBlock, EvmOperator
from evm_ir.program import EVMProgram
from state.host_gas import (
    HOST_GAS_UF_KINDS,
    HOST_GAS_UNBOUNDED_KINDS,
    HOST_GAS_UPPER_BOUNDS,
    emit_host_gas_bound,
    host_gas_uf,
)
from state.smt_state import SMTState
from x86_64.program import X86Program

_DATA = os.path.join(os.path.dirname(__file__), "..", "data")

# 两侧执行 `SLOAD(7)` 作为本路径第 0 次 SLOAD 时，应当出现在路径约束里的那条上界。
# 两侧生成的是**同一个** AST（`ULE(host_gas_sload(7, 0), 2100)`），所以可以按结构相等比。
_SLOAD_BOUND = ULE(
    host_gas_uf("SLOAD", [BitVecVal(7, 256)], BitVecVal(0, 256)),
    BitVecVal(HOST_GAS_UPPER_BOUNDS["SLOAD"], 64),
)


# --- 1. 发射规则 ---


def test_bounded_opcode_emits_upper_bound():
    state = SMTState.create_initial_state()
    cost = BitVec("cost", 64)

    emit_host_gas_bound(state, "SLOAD", cost)

    assert len(state.pending_constraints) == 1
    solver = Solver()
    solver.add(state.pending_constraints[0], cost == BitVecVal(2101, 64))
    assert solver.check() == unsat, "上界没生效：2101 仍可满足"
    solver = Solver()
    solver.add(state.pending_constraints[0], cost == BitVecVal(2100, 64))
    assert solver.check() == sat, "上界收得过紧：边界值 2100 应当可达"


def test_selfdestruct_bound_pins_cost_to_zero():
    """SELFDESTRUCT 的上界 0 把 cost 钉死成 0。

    注意**不是**因为它用了等式：无符号下 `ULE(c, 0)` 与 `c == 0` 逻辑等价（0 是无符号
    最小值），所以 `emit_host_gas_bound` 不为 bound==0 特判。这条验的是钉死这个**效果**，
    不区分编码形式——曾经有一条测试声称在验"等式比 ULE 更强"，那个区别根本不存在。
    """
    state = SMTState.create_initial_state()
    cost = BitVec("cost", 64)

    emit_host_gas_bound(state, "SELFDESTRUCT", cost)

    solver = Solver()
    solver.add(state.pending_constraints[0], cost != BitVecVal(0, 64))
    assert solver.check() == unsat, "SELFDESTRUCT 的 cost 应当只能是 0"


@pytest.mark.parametrize("opcode", sorted(HOST_GAS_UNBOUNDED_KINDS))
def test_unbounded_opcode_emits_nothing(opcode):
    """无界 opcode 什么都不加。

    它们的 UF 照扣（无约束 UF 仍然健全），只是 OOG 分支剪不掉、路径规模偏大。宁可慢也
    不瞎编上界——上界写小了是静默缩域，没有任何测试看得见。
    """
    state = SMTState.create_initial_state()

    emit_host_gas_bound(state, opcode, BitVec("cost", 64))

    assert state.pending_constraints == []


def test_unbounded_set_is_derived_not_hardcoded():
    """无界集合必须由上界表**派生**。

    新增 host opcode 却忘了写上界时，它会自动落进无界集（照扣 UF、不剪枝），而不是被
    静默当成有界。这条锁的是"派生"这件事本身。
    """
    assert HOST_GAS_UNBOUNDED_KINDS == HOST_GAS_UF_KINDS - frozenset(HOST_GAS_UPPER_BOUNDS)
    assert frozenset(HOST_GAS_UPPER_BOUNDS) <= HOST_GAS_UF_KINDS, "上界表混进了非 host op"
    assert HOST_GAS_UNBOUNDED_KINDS == frozenset({
        "CALL", "CALLCODE", "DELEGATECALL", "STATICCALL", "CREATE", "CREATE2",
    }), "无界集变了：新成员要说明为什么写不出可剪枝的小常量上界"


# --- 2. EVM 侧 drain ---


def _sload_program() -> EVMProgram:
    """PUSH 7 / SLOAD / POP / STOP —— 最小的含 host op 的块。"""
    ops = [
        EvmOperator(kind="TAG", pc=0, param=1),
        EvmOperator(kind="PUSH", pc=0, immediate="7", param=1),
        EvmOperator(kind="SLOAD", pc=2, param=9),
        EvmOperator(kind="POP", pc=3),
        EvmOperator(kind="STOP", pc=4),
    ]
    block = EVMBlock(
        pc=0, stack_depth=0, min_depth=0, max_depth=1024, static_gas=5,
        is_jump_target=False, is_inner_block=False, is_stop=True, operations=ops,
    )
    for op in ops:
        op.block = block
    return EVMProgram(CompilerEVMResult(blocks=[block]))


def _assert_bound_in_path_constraints(paths, where: str):
    """断言 `_SLOAD_BOUND` **作为一条完整约束**出现在某条路径上。

    不能退化成「'host_gas_sload' 与 '2100' 两个子串各自出现」——那两个断言不保证来自
    同一条约束，换个路径条件本就含 gas UF 项的 fixture 就可能各自命中而漏掉 drain 缺失。
    """
    assert paths.global_states, f"{where}: 没有终止路径，测试没测到东西"
    found = [
        c
        for g in paths.global_states
        for c in g.world_state.constraints
        if c.eq(_SLOAD_BOUND)
    ]
    assert found, (
        f"{where}: 路径约束里没有 {_SLOAD_BOUND}；实际约束="
        + " | ".join(str(c) for g in paths.global_states for c in g.world_state.constraints)
    )


def test_evm_executor_drains_bound_into_path_constraints():
    """EVM 侧执行完 SLOAD 后，上界必须已在当前路径的 world_state.constraints 里。

    只挂在 `state.pending_constraints` 上而不 drain 的话，上界进不了分支可行性判定，
    剪枝收益为零，而且最终结果一切正常——静默失效。
    """
    state = SMTState.create_initial_state()
    state.host_gas_uf_enabled = True

    paths = _sload_program().to_z3_paths(state, merge_state=False)

    _assert_bound_in_path_constraints(paths, "EVM")


def test_evm_state_carrying_undrained_constraints_fails_closed():
    """带着未消费 pending_constraints 进入下一条 op ⟹ LogicError。

    这是"drain 漏了"的唯一探测手段：丢约束本身只是少剪枝（安全方向），不会有任何
    可见症状。
    """
    from utils.exceptions import LogicError

    program = _sload_program()
    state = SMTState.create_initial_state()
    state.host_gas_uf_enabled = True
    # 模拟 drain 漏掉：让 state 带着一条陈旧约束进入执行
    state.pending_constraints.append(BitVec("stale", 64) == BitVecVal(0, 64))

    with pytest.raises(LogicError, match="pending_constraints"):
        program.to_z3_paths(state, merge_state=False)


def test_pending_constraints_are_not_shared_across_copies():
    """copy 必须拷列表——共享会让未消费的约束顺着分叉扩散到 sibling。"""
    parent = SMTState.create_initial_state()
    parent.pending_constraints.append(BitVec("a", 64) == BitVecVal(1, 64))

    child = parent.copy()
    child.pending_constraints.append(BitVec("b", 64) == BitVecVal(2, 64))

    assert len(parent.pending_constraints) == 1, "子状态的约束回流到了父状态"
    assert len(child.pending_constraints) == 2


# --- 3. x86 侧 drain ---


def _load_x86(name: str) -> X86Program:
    hex_path = os.path.join(_DATA, f"{name}.hex")
    if not os.path.exists(hex_path):
        pytest.skip(f"fixture {name} 未生成")
    return X86Program.from_hex(open(hex_path, encoding="utf-8").read().strip(), base_addr=0)


def test_x86_executor_drains_bound_into_path_constraints():
    """x86 侧同样要 drain——两侧都加，OOG 剪枝才对称。

    两侧生成的是同一个 AST，所以这里比的是与 EVM 侧**完全相同**的那条约束。
    """
    x86 = _load_x86("gas_sload")
    state = SMTState.create_initial_state()
    state.host_gas_uf_enabled = True

    paths = x86.to_z3_paths(state, merge_state=False)

    _assert_bound_in_path_constraints(paths, "x86")


def test_x86_bridge_carrying_undrained_constraints_fails_closed():
    """x86 侧要有与 EVM 对称的入口守卫。

    当前唯一的 emitter 紧邻 drain，漏 drain 暂时不会发生；写上守卫是为了让机制不依赖
    "这两行恰好挨着"这个巧合。
    """
    from utils.exceptions import LogicError

    x86 = _load_x86("gas_sload")
    state = SMTState.create_initial_state()
    state.host_gas_uf_enabled = True
    state.pending_constraints.append(BitVec("stale_x86", 64) == BitVecVal(0, 64))

    with pytest.raises(LogicError, match="pending_constraints"):
        x86.to_z3_paths(state, merge_state=False)
