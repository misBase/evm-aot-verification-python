#!/usr/bin/env python3
"""P2：Tier 1 锁步归纳引擎的合成小循环端到端测试。

合成循环对（语义：`while (i != 0) i -= 1`，i 为符号输入）：

EVM（3 块）::

    header pc=0 : DUP1; ISZERO; JUMPI→30   （i==0 退出；否则 fallthrough）
    body   pc=20: PUSH 1; SWAP1; SUB; JUMP→0
    exit   pc=30: STOP

x86（手工汇编，AOT block-entry 栈窗口约定：栈顶 slot 在 [r14-0x20]）::

    0x00 header: mov rax,[r14-0x20]; test rax,rax; je 0x13
    0x09 body  : sub rax,1; mov [r14-0x20],rax; jmp 0x00
    0x13 exit  : ret

x86 只操作 limb0，因此需要循环不变式强化：栈顶 hi-192 位为 0（作为归纳
前提加在 cutpoint、作为义务在 latch/exit 重证——engine 的 extra_invariant
槽位保证强化是归纳的而非白嫖）。

负例：把 body 的减 1 改成减 2，归纳步必须给出 inconclusive（不是 proved，
也绝不报告"反例"——§6：归纳步 SAT ≠ bug）。
"""

from z3 import Array, BitVec, BitVecSort, Extract, Lambda, Select

from evm_ir.models import EVMBlock, EvmOperator
from state.smt_state import SMTState
from verification.loop_induction import (
    LoopInductionResult,
    Tier1LoopInduction,
    read_x86_stack_slot,
)
from x86_64.cfg import identify_basic_blocks
from x86_64.disassembler import disassemble_hex
from x86_64.models import Register


def _evm_block(pc, ops):
    block = EVMBlock(
        pc=pc, stack_depth=0, min_depth=0, max_depth=1024, static_gas=0,
        is_jump_target=False, is_inner_block=False, is_stop=False,
        operations=ops,
    )
    for op in ops:
        op.block = block
    return block


def _make_evm_loop_blocks():
    header = _evm_block(0, [
        EvmOperator(kind="TAG", pc=0),
        EvmOperator(kind="DUP", pc=1, param=1),
        EvmOperator(kind="ISZERO", pc=2),
        EvmOperator(kind="JUMPI", pc=3, immediate=30, is_static=True),
    ])
    body = _evm_block(20, [
        EvmOperator(kind="TAG", pc=20),
        EvmOperator(kind="PUSH", pc=21, immediate=1),
        EvmOperator(kind="SWAP", pc=22, param=1),
        EvmOperator(kind="SUB", pc=23),
        EvmOperator(kind="JUMP", pc=24, immediate=0, is_static=True),
    ])
    exit_block = _evm_block(30, [
        EvmOperator(kind="TAG", pc=30),
        EvmOperator(kind="STOP", pc=31),
    ])
    return [header, body, exit_block]


# mov rax,[r14-0x20]; test rax,rax; je +0x0a(→0x13);
# sub rax,1; mov [r14-0x20],rax; jmp -0x13(→0x00); ret
_X86_LOOP_HEX = "498b46e04885c0740a4883e801498946e0ebedc3"
# 负例：sub rax,2（一轮减 2，与 EVM 的减 1 不一致）
_X86_BUGGY_HEX = "498b46e04885c0740a4883e802498946e0ebedc3"


def _make_x86_blocks(hex_str):
    insns = disassemble_hex(hex_str, base_addr=0)
    return identify_basic_blocks(insns)


def _hi192_zero_invariant(evm_state, _x86_state):
    """循环特定 R 强化：栈顶值高 192 位为 0（x86 侧只建模了 limb0 运算）。"""
    return [Extract(255, 64, evm_state.evm_stack.peek(0)) == 0]


def _make_checker(x86_hex, timeout_ms=30000):
    return Tier1LoopInduction(
        evm_blocks=_make_evm_loop_blocks(),
        x86_blocks=_make_x86_blocks(x86_hex),
        evm_header=0,
        x86_header=0x00,
        evm_exits=[30],
        x86_exits=[0x13],
        stack_depth=1,
        timeout_ms=timeout_ms,
        extra_invariant=_hi192_zero_invariant,
    )


def test_cut_state_couples_both_sides_by_construction():
    """havoc 后的 cutpoint 状态：EVM 栈顶与 x86 栈窗口是同一组符号。"""
    from z3 import Solver, unsat, Not

    checker = _make_checker(_X86_LOOP_HEX)
    cut = checker.build_cut_state()

    solver = Solver()
    solver.add(Not(cut.evm_stack.peek(0) == read_x86_stack_slot(cut, 0)))
    assert solver.check() == unsat  # by construction 相等


def test_inductive_step_proves_synthetic_loop():
    checker = _make_checker(_X86_LOOP_HEX)
    result = checker.check_inductive_step()

    assert result.proved, f"expected proved, got {result.status}: {result.reasons}\n{result.queries}"
    # ②(b)/(c)/(a) 的查询都应实际执行过
    labels = [label for label, _ in result.queries]
    assert any("②(b)" in label for label in labels)
    assert any("②(c)" in label for label in labels)


def test_inductive_step_buggy_x86_is_inconclusive_not_counterexample():
    checker = _make_checker(_X86_BUGGY_HEX)
    result = checker.check_inductive_step()

    assert result.status == "inconclusive"
    # §6 关键语义：归纳步 SAT 不是反例，输出必须明确说明
    assert any("NOT a counterexample" in r or "diverge" in r for r in result.reasons)


def test_terminal_observables_compare_returned_memory():
    """②(d) 必须比较返回内容：同 metadata、不同返回字节的两个终止状态
    不能被判等价；写入相同字节则可证等价。"""
    from z3 import And, BitVecVal, Not, Store, unsat

    from verification.loop_induction import (
        _make_solver,
        terminal_observable_conditions,
    )
    from x86_64.models import Register

    checker = _make_checker(_X86_LOOP_HEX)

    def _states_with_byte(evm_byte, x86_byte):
        cut = checker.build_cut_state()
        evm_state = cut.copy()
        x86_state = cut.copy()
        r15 = x86_state.x86_registers.get_register(Register.R15)
        offset = BitVecVal(5, 64)
        evm_state.evm_memory.Memory = Store(
            evm_state.evm_memory.Memory, offset, BitVecVal(evm_byte, 8)
        )
        x86_state.x86_memory.evm_mem = Store(
            x86_state.x86_memory.evm_mem, r15 + offset, BitVecVal(x86_byte, 8)
        )
        return evm_state, x86_state

    # 不同返回字节：绝不可能被证明等价（fail-closed 性质）。
    # 求解器对嵌套 lambda 的模型构造可能给 unknown——sat 与 unknown 在
    # 引擎里同样走 inconclusive → 降级；唯一不可接受的是 unsat（假绿）。
    evm_state, x86_state = _states_with_byte(0xAA, 0xAB)
    solver = _make_solver(30000)
    solver.add(Not(And(*terminal_observable_conditions(evm_state, x86_state))))
    assert solver.check() != unsat

    # 相同字节：等价可证（Not(∧goals) 不可满足）——真实证明依赖的方向
    evm_state, x86_state = _states_with_byte(0xAA, 0xAA)
    solver = _make_solver(30000)
    solver.add(Not(And(*terminal_observable_conditions(evm_state, x86_state))))
    assert solver.check() == unsat


def test_exit_count_mismatch_is_inconclusive():
    checker = Tier1LoopInduction(
        evm_blocks=_make_evm_loop_blocks(),
        x86_blocks=_make_x86_blocks(_X86_LOOP_HEX),
        evm_header=0,
        x86_header=0x00,
        evm_exits=[30],
        x86_exits=[],  # 出口数不匹配
        stack_depth=1,
    )
    result = checker.check_inductive_step()
    assert result.status == "inconclusive"
    assert any("exit count mismatch" in r for r in result.reasons)


# ---------------------------------------------------------------------------
# ① Base 查询
# ---------------------------------------------------------------------------

# base 入口段（0x14 起）：把初始值 7 写入栈窗口 slot0（4 limb 全写，
# 高 limb 清零），然后跳循环头 0x00。与 EVM 侧 PUSH 7 各自独立建立
# 初值——到达时 R 是真证明义务，不是 by construction。
_X86_ENTRY_HEX = (
    "48c7c007000000"  # mov rax,7
    "498946e0"        # mov [r14-0x20],rax
    "48c7c000000000"  # mov rax,0
    "498946e8"        # mov [r14-0x18],rax
    "498946f0"        # mov [r14-0x10],rax
    "498946f8"        # mov [r14-0x08],rax
    "ebcc"            # jmp 0x00
)
# 负例：初值写 8（EVM 侧 PUSH 7）——到达时 R 不成立
_X86_ENTRY_BUGGY_HEX = _X86_ENTRY_HEX.replace("48c7c007000000", "48c7c008000000")
# 负例：入口直接跳 0x13 的 ret，永不到达循环头
_X86_ENTRY_NO_ARRIVAL_HEX = "ebfd"  # 0x14: jmp 0x13


def _make_evm_entry_block():
    return _evm_block(100, [
        EvmOperator(kind="TAG", pc=100),
        EvmOperator(kind="PUSH", pc=101, immediate=7),
        EvmOperator(kind="JUMP", pc=102, immediate=0, is_static=True),
    ])


def _make_base_checker(x86_hex):
    return Tier1LoopInduction(
        evm_blocks=_make_evm_loop_blocks() + [_make_evm_entry_block()],
        x86_blocks=_make_x86_blocks(x86_hex),
        evm_header=0,
        x86_header=0x00,
        evm_exits=[30],
        x86_exits=[0x13],
        stack_depth=1,
    )


def _make_base_initial_state():
    """base 查询的真实入口状态。合成 x86 无 TAG 序言，寄存器按 AOT 约定
    手工装载；memory 按 R15 平移耦合（对齐 build_cut_state 的姿势）。"""
    state = SMTState.create_initial_state(num_inputs=0)
    state.x86_registers.set_register(
        Register.R14,
        state.callengine_stack_base + state.callengine_stack_byte_offset,
    )
    state.x86_registers.set_register(Register.R15, state.callengine_memory_base)
    mem0 = Array("base_evm_mem0", BitVecSort(64), BitVecSort(8))
    state.evm_memory.Memory = mem0
    addr = BitVec("__base_mem_addr", 64)
    state.x86_memory.evm_mem = Lambda(
        [addr], Select(mem0, addr - state.callengine_memory_base)
    )
    return state


def test_base_query_proves_arrival_and_extracts_depth_class():
    """① Base：两侧从真实入口独立建立初值 7，到达循环头时 R 可证，
    且深度类提取为具体值 [1]。"""
    checker = _make_base_checker(_X86_LOOP_HEX + _X86_ENTRY_HEX)
    result = checker.check_base_query(
        _make_base_initial_state(), evm_entry_pc=100, x86_entry_addr=0x14,
    )

    assert result.proved, f"expected proved, got {result.status}: {result.reasons}\n{result.queries}"
    assert result.depth_classes == [1]
    labels = [label for label, _ in result.queries]
    assert any("①-R base" in label for label in labels)


def test_base_query_value_mismatch_is_inconclusive():
    """x86 入口写 8、EVM 入口 PUSH 7 ⇒ 到达时 R 不成立 ⇒ inconclusive
    （不是反例）。"""
    checker = _make_base_checker(_X86_LOOP_HEX + _X86_ENTRY_BUGGY_HEX)
    result = checker.check_base_query(
        _make_base_initial_state(), evm_entry_pc=100, x86_entry_addr=0x14,
    )

    assert result.status == "inconclusive"
    assert any("NOT a counterexample" in r for r in result.reasons)


def test_base_query_missing_x86_arrival_is_inconclusive():
    """①-对齐：EVM 到达循环头而 x86 永不到达 ⇒ 失配。"""
    checker = _make_base_checker(_X86_LOOP_HEX + _X86_ENTRY_NO_ARRIVAL_HEX)
    result = checker.check_base_query(
        _make_base_initial_state(), evm_entry_pc=100, x86_entry_addr=0x14,
    )

    assert result.status == "inconclusive"
    assert any("without x86 arrival" in r for r in result.reasons)


# ---------------------------------------------------------------------------
# ③ 出口查询
# ---------------------------------------------------------------------------

# 出口块换成真实 AOT STOP stub 形态：mov byte [r13+0xe0],2（stopped）; ret。
# status side-channel 只认 1 字节写（semantics 的 (0xE0,1) 键）；裸 ret 会把
# 默认 status=0 当 RETURNED，从栈顶读 return_offset，与 EVM STOP 不等。
_X86_LOOP_STOP_EXIT_HEX = _X86_LOOP_HEX[:-2] + "41c685e000000002" + "c3"


def _make_stop_exit_checker(evm_blocks=None):
    return Tier1LoopInduction(
        evm_blocks=evm_blocks or _make_evm_loop_blocks(),
        x86_blocks=_make_x86_blocks(_X86_LOOP_STOP_EXIT_HEX),
        evm_header=0,
        x86_header=0x00,
        evm_exits=[30],
        x86_exits=[0x13],
        stack_depth=1,
        extra_invariant=_hi192_zero_invariant,
    )


def test_exit_query_proves_synthetic_terminal():
    """③：出口延续两侧都立即终止（STOP ↔ stopped-stub ret），终止可观测量
    等价可证。"""
    checker = _make_stop_exit_checker()
    result = checker.check_exit_query(stack_depth=1)

    assert result.proved, f"expected proved, got {result.status}: {result.reasons}\n{result.queries}"
    labels = [label for label, _ in result.queries]
    assert any("③-terminal" in label for label in labels)


def test_exit_query_divergent_storage_is_inconclusive():
    """③ 负例：EVM 出口段多写一个 storage 槽而 x86 直接 ret ⇒ 终止
    可观测量不等价 ⇒ inconclusive。"""
    header, body, _ = _make_evm_loop_blocks()
    sstore_exit = _evm_block(30, [
        EvmOperator(kind="TAG", pc=30),
        EvmOperator(kind="PUSH", pc=31, immediate=1),
        EvmOperator(kind="PUSH", pc=32, immediate=0),
        EvmOperator(kind="SSTORE", pc=33),
        EvmOperator(kind="STOP", pc=34),
    ])
    checker = _make_stop_exit_checker(evm_blocks=[header, body, sstore_exit])
    result = checker.check_exit_query(stack_depth=1)

    assert result.status == "inconclusive"
    assert any("NOT a counterexample" in r for r in result.reasons)


# ---------------------------------------------------------------------------
# bridge site 显式配对校验
# ---------------------------------------------------------------------------

# 五个静态构造的 x86 块（识别边界已验证）：
#   0x00 host bridge：status=4(call_go_host_function) + func_index=9(sload)
#   0x1e builtin bridge：status=5(call_builtin_function) + func_index=0(memory_grow)
#   0x3c 错误 stub：status=14(stack_underflow)，无 lea rip ⇒ 非 bridge
#   0x48 host bridge：func_index=99（profile 中不存在）
#   0x66 未知状态码 77 + lea/ret
_X86_BRIDGE_HEX = (
    "49c785e000000004000000"  # mov qword [r13+0xe0],4
    "49c785e800000009000000"  # mov qword [r13+0xe8],9
    "488d0510000000"          # lea rax,[rip+0x10]
    "c3"
    "49c785e000000005000000"
    "41c785e400000000000000"  # mov dword [r13+0xe4],0
    "488d0510000000"
    "c3"
    "49c785e00000000e000000"
    "c3"
    "49c785e000000004000000"
    "49c785e800000063000000"
    "488d0510000000"
    "c3"
    "49c785e00000004d000000"
    "488d0510000000"
    "c3"
)


def _make_bridge_checker(evm_kinds):
    ops = [EvmOperator(kind="TAG", pc=0)] + [
        EvmOperator(kind=k, pc=i + 1) for i, k in enumerate(evm_kinds)
    ]
    return Tier1LoopInduction(
        evm_blocks=[_evm_block(0, ops)],
        x86_blocks=_make_x86_blocks(_X86_BRIDGE_HEX),
        evm_header=0,
        x86_header=0x00,
        evm_exits=[],
        x86_exits=[],
        stack_depth=1,
    )


def test_bridge_sites_host_matching_evm_op_passes():
    checker = _make_bridge_checker(["SLOAD"])
    assert checker.check_bridge_sites({0x00}) == []


def test_bridge_sites_host_without_evm_op_fails_closed():
    checker = _make_bridge_checker(["ADD"])
    reasons = checker.check_bridge_sites({0x00})
    assert len(reasons) == 1
    assert "host 'sload' has no matching EVM op" in reasons[0]


def test_bridge_sites_internal_builtin_always_allowed():
    # memory_grow 是 codegen 内部 builtin，EVM 侧无对应操作也合法
    checker = _make_bridge_checker(["ADD"])
    assert checker.check_bridge_sites({0x1E}) == []


def test_bridge_sites_error_stub_is_not_a_bridge():
    # 无 lea rip 返回地址的 ret 是错误终止 stub，不参与配对校验
    checker = _make_bridge_checker(["ADD"])
    assert checker.check_bridge_sites({0x3C}) == []


def test_bridge_sites_unknown_host_index_fails_closed():
    checker = _make_bridge_checker(["SLOAD"])
    reasons = checker.check_bridge_sites({0x48})
    assert len(reasons) == 1
    assert "unknown host func_index 99" in reasons[0]


def test_bridge_sites_unexpected_status_fails_closed():
    checker = _make_bridge_checker(["SLOAD"])
    reasons = checker.check_bridge_sites({0x66})
    assert len(reasons) == 1
    assert "unexpected status code 77" in reasons[0]
