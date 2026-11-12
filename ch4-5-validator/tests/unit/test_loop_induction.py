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

from z3 import Array, BitVec, BitVecSort, BitVecVal, Extract, Lambda, Select

from evm_ir.models import EVMBlock, EvmOperator
from state.smt_state import SMTState, MemoryDomain
from x86_64.aot_profile import AOT_COMPILER_PROFILE
from verification.loop_induction import (
    LoopInductionResult,
    Tier1LoopInduction,
    read_x86_stack_slot,
)
from x86_64.cfg import identify_basic_blocks
from x86_64.disassembler import disassemble_hex
from x86_64.models import Register


def _evm_block(pc, ops, is_jump_target=False):
    block = EVMBlock(
        pc=pc, stack_depth=0, min_depth=0, max_depth=1024, static_gas=0,
        is_jump_target=is_jump_target, is_inner_block=False, is_stop=False,
        operations=ops,
    )
    for op in ops:
        op.block = block
    return block


def _make_evm_loop_blocks():
    header = _evm_block(0, is_jump_target=True, ops=[
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
    exit_block = _evm_block(30, is_jump_target=True, ops=[
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
        # havoc 后两侧 status 是**独立符号**——status 不进 R 的等式分量，
        # 「两侧均 running」由结构前提单独核对（§4.5.6）。本用例要隔离的是
        # ②(d) 的**返回内容**比较，所以把 status 对齐成同一个值；不对齐的话
        # status 那一项恒不成立，整个合取永远证不出 unsat，测到的就不是
        # memory 而是 status 了。
        x86_state.callengine_status_code = evm_state.error_code
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


def _make_base_initial_state(stack_byte_offset: int = 0x20):
    """base 查询的真实入口状态。合成 x86 无 TAG 序言，寄存器按 AOT 约定
    手工装载；memory 按 R15 平移耦合（对齐 build_cut_state 的姿势）。

    ``stack_byte_offset`` 必须等于**到达循环头时**的深度类 × 0x20（这里 k=1
    ⇒ 0x20）。真实 AOT 里这个值由块入口 TAG 序言的
    ``mov r14,[r13+0x38]; add r14,[r13+0x30]`` 装载，合成 hex 没有 TAG 序言，
    只能在初始状态里摆好——否则 R 的 ``stack_geometry`` 分量（要求
    ``callengine_stack_byte_offset == depth * 0x20``）在到达时不成立。
    同一 block 内该值恒定，故入口处就设成循环头的值是忠实的。
    """
    state = SMTState.create_initial_state(num_inputs=0)
    offset = BitVecVal(stack_byte_offset, 64)
    state.callengine_stack_byte_offset = offset
    r13 = state.x86_registers.get_register(Register.R13)
    state.x86_memory = state.x86_memory.store_limb(
        r13 + BitVecVal(AOT_COMPILER_PROFILE.offsets["stack_byte_offset"], 64),
        offset,
        domain=MemoryDomain.CALLENGINE,
    )
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


# ---------------------------------------------------------------------------
# envelope 取消：TAG 错误终态改为可配对 terminal outcome（§4.2 ②(d)）
# ---------------------------------------------------------------------------

def _x86_error_stub_hex(status_code: int) -> str:
    """写 [r13+0xe0] = status 并 ret 的错误 stub（对应 TAG 守卫的错误分支）。

    `mov byte ptr [r13+0xe0], imm8` = 41 c6 85 <disp32-le> <imm8>
    （REX.B + C6 /0，ModRM.rm=101 配 mod=10 ⇒ r13 + disp32）。状态码是
    **单字节**写——用 qword 宽度会被 `_maybe_update_callengine_field`
    以"side-channel write width is not modeled"拒绝。
    """
    return "41c685e0000000" + f"{status_code:02x}" + "c3"


def test_terminal_observables_include_status_code():
    """②(d) 必须比较 status code。

    没有它，两侧停在**不同**的错误码上（如 EVM 给 STOPPED 而 x86 给
    OUT_OF_GAS）也会被判等价——这正是 envelope 取消后必须补上的那一条。
    用语义检查而不是看渲染字符串：两侧都是 0 时等式会被 simplify 成 True。
    """
    from z3 import BitVecVal, Not, And, Solver, sat, unsat

    from verification.loop_induction import terminal_observable_conditions

    evm_state = SMTState.create_initial_state(num_inputs=0)
    x86_state = SMTState.create_initial_state(num_inputs=0)

    # EVM 停在 STOPPED(2)、x86 停在 OUT_OF_GAS(12) ⇒ 终止义务必须被违反
    evm_state.error_code = BitVecVal(2, 64)
    x86_state.callengine_status_code = BitVecVal(12, 64)
    conditions = terminal_observable_conditions(evm_state, x86_state)

    solver = Solver()
    solver.add(And(*conditions))
    assert solver.check() == unsat, (
        "status 不同的两个终止状态仍被判可等价——②(d) 缺 status code"
    )


def test_terminal_observables_compare_gas_only_when_asked():
    """gas 的双重身份：terminal 比较只在 FIXED_BUDGET/FULL 档（§4.1）。

    cutpoint 上的 gas 相等是 R 的分量（三档都要，见 test_cutpoint_relation），
    与这里的 terminal 比较是两件事；混同会得出"OFF 档也在比较 gas"的错误结论。
    """
    from verification.loop_induction import terminal_observable_conditions

    evm_state = SMTState.create_initial_state(num_inputs=0)
    x86_state = SMTState.create_initial_state(num_inputs=0)

    without_gas = terminal_observable_conditions(evm_state, x86_state)
    with_gas = terminal_observable_conditions(
        evm_state, x86_state, compare_gas=True
    )
    assert len(with_gas) == len(without_gas) + 1


def test_error_stub_terminal_paths_are_kept_not_dropped():
    """x86 的 TAG 错误终态必须进入路径列表，交给 ②(d) 配对证明。

    旧行为（no-OOG/no-stack-limit envelope）把这些路径整个 `continue` 掉，
    于是 EVM 侧的 OUT_OF_GAS 终态在矩阵里找不到 partner —— 那不是"证明"，
    是把证明义务删掉了。develop 的 EVM 侧已镜像 TAG 三分支
    （`evm_ir/cfg_executor.py`），排除的理由不复存在。
    """
    from verification.loop_induction import run_x86_segment

    # 单块：直接写 OUT_OF_GAS(12) 状态码并 ret
    blocks = _make_x86_blocks(_x86_error_stub_hex(12))
    state = SMTState.create_initial_state(num_inputs=0)
    state.x86_registers.set_register(
        Register.R14,
        state.callengine_stack_base + state.callengine_stack_byte_offset,
    )
    state.x86_registers.set_register(Register.R15, state.callengine_memory_base)

    paths, defects, notes = run_x86_segment(
        blocks, state, entry_addr=0x00, stop_addrs=set(),
        aot_profile=AOT_COMPILER_PROFILE,
    )

    terminals = [p for p in paths if p.kind == "terminal"]
    assert terminals, "错误终态被丢弃了——envelope 排除逻辑仍在"
    assert any("paired terminal outcome" in n for n in notes)
    assert not any("excluded by no-OOG" in n for n in notes)


def test_error_stub_is_still_not_a_pairable_exit():
    """但错误 stub 仍**不是**可配对出口（§4.2）：它不回循环头也不走正常出口。

    这一条与上一条不矛盾：出口边按地址配对，错误终态按 status 归入 ②(d)。
    """
    checker = Tier1LoopInduction(
        evm_blocks=_make_evm_loop_blocks(),
        x86_blocks=_make_x86_blocks(_X86_LOOP_HEX + _x86_error_stub_hex(12)),
        evm_header=0,
        x86_header=0x00,
        evm_exits=[30],
        x86_exits=[0x13, 0x14],  # 0x14 是错误 stub
        stack_depth=1,
    )
    assert 0x14 not in checker.x86_exits


# ---------------------------------------------------------------------------
# gas 进 R 与 ②(e) 终止义务
# ---------------------------------------------------------------------------

def test_gas_in_relation_catches_one_sided_gas_accounting():
    """gas 是 R 的分量，而且**有牙**。

    合成 x86 没有 TAG 序言的 `makeStaticUseGas`，所以只要给 EVM 块设
    `static_gas > 0`，就制造了"一侧扣 gas、另一侧不扣"的记账不一致。
    envelope 时代 gas 不在 R 里、OOG 又被假设掉，这种偏差不会被发现；
    现在必须当场 inconclusive。

    注意方向：这是**降级**（inconclusive）不是反例报告——§6 的"归纳步
    SAT ≠ 找到 bug"同样适用。
    """
    blocks = _make_evm_loop_blocks()
    for block in blocks:
        block.static_gas = 3

    checker = Tier1LoopInduction(
        evm_blocks=blocks,
        x86_blocks=_make_x86_blocks(_X86_LOOP_HEX),
        evm_header=0,
        x86_header=0x00,
        evm_exits=[30],
        x86_exits=[0x13],
        stack_depth=1,
        extra_invariant=_hi192_zero_invariant,
    )
    result = checker.check_inductive_step()

    assert result.status == "inconclusive"
    assert any("NOT a counterexample" in r for r in result.reasons)


def test_termination_evidence_is_separate_from_synchronisation():
    """②(e) 与 ②(a)–(d) 是两个不同结论，必须分别报告。

    合成循环的块 `static_gas=0`，模型里 gas 不递减 ⇒ **终止性证不出**；
    但两侧锁步同步是成立的。把两者混进一个 `proved` 字段会让"同步已证"
    冒充"终止已证"。
    """
    checker = _make_checker(_X86_LOOP_HEX)
    result = checker.check_inductive_step()

    assert result.proved, "锁步同步应当成立"
    assert result.termination is not None
    assert result.termination.latch_arms_checked == 1
    # static_gas=0 ⇒ 这条 latch arm 上 gas 不严格递减
    assert not result.termination.all_arms_decrease

    labels = [label for label, _ in result.queries]
    assert any("②(e)" in label for label in labels), "②(e) 查询没有实际执行"


def test_termination_evidence_records_external_premises():
    """六项前提里本处只证一条，其余必须逐条记录供证书汇总（§4.5）。

    只写在文档里的前提不是"主证明可消费的证据"。
    """
    checker = _make_checker(_X86_LOOP_HEX)
    evidence = checker.check_inductive_step().termination

    assert evidence.no_wraparound_basis is not None
    assert "consume_static" in evidence.no_wraparound_basis
    # 段覆盖 / 内层循环 / SCC / stuttering / fail-closed 五条
    assert len(evidence.external_premises) == 5


# ---------------------------------------------------------------------------
# 深度类完备性的两条义务（§4.1）
# ---------------------------------------------------------------------------

def test_depth_class_transition_closure_on_synthetic_loop():
    """(ii) 转移封闭：latch 回到循环头时栈深仍在已登记集合内。"""
    checker = _make_checker(_X86_LOOP_HEX)
    evidence = checker.check_inductive_step().depth_evidence

    assert evidence is not None
    assert evidence.registered_classes == (1,)
    assert evidence.latch_transitions_checked == 1
    assert evidence.transition_closed
    assert evidence.escaping_depths == ()


def test_depth_class_escape_is_recorded_not_silently_accepted():
    """逃逸到未登记深度类必须被记录。

    这正是"仅遇到新 class 就 fail-closed 不够"的那一半：真正的义务是
    **转移封闭**——已登记 class 的 latch 只能转移到已登记集合内。落在集合
    外意味着存在未登记的深度类，枚举不完整。
    """
    from verification.loop_induction import SegmentPath

    checker = _make_checker(_X86_LOOP_HEX)
    cut = checker.build_cut_state()

    # 伪造一条 latch：栈深从 1 变成 2（未登记）
    escaped = cut.copy()
    escaped.evm_stack = escaped.evm_stack.push(BitVecVal(9, 256))
    paths = [
        SegmentPath(kind="latch", location=0, condition=None, state=escaped)
    ]
    evidence = checker._check_depth_transition_closure(paths)

    assert not evidence.transition_closed
    assert evidence.escaping_depths == (2,)


def test_symbolic_latch_depth_counts_as_escape():
    """符号栈深无法判定封闭性 ⇒ 按逃逸处理（fail-closed 方向）。"""
    from z3 import Int

    from verification.loop_induction import SegmentPath

    checker = _make_checker(_X86_LOOP_HEX)
    cut = checker.build_cut_state()
    symbolic = cut.copy()
    symbolic.evm_stack.SP = Int("symbolic_sp")

    evidence = checker._check_depth_transition_closure(
        [SegmentPath(kind="latch", location=0, condition=None, state=symbolic)]
    )
    assert not evidence.transition_closed


def test_base_query_records_arrival_coverage_basis():
    """(i) 首次到达覆盖：依据必须落在证据里，不能只写在文档中（§4.5）。"""
    checker = _make_base_checker(_X86_LOOP_HEX + _X86_ENTRY_HEX)
    result = checker.check_base_query(
        _make_base_initial_state(), evm_entry_pc=100, x86_entry_addr=0x14,
    )

    evidence = result.depth_evidence
    assert evidence is not None
    assert evidence.registered_classes == (1,)
    assert evidence.arrival_coverage_basis is not None
    assert "coverage certificate" in evidence.arrival_coverage_basis
    # Base 只负责 (i)；(ii) 是归纳步的义务，此处不应冒充已证
    assert not evidence.transition_closed


# ---------------------------------------------------------------------------
# 段结构校验（§4.3）：按静态可达块扫描，而不是只扫循环体
# ---------------------------------------------------------------------------

def test_gas_opcode_in_segment_is_rejected():
    """段内可达 `GAS` ⇒ 结构预检拒绝。

    `compileEVMGAS` 返回 `Blk.StaticGas - Immediate`，与 EVM 侧在 havoc 的
    符号 gas 下是否逐字对齐尚未核实——保守拒绝，方向只多降级。
    """
    blocks = _make_evm_loop_blocks()
    body = next(b for b in blocks if b.pc == 20)
    body.operations.insert(1, EvmOperator(kind="GAS", pc=21))
    body.operations[1].block = body

    checker = Tier1LoopInduction(
        evm_blocks=blocks,
        x86_blocks=_make_x86_blocks(_X86_LOOP_HEX),
        evm_header=0, x86_header=0x00,
        evm_exits=[30], x86_exits=[0x13], stack_depth=1,
    )
    result = checker.check_inductive_step()
    assert result.status == "inconclusive"
    assert any("GAS" in r for r in result.reasons)


def test_msize_is_allowed_once_msize_is_in_the_relation():
    """`MSIZE` 不再无条件拒绝：R 的 `memory_size` 分量已钉住两侧 MSize。

    旧版把 MSIZE 与 GAS 一并拒掉，那是 MSize 尚未进 R 时的保守做法；现在
    继续拒就只是无谓降级。
    """
    from verification.cutpoint_relation import CutpointRelationSchema
    from verification.segment_validation import SegmentStructuralValidator

    blocks = _make_evm_loop_blocks()
    body = next(b for b in blocks if b.pc == 20)
    body.operations.insert(1, EvmOperator(kind="MSIZE", pc=21))
    body.operations[1].block = body

    schema = CutpointRelationSchema()
    assert schema.supports_msize

    check = SegmentStructuralValidator().validate_evm(
        blocks, entry_pc=0, stop_pcs={0, 30},
        supports_msize=schema.supports_msize,
    )
    assert check.ok, f"MSIZE 不该被拒: {check.reasons}"

    # 反向：R 里没有 MSize 时必须拒
    denied = SegmentStructuralValidator().validate_evm(
        blocks, entry_pc=0, stop_pcs={0, 30}, supports_msize=False,
    )
    assert not denied.ok
    assert any("MSIZE" in r for r in denied.reasons)


def test_segment_validation_scans_reachable_blocks_not_just_body():
    """校验范围是「段入口到 stop 的静态可达块」，不是调用方给的 body 集合。

    旧版只扫 `evm_body`；循环体经未登记边到达、但仍在本次段执行范围内的块
    会被漏掉。这里把 GAS 放在 body 集合**之外**但仍可达的块上。
    """
    blocks = _make_evm_loop_blocks()
    exit_block = next(b for b in blocks if b.pc == 30)
    exit_block.operations.insert(1, EvmOperator(kind="GAS", pc=31))
    exit_block.operations[1].block = exit_block

    checker = Tier1LoopInduction(
        evm_blocks=blocks,
        x86_blocks=_make_x86_blocks(_X86_LOOP_HEX),
        evm_header=0, x86_header=0x00,
        evm_exits=[30], x86_exits=[0x13], stack_depth=1,
        evm_body={0, 20},          # 故意不含 pc=30
    )
    result = checker.check_inductive_step()
    assert result.status == "inconclusive"
    assert any("GAS" in r for r in result.reasons)


# ---------------------------------------------------------------------------
# 域约束：按侧取正确的 MSize 字段（§4.4 ②）
# ---------------------------------------------------------------------------


def test_domain_goals_read_the_semantic_msize_on_the_evm_side():
    """`_domain_goals` 必须按侧传 `side`。

    两侧的"内存大小"落在不同字段上：EVM 侧是 `evm_memory.MSize`
    （`evm_ir.semantics_gas.charge_dynamic_gas` 的唯一写入点），x86 侧是
    callEngine 镜像 `callengine_memory_size_bytes`。两侧都读镜像字段时，EVM
    侧读到的永远是 havoc 原值——域约束在 havoc 里已被 assume，义务因此**恒真**。
    那不是"两侧都证过"，是只证了一侧，而 §4.4 ② 恰恰写着不能靠 R 的
    `memory_size` 分量省掉一侧。
    """
    from z3 import And, BitVec, Not, SolverFor, sat

    checker = _make_checker(_X86_LOOP_HEX)
    cut = checker.build_cut_state()
    evm_state, x86_state = cut.copy(), cut.copy()
    # 只把 EVM 侧的**语义**字段顶出域外，镜像字段保持 havoc 原值：这正是
    # "EVM 侧扩容了一轮"在状态上的样子。
    evm_state.evm_memory.MSize = BitVec("escaped_msize", 64)

    solver = SolverFor("QF_AUFBV")
    solver.set("timeout", 20000)
    solver.add(Not(And(*checker._domain_goals(evm_state, x86_state))))
    assert solver.check() == sat, (
        "EVM 侧域义务没读 evm_memory.MSize —— 它恒真，等于没证"
    )


# ---------------------------------------------------------------------------
# 路径已判定的 ITE 极性（提速，soundness 中性）
# ---------------------------------------------------------------------------


def _shared_ite_goals(condition):
    """两个共用同一条件的 BV-ITE 结点（够到 `_ITE_POLARITY_MIN_SITES`）。"""
    from z3 import BitVec, If

    left, right = BitVec("ite_left", 64), BitVec("ite_right", 64)
    return [If(condition, left, right) == left,
            If(condition, right, left) == right]


def test_ite_condition_collector_only_takes_shared_bitvector_conditions():
    from z3 import BitVec, Bool, If

    from verification.loop_induction import _collect_shared_bv_ite_conditions

    shared, lonely = Bool("shared"), Bool("lonely")
    left, right = BitVec("ite_left", 64), BitVec("ite_right", 64)
    yes, no = Bool("yes"), Bool("no")
    goals = _shared_ite_goals(shared) + [
        If(lonely, left, right) == right,   # 只此一处 ⇒ 解开也没得相消
        If(shared, yes, no) == yes,         # Bool 分支 ⇒ 布尔层自己会分裂
    ]

    assert [str(c) for c in
            _collect_shared_bv_ite_conditions(goals, 4)] == ["shared"]
    # 上限为 0 时一条都不取（提速手段自己不能失控）
    assert _collect_shared_bv_ite_conditions(goals, 0) == []


def test_proved_ite_polarity_is_added_only_when_premises_decide_it():
    """判得出才加，判不出一条都不加——绝不猜极性。"""
    from z3 import Bool, Not

    checker = _make_checker(_X86_LOOP_HEX)
    flag = Bool("expands_probe")
    goals = _shared_ite_goals(flag)

    queries = []
    decided = checker._proved_ite_polarities(
        "probe", [Not(flag)], goals, queries
    )
    assert [str(literal) for literal in decided] == [str(Not(flag))]
    assert queries, "极性判定必须留下查询台账"

    # 前提判不出极性 ⇒ 空手而归（fail-closed）
    assert checker._proved_ite_polarities("probe", [], goals, []) == []


def test_proved_ite_polarity_literals_are_consequences_of_the_premises():
    """返回的每条字面量必须是前提的**逻辑后承**：它是"已证"，不是新假设。

    这条一破，`_prove` 就变成了在一个未被证明的分支上"证明"义务——那是假绿
    方向，与 `common/div_bridge.py` 未证实参恒等就注入等式是同一类错误。
    """
    from z3 import Bool, Not, SolverFor, unsat

    checker = _make_checker(_X86_LOOP_HEX)
    flag = Bool("expands_probe")
    premises = [Not(flag)]
    decided = checker._proved_ite_polarities(
        "probe", premises, _shared_ite_goals(flag), []
    )
    assert decided
    for literal in decided:
        solver = SolverFor("QF_AUFBV")
        solver.set("timeout", 20000)
        solver.add(*premises)
        solver.add(Not(literal))
        assert solver.check() == unsat, f"{literal} 不是前提的后承"
