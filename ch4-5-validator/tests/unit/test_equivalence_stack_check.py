#!/usr/bin/env python3
"""EquivalenceChecker 固定栈槽检查的回归测试。"""

from z3 import BitVecVal, Select, Store

from state.evm_stack_state import EVMStackState
from state.smt_state import SMTState
from state.x86_state import X86MemoryState
from verification.memory_mapping import StackMemoryMapper
from verification.equivalence_checker import EquivalenceChecker
from x86_64.models import Register


def _make_equivalence_checker() -> EquivalenceChecker:
    return EquivalenceChecker(timeout_ms=10000, verbose=False)


def _rebase_fixed_stack_window(state: SMTState, stack_base_value: int) -> tuple[SMTState, SMTState]:
    """将固定槽位窗口重建到一个与旧 pin 冲突的新 host layout。"""
    rebased_initial = state.copy()
    rebased_initial.stack_base = BitVecVal(stack_base_value, 64)

    stack_values = [
        Select(state.evm_stack.Stack, 0),
        Select(state.evm_stack.Stack, 1),
    ]

    rebased_x86 = state.copy()
    rebased_x86.x86_registers.set_register(Register.R13, BitVecVal(0x00410000, 64))
    rebased_x86.x86_registers.set_register(Register.R14, BitVecVal(stack_base_value, 64))
    rebased_x86.x86_registers.set_register(Register.R15, BitVecVal(0x00610000, 64))
    rebased_x86.x86_memory = StackMemoryMapper.initialize_x86_memory_from_stack(
        X86MemoryState(),
        stack_values,
        base=rebased_initial.stack_base,
    )

    return rebased_initial, rebased_x86


def test_stack_check_succeeds_without_concrete_host_layout_pins():
    """stack_check 不应依赖旧实现里那组具体 host 地址常量。"""
    equivalence_checker = _make_equivalence_checker()
    base_state = SMTState.create_initial_state(2)
    initial_state, x86_state = _rebase_fixed_stack_window(base_state, 0x00430000)

    verified, msg = equivalence_checker.check_stack_equivalence(
        base_state,
        x86_state,
        initial_state,
        n_elements=2,
    )

    assert verified, msg


def test_stack_check_reports_real_counterexample_instead_of_vacuous_pass():
    """旧实现会因硬编码 pin 自相矛盾而 vacuous pass；新实现必须报真实差异。"""
    equivalence_checker = _make_equivalence_checker()
    base_state = SMTState.create_initial_state(2)
    initial_state, x86_state = _rebase_fixed_stack_window(base_state, 0x00430000)

    evm_state = base_state.copy()
    evm_state.evm_stack = EVMStackState(
        stack_array=Store(evm_state.evm_stack.Stack, 0, BitVecVal(0xAA, 256)),
        sp=evm_state.evm_stack.SP,
    )

    verified, msg = equivalence_checker.check_stack_equivalence(
        evm_state,
        x86_state,
        initial_state,
        n_elements=1,
    )

    assert not verified
    assert "Fixed stack slot 0 differs" in msg
