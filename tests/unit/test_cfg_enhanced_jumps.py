"""测试增强的跳转处理逻辑。"""

import pytest
from evm_ir.cfg_executor import SymbolicExecutor
from evm_ir.models import EVMBlock, EvmOperator
from state.smt_state import SMTState
from evm_ir.cfg_state import GlobalState, WorldState
from evm_ir.cfg_structures import CFGNode
from utils.exceptions import UnsupportedJumpError
from z3 import BitVecVal, If, BitVec


def test_jump_with_constant_target():
    """测试 JUMP 指令，目标是常量（从栈中）。"""
    # 创建测试块
    block = EVMBlock(
        pc=0,
        stack_depth=1,
        min_depth=1,
        max_depth=1024,
        static_gas=1,
        is_jump_target=False,
        is_inner_block=False,
        is_stop=False,
        operations=[
            EvmOperator(kind="JUMP", pc=0, immediate=None, is_static=False)
        ]
    )

    target_block = EVMBlock(
        pc=42,
        stack_depth=0,
        min_depth=0,
        max_depth=1024,
        static_gas=1,
        is_jump_target=True,
        is_inner_block=False,
        is_stop=False,
        operations=[]
    )

    executor = SymbolicExecutor([block, target_block])

    # 创建初始状态，栈顶有常量目标值
    mstate = SMTState()
    mstate.evm_stack = mstate.evm_stack.push(BitVecVal(42, 256))

    node = CFGNode(block=block)

    global_state = GlobalState(
        mstate=mstate,
        world_state=WorldState(),
        node=node
    )

    # 执行跳转处理
    new_states = executor._handle_jump(global_state, mstate, block, BitVecVal(42, 256))

    assert len(new_states) == 1
    assert new_states[0].node.pc == 42


def test_jump_with_if_target():
    """测试 JUMP 指令，目标是 If 表达式。"""
    # 创建测试块
    block = EVMBlock(
        pc=0,
        stack_depth=1,
        min_depth=1,
        max_depth=1024,
        static_gas=1,
        is_jump_target=False,
        is_inner_block=False,
        is_stop=False,
        operations=[
            EvmOperator(kind="JUMP", pc=0, immediate=None, is_static=False)
        ]
    )

    target1 = EVMBlock(
        pc=10,
        stack_depth=0,
        min_depth=0,
        max_depth=1024,
        static_gas=1,
        is_jump_target=True,
        is_inner_block=False,
        is_stop=False,
        operations=[]
    )

    target2 = EVMBlock(
        pc=20,
        stack_depth=0,
        min_depth=0,
        max_depth=1024,
        static_gas=1,
        is_jump_target=True,
        is_inner_block=False,
        is_stop=False,
        operations=[]
    )

    executor = SymbolicExecutor([block, target1, target2])

    # 创建初始状态，栈顶有 If 表达式
    x = BitVec('x', 256)
    if_target = If(x == 0, BitVecVal(10, 256), BitVecVal(20, 256))

    mstate = SMTState()
    mstate.evm_stack = mstate.evm_stack.push(if_target)

    node = CFGNode(block=block)
    global_state = GlobalState(
        mstate=mstate,
        world_state=WorldState(),
        node=node
    )

    # 执行跳转处理
    new_states = executor._handle_jump(global_state, mstate, block, if_target)

    # 应该创建两个分支
    assert len(new_states) == 2
    target_pcs = {s.node.pc for s in new_states}
    assert target_pcs == {10, 20}


def test_jump_with_dynamic_target():
    """测试 JUMP 指令，目标是动态值（应抛出异常）。"""
    block = EVMBlock(
        pc=0,
        stack_depth=1,
        min_depth=1,
        max_depth=1024,
        static_gas=1,
        is_jump_target=False,
        is_inner_block=False,
        is_stop=False,
        operations=[
            EvmOperator(kind="JUMP", pc=0, immediate=None, is_static=False)
        ]
    )

    executor = SymbolicExecutor([block])

    # 创建初始状态，栈顶有符号值
    x = BitVec('x', 256)
    mstate = SMTState()
    mstate.evm_stack = mstate.evm_stack.push(x)

    node = CFGNode(block=block)
    global_state = GlobalState(
        mstate=mstate,
        world_state=WorldState(),
        node=node
    )

    # 应该抛出异常
    with pytest.raises(UnsupportedJumpError) as exc_info:
        executor._handle_jump(global_state, mstate, block, x)

    assert exc_info.value.jump_type == "dynamic_jump"


def test_jumpi_with_constant_target():
    """测试 JUMPI 指令，目标是常量。"""
    block = EVMBlock(
        pc=0,
        stack_depth=2,
        min_depth=2,
        max_depth=1024,
        static_gas=1,
        is_jump_target=False,
        is_inner_block=False,
        is_stop=False,
        operations=[
            EvmOperator(kind="JUMPI", pc=0, immediate=None, is_static=False)
        ]
    )

    target_block = EVMBlock(
        pc=42,
        stack_depth=0,
        min_depth=0,
        max_depth=1024,
        static_gas=1,
        is_jump_target=True,
        is_inner_block=False,
        is_stop=False,
        operations=[]
    )

    fallthrough_block = EVMBlock(
        pc=5,
        stack_depth=0,
        min_depth=0,
        max_depth=1024,
        static_gas=1,
        is_jump_target=False,
        is_inner_block=False,
        is_stop=False,
        operations=[]
    )

    executor = SymbolicExecutor([block, fallthrough_block, target_block])

    # 条件为真，目标为 42
    mstate = SMTState()
    mstate.evm_stack = mstate.evm_stack.push(BitVecVal(42, 256))  # 目标
    mstate.evm_stack = mstate.evm_stack.push(BitVecVal(1, 256))   # 条件

    node = CFGNode(block=block)
    global_state = GlobalState(
        mstate=mstate,
        world_state=WorldState(),
        node=node
    )

    # 执行跳转处理
    new_states = executor._handle_jumpi(
        global_state, mstate, block,
        condition_value=BitVecVal(1, 256),
        target_value=BitVecVal(42, 256)
    )

    # 应该创建两个分支：跳转和 fallthrough
    assert len(new_states) == 2
    target_pcs = {s.node.pc for s in new_states}
    assert target_pcs == {42, 5}


def test_static_jump_with_empty_stack():
    """测试静态 JUMP 指令，栈为空的情况。

    验证静态跳转（is_static=True 且有 immediate）不会尝试从栈中弹出目标值。
    """
    block = EVMBlock(
        pc=0,
        stack_depth=0,
        min_depth=0,
        max_depth=1024,
        static_gas=1,
        is_jump_target=False,
        is_inner_block=False,
        is_stop=False,
        operations=[
            EvmOperator(kind="JUMP", pc=0, immediate=42, is_static=True)
        ]
    )

    target_block = EVMBlock(
        pc=42,
        stack_depth=0,
        min_depth=0,
        max_depth=1024,
        static_gas=1,
        is_jump_target=True,
        is_inner_block=False,
        is_stop=False,
        operations=[]
    )

    executor = SymbolicExecutor([block, target_block])

    # 栈为空（静态跳转不需要从栈中获取目标）
    mstate = SMTState()

    node = CFGNode(block=block)
    global_state = GlobalState(
        mstate=mstate,
        world_state=WorldState(),
        node=node
    )

    # 应该正确处理静态跳转，不会因为栈空而失败
    new_states = executor.execute_state(global_state)

    assert len(new_states) == 1
    assert new_states[0].node.pc == 42


def test_jump_with_if_creates_conditional_jump_edge():
    """测试 JUMP 从 If 表达式解析时使用 IF_THEN/IF_ELSE 边类型。"""
    # 创建测试块
    block = EVMBlock(
        pc=0,
        stack_depth=1,
        min_depth=1,
        max_depth=1024,
        static_gas=1,
        is_jump_target=False,
        is_inner_block=False,
        is_stop=False,
        operations=[
            EvmOperator(kind="JUMP", pc=0, immediate=None, is_static=False)
        ]
    )

    target1 = EVMBlock(pc=10, stack_depth=0, min_depth=0, max_depth=1024,
                      static_gas=1, is_jump_target=True, is_inner_block=False,
                      is_stop=False, operations=[])

    target2 = EVMBlock(pc=20, stack_depth=0, min_depth=0, max_depth=1024,
                      static_gas=1, is_jump_target=True, is_inner_block=False,
                      is_stop=False, operations=[])

    executor = SymbolicExecutor([block, target1, target2])

    # 创建 If 表达式
    x = BitVec('x', 256)
    if_target = If(x == 0, BitVecVal(10, 256), BitVecVal(20, 256))

    mstate = SMTState()
    mstate.evm_stack = mstate.evm_stack.push(if_target)

    node = CFGNode(block=block)
    global_state = GlobalState(
        mstate=mstate,
        world_state=WorldState(),
        node=node
    )

    # 直接调用 _handle_jump 方法处理跳转
    new_states = executor._handle_jump(global_state, mstate, block, if_target)

    # 验证生成了两个目标状态
    assert len(new_states) == 2

    # 手动调用 manage_cfg 来添加边
    executor.manage_cfg("JUMP", new_states, from_pc=0, source_op=block.operations[-1])

    # 验证边类型为 IF_THEN/IF_ELSE
    from evm_ir.cfg_structures import EdgeType
    jump_edges = [e for e in executor.cfg.edges if e.node_from == 0]
    assert len(jump_edges) == 2
    
    # 应该有一条 IF_THEN 边和一条 IF_ELSE 边
    if_then_edges = [e for e in jump_edges if e.edge_type == EdgeType.IF_THEN]
    if_else_edges = [e for e in jump_edges if e.edge_type == EdgeType.IF_ELSE]
    assert len(if_then_edges) == 1, "Should have one IF_THEN edge"
    assert len(if_else_edges) == 1, "Should have one IF_ELSE edge"
    
    # 验证目标 PC
    assert if_then_edges[0].node_to == 10, "IF_THEN should target PC=10"
    assert if_else_edges[0].node_to == 20, "IF_ELSE should target PC=20"


def test_jumpi_multi_target_edge_types():
    """测试 JUMPI 从 If 表达式解析多目标时的边类型。"""
    block = EVMBlock(
        pc=0,
        stack_depth=2,
        min_depth=2,
        max_depth=1024,
        static_gas=1,
        is_jump_target=False,
        is_inner_block=False,
        is_stop=False,
        operations=[
            EvmOperator(kind="JUMPI", pc=0, immediate=None, is_static=False)
        ]
    )

    # JUMPI 跳转到两个目标（从 If 解析）
    target1 = EVMBlock(pc=10, stack_depth=0, min_depth=0, max_depth=1024,
                      static_gas=1, is_jump_target=True, is_inner_block=False,
                      is_stop=False, operations=[])

    target2 = EVMBlock(pc=20, stack_depth=0, min_depth=0, max_depth=1024,
                      static_gas=1, is_jump_target=True, is_inner_block=False,
                      is_stop=False, operations=[])

    # Fallthrough 目标
    fallthrough = EVMBlock(pc=5, stack_depth=0, min_depth=0, max_depth=1024,
                          static_gas=1, is_jump_target=False, is_inner_block=False,
                          is_stop=False, operations=[])

    executor = SymbolicExecutor([block, fallthrough, target1, target2])

    # 创建 If 表达式作为跳转目标
    x = BitVec('x', 256)
    if_target = If(x < 100, BitVecVal(10, 256), BitVecVal(20, 256))

    mstate = SMTState()
    mstate.evm_stack = mstate.evm_stack.push(if_target)  # 目标
    mstate.evm_stack = mstate.evm_stack.push(BitVecVal(1, 256))  # 条件（非零）

    node = CFGNode(block=block)
    global_state = GlobalState(
        mstate=mstate,
        world_state=WorldState(),
        node=node
    )

    # 直接调用 _handle_jumpi 方法处理跳转
    new_states = executor._handle_jumpi(
        global_state, mstate, block,
        condition_value=BitVecVal(1, 256),
        target_value=if_target
    )

    # 验证生成了三个目标状态（两个跳转目标 + fallthrough）
    assert len(new_states) == 3

    # 手动调用 manage_cfg 来添加边
    executor.manage_cfg("JUMPI", new_states, from_pc=0, source_op=block.operations[-1])

    # 验证边类型
    from evm_ir.cfg_structures import EdgeType
    jumpi_edges = [e for e in executor.cfg.edges if e.node_from == 0]
    assert len(jumpi_edges) == 3

    # 跳转分支应为 IF_THEN/IF_ELSE（因为目标是 If 表达式）
    if_then_edges = [e for e in jumpi_edges if e.edge_type == EdgeType.IF_THEN]
    if_else_edges = [e for e in jumpi_edges if e.edge_type == EdgeType.IF_ELSE]
    assert len(if_then_edges) == 1, "Should have one IF_THEN edge"
    assert len(if_else_edges) == 1, "Should have one IF_ELSE edge"
    
    # 验证跳转目标
    assert if_then_edges[0].node_to == 10, "IF_THEN should target PC=10"
    assert if_else_edges[0].node_to == 20, "IF_ELSE should target PC=20"

    # Fallthrough 分支应为 CONDITIONAL_FALSE
    ft_edges = [e for e in jumpi_edges if e.edge_type == EdgeType.CONDITIONAL_FALSE]
    assert len(ft_edges) == 1
    assert ft_edges[0].node_to == 5
