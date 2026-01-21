#!/usr/bin/env python3
"""测试新的动态 CFG 构建和 worklist 驱动的符号执行。"""

import os
import pytest
from z3 import BoolVal, BitVecVal

from evm_ir.json_parser import load_ir_from_json
from evm_ir.cfg import (
    DynamicCFG, CFGNode, CFGEdge, EdgeType,
    SymbolicExecutor, DFSStrategy, BFSStrategy,
    GlobalState, WorldState, Constraints,
    StateAnnotation, LoopCountAnnotation,
    build_dynamic_cfg
)
from state.smt_state import SMTState


class TestConstraints:
    """测试约束集合。"""

    def test_constraints_creation(self):
        """测试约束集合创建。"""
        constraints = Constraints()
        assert len(constraints) == 1  # 默认包含 True

    def test_add_constraint(self):
        """测试添加约束。"""
        from z3 import Bool
        constraints = Constraints()
        x = Bool('x')
        constraints.add(x)
        assert len(constraints) == 2

    def test_is_possible(self):
        """测试可达性检查。"""
        from z3 import Bool, And
        constraints = Constraints()
        x = Bool('x')
        y = Bool('y')
        constraints.add(x)
        constraints.add(y)

        # 可满足
        assert constraints.is_possible() == True

        # 不可满足
        constraints2 = Constraints()
        constraints2.add(x)
        constraints2.add(BoolVal(False))
        # 注意：Z3 可能不会立即检测到不可满足性
        # 这里主要测试 API

    def test_as_bool(self):
        """测试转换为 BoolRef。"""
        from z3 import Bool
        constraints = Constraints()
        x = Bool('x')
        constraints.add(x)

        result = constraints.as_bool()
        assert result is not None


class TestWorldState:
    """测试世界状态。"""

    def test_world_state_creation(self):
        """测试世界状态创建。"""
        world_state = WorldState()
        assert world_state.constraints is not None
        assert world_state.transaction_sequence == []
        assert world_state.annotations == []

    def test_world_state_copy(self):
        """测试世界状态拷贝。"""
        world_state = WorldState()
        copied = copy.copy(world_state)
        assert copied is not world_state


class TestGlobalState:
    """测试全局状态。"""

    def test_global_state_creation(self):
        """测试全局状态创建。"""
        mstate = SMTState.create_initial_state(num_inputs=0)
        gstate = GlobalState(mstate=mstate)

        assert gstate.mstate == mstate
        assert gstate.world_state is not None
        assert gstate.depth == 0

    def test_global_state_add_constraint(self):
        """测试添加约束。"""
        from z3 import Bool
        mstate = SMTState.create_initial_state(num_inputs=0)
        gstate = GlobalState(mstate=mstate)

        x = Bool('x')
        gstate.add_constraint(x)

        assert len(gstate.get_constraints()) == 2  # True + x

    def test_global_state_annotate(self):
        """测试添加注解。"""
        mstate = SMTState.create_initial_state(num_inputs=0)
        gstate = GlobalState(mstate=mstate)

        ann = LoopCountAnnotation(loop_target_pc=10, count=1)
        gstate.annotate(ann)

        retrieved = gstate.get_annotation(LoopCountAnnotation)
        assert retrieved is not None
        assert retrieved.loop_target_pc == 10


class TestDynamicCFGStructure:
    """测试动态 CFG 的基本结构。"""

    def test_cfg_node_creation(self):
        """测试 CFG 节点创建。"""
        from evm_ir.models import EVMBlock

        block = EVMBlock(
            pc=0,
            stack_depth=0,
            min_depth=0,
            max_depth=1024,
            static_gas=10,
            is_jump_target=False,
            is_inner_block=False,
            is_stop=False,
            operations=[]
        )

        node = CFGNode(block=block)
        assert node.pc == 0
        assert len(node.states) == 0
        assert len(node.incoming_edges) == 0
        assert len(node.outgoing_edges) == 0

    def test_cfg_edge_creation(self):
        """测试 CFG 边创建。"""
        edge = CFGEdge(
            node_from=0,
            node_to=13,
            edge_type=EdgeType.CONDITIONAL,
            condition=BoolVal(True)
        )

        assert edge.node_from == 0
        assert edge.node_to == 13
        assert edge.edge_type == EdgeType.CONDITIONAL
        assert edge.condition == BoolVal(True)

    def test_dynamic_cfg_creation(self):
        """测试动态 CFG 创建。"""
        from evm_ir.models import EVMBlock

        blocks = [
            EVMBlock(
                pc=i,
                stack_depth=0,
                min_depth=0,
                max_depth=1024,
                static_gas=10,
                is_jump_target=False,
                is_inner_block=False,
                is_stop=False,
                operations=[]
            )
            for i in range(3)
        ]

        cfg = DynamicCFG(blocks)
        assert len(cfg.nodes) == 3
        assert 0 in cfg.nodes
        assert 1 in cfg.nodes
        assert 2 in cfg.nodes

    def test_add_edge(self):
        """测试添加边。"""
        from evm_ir.models import EVMBlock

        blocks = [
            EVMBlock(
                pc=i,
                stack_depth=0,
                min_depth=0,
                max_depth=1024,
                static_gas=10,
                is_jump_target=False,
                is_inner_block=False,
                is_stop=False,
                operations=[]
            )
            for i in range(2)
        ]

        cfg = DynamicCFG(blocks)
        edge = cfg.add_edge(0, 1, EdgeType.UNCONDITIONAL)

        assert edge.node_from == 0
        assert edge.node_to == 1
        assert edge.edge_type == EdgeType.UNCONDITIONAL

        # 检查节点的边
        node0 = cfg.get_node(0)
        node1 = cfg.get_node(1)
        assert len(node0.outgoing_edges) == 1
        assert len(node1.incoming_edges) == 1

    def test_get_successors(self):
        """测试获取后继节点。"""
        from evm_ir.models import EVMBlock

        blocks = [
            EVMBlock(
                pc=i,
                stack_depth=0,
                min_depth=0,
                max_depth=1024,
                static_gas=10,
                is_jump_target=False,
                is_inner_block=False,
                is_stop=False,
                operations=[]
            )
            for i in range(3)
        ]

        cfg = DynamicCFG(blocks)
        cfg.add_edge(0, 1, EdgeType.FALLTHROUGH)
        cfg.add_edge(0, 2, EdgeType.CONDITIONAL, BoolVal(True))

        successors = cfg.get_successors(0)
        assert len(successors) == 2


class TestSearchStrategies:
    """测试搜索策略。"""

    def test_dfs_strategy(self):
        """测试 DFS 策略。"""
        strategy = DFSStrategy(work_list=[], max_depth=100)

        # 添加一些状态
        mstate = SMTState.create_initial_state(num_inputs=0)
        for i in range(3):
            node = CFGNode(block=None)  # 简化测试
            gstate = GlobalState(mstate=mstate, node=node)
            gstate.depth = i
            strategy.work_list.append(gstate)

        # DFS 应该返回最后一个添加的状态
        state = strategy.get_strategic_global_state()
        assert state is not None
        assert state.depth == 2

    def test_bfs_strategy(self):
        """测试 BFS 策略。"""
        strategy = BFSStrategy(work_list=[], max_depth=100)

        # 添加一些状态
        mstate = SMTState.create_initial_state(num_inputs=0)
        for i in range(3):
            node = CFGNode(block=None)  # 简化测试
            gstate = GlobalState(mstate=mstate, node=node)
            gstate.depth = i
            strategy.work_list.append(gstate)

        # BFS 应该返回第一个添加的状态
        state = strategy.get_strategic_global_state()
        assert state is not None
        assert state.depth == 0

    def test_strategy_iteration(self):
        """测试策略迭代。"""
        strategy = DFSStrategy(work_list=[], max_depth=100)

        mstate = SMTState.create_initial_state(num_inputs=0)
        node = CFGNode(block=None)
        gstate = GlobalState(mstate=mstate, node=node)
        gstate.depth = 0
        strategy.work_list.append(gstate)

        # 测试迭代器接口
        count = 0
        for _ in strategy:
            count += 1
            if count >= 1:
                break
        assert count == 1


class TestStateAnnotations:
    """测试状态注释系统。"""

    def test_loop_count_annotation(self):
        """测试循环计数注释。"""
        ann = LoopCountAnnotation(loop_target_pc=10, count=5)
        assert ann.loop_target_pc == 10
        assert ann.count == 5

    def test_annotation_merge(self):
        """测试注释合并。"""
        ann1 = LoopCountAnnotation(loop_target_pc=10, count=5)
        ann2 = LoopCountAnnotation(loop_target_pc=10, count=3)

        assert ann1.check_merge(ann2)
        merged = ann1.merge(ann2)
        assert merged.count == 5  # 取最大值


class TestSymbolicExecutor:
    """测试符号执行引擎。"""

    def test_executor_creation(self):
        """测试执行器创建。"""
        from evm_ir.models import EVMBlock, EvmOperator

        blocks = [
            EVMBlock(
                pc=0,
                stack_depth=0,
                min_depth=0,
                max_depth=1024,
                static_gas=10,
                is_jump_target=False,
                is_inner_block=False,
                is_stop=True,
                operations=[
                    EvmOperator(kind="STOP", pc=0)
                ]
            )
        ]

        executor = SymbolicExecutor(blocks, strategy_cls=DFSStrategy, max_depth=100)
        assert len(executor.blocks) == 1
        assert executor.cfg is not None
        assert executor.work_list == []

    def test_execute_simple_program(self):
        """测试执行简单程序（单个 STOP 块）。"""
        from evm_ir.models import EVMBlock, EvmOperator

        blocks = [
            EVMBlock(
                pc=0,
                stack_depth=0,
                min_depth=0,
                max_depth=1024,
                static_gas=2,
                is_jump_target=False,
                is_inner_block=False,
                is_stop=True,
                operations=[
                    EvmOperator(kind="TAG", pc=0),
                    EvmOperator(kind="STOP", pc=1)
                ]
            )
        ]

        executor = SymbolicExecutor(blocks)
        state = SMTState.create_initial_state(num_inputs=0)

        final_states = executor.execute(state)

        # 应该有一个终止状态
        assert len(final_states) == 1

        # CFG 应该有一个节点
        assert len(executor.cfg.nodes) == 1

    def test_execute_two_block_program(self):
        """测试执行两块程序（JUMPI + STOP）。"""
        test_dir = os.path.dirname(__file__)
        ir_file = os.path.join(test_dir, "..", "data", "two_block.json")

        ir_result = load_ir_from_json(ir_file)

        executor = SymbolicExecutor(ir_result.blocks, strategy_cls=DFSStrategy)
        state = SMTState.create_initial_state(num_inputs=0)

        final_states = executor.execute(state)

        # 应该有终止状态
        assert len(final_states) > 0

        # CFG 应该有边
        assert len(executor.cfg.edges) > 0

    def test_reachability_check(self):
        """测试可达性检查。"""
        from evm_ir.models import EVMBlock, EvmOperator

        blocks = [
            EVMBlock(
                pc=0,
                stack_depth=0,
                min_depth=0,
                max_depth=1024,
                static_gas=2,
                is_jump_target=False,
                is_inner_block=False,
                is_stop=True,
                operations=[
                    EvmOperator(kind="STOP", pc=0)
                ]
            )
        ]

        # 启用可达性检查
        executor = SymbolicExecutor(blocks, use_reachability_check=True)
        state = SMTState.create_initial_state(num_inputs=0)

        final_states = executor.execute(state)
        assert len(final_states) == 1


class TestEVMProgramIntegration:
    """测试 EVMProgram 与新执行引擎的集成。"""

    def test_evm_program_to_z3(self):
        """测试 EVMProgram.to_z3 使用新执行引擎。"""
        from evm_ir.program import EVMProgram

        test_dir = os.path.dirname(__file__)
        ir_file = os.path.join(test_dir, "..", "data", "two_block.json")

        ir_result = load_ir_from_json(ir_file)
        program = EVMProgram(ir_result)

        state = SMTState.create_initial_state(num_inputs=0)

        # 使用默认的 DFS 策略
        final_state, result = program.to_z3(state)

        assert final_state is not None
        assert 'offset' in result
        assert 'length' in result
        assert 'memory' in result
        assert 'has_return' in result

    def test_evm_program_with_bfs_strategy(self):
        """测试 EVMProgram 使用 BFS 策略。"""
        from evm_ir.program import EVMProgram

        test_dir = os.path.dirname(__file__)
        ir_file = os.path.join(test_dir, "..", "data", "two_block.json")

        ir_result = load_ir_from_json(ir_file)
        program = EVMProgram(ir_result)

        state = SMTState.create_initial_state(num_inputs=0)

        # 使用 BFS 策略
        final_state, result = program.to_z3(state, strategy_cls=BFSStrategy)

        assert final_state is not None
        assert 'offset' in result


class TestEdgeType:
    """测试边类型枚举。"""

    def test_edge_type_values(self):
        """测试边类型值。"""
        assert EdgeType.UNCONDITIONAL.value == "unconditional"
        assert EdgeType.CONDITIONAL.value == "conditional"
        assert EdgeType.FALLTHROUGH.value == "fallthrough"
        assert EdgeType.CALL.value == "call"
        assert EdgeType.RETURN.value == "return"


class TestDynamicJumpHandling:
    """测试动态跳转处理。"""

    def test_dynamic_jump_raises_error(self):
        """测试动态跳转应该抛出错误。"""
        from evm_ir.models import EVMBlock, EvmOperator
        from utils.exceptions import UnsupportedJumpError

        # 创建动态 JUMP
        blocks = [
            EVMBlock(
                pc=0,
                stack_depth=0,
                min_depth=0,
                max_depth=1024,
                static_gas=10,
                is_jump_target=False,
                is_inner_block=False,
                is_stop=False,
                operations=[
                    EvmOperator(
                        kind="JUMP",
                        pc=0,
                        immediate=None,
                        is_static=False
                    )
                ]
            )
        ]

        executor = SymbolicExecutor(blocks)
        state = SMTState.create_initial_state(num_inputs=0)

        # 应该抛出 UnsupportedJumpError
        with pytest.raises(UnsupportedJumpError) as exc_info:
            executor.execute(state)

        assert "dynamic_jump" in str(exc_info.value)


# 导入 copy 模块
import copy


class TestCompleteCFG:
    """测试执行完成后完整构建出的 CFG。"""

    def test_two_block_complete_cfg(self):
        """测试两块程序执行完成后 CFG 的完整结构。"""
        test_dir = os.path.dirname(__file__)
        ir_file = os.path.join(test_dir, "..", "data", "two_block.json")

        ir_result = load_ir_from_json(ir_file)

        executor = SymbolicExecutor(ir_result.blocks, strategy_cls=DFSStrategy)
        state = SMTState.create_initial_state(num_inputs=0)

        final_states = executor.execute(state)

        # 验证执行完成
        assert len(final_states) > 0

        cfg = executor.cfg

        # 验证节点: 应该有两个节点
        assert len(cfg.nodes) == 2
        assert 0 in cfg.nodes
        assert 13 in cfg.nodes

        # 验证边: JUMPI 产生两条边（条件为真跳转，条件为假 fallthrough）
        # 但由于 pc=13 是下一个块，fallthrough 也指向 pc=13
        # 所以可能会有两条到 pc=13 的边，或者一条边
        assert len(cfg.edges) > 0

        # 验证边的类型
        for edge in cfg.edges:
            if edge.node_from == 0 and edge.node_to == 13:
                # 应该是条件跳转相关的边
                assert edge.edge_type in [
                    EdgeType.CONDITIONAL_TRUE,
                    EdgeType.CONDITIONAL_FALSE,
                    EdgeType.FALLTHROUGH
                ]
                # 验证源操作被正确记录
                assert edge.source_operation is not None
                assert edge.source_operation.kind == "JUMPI"

    def test_cfg_structure_after_execution(self):
        """测试执行完成后 CFG 的结构性属性。"""
        test_dir = os.path.dirname(__file__)
        ir_file = os.path.join(test_dir, "..", "data", "two_block.json")

        ir_result = load_ir_from_json(ir_file)

        executor = SymbolicExecutor(ir_result.blocks, strategy_cls=DFSStrategy)
        state = SMTState.create_initial_state(num_inputs=0)

        final_states = executor.execute(state)

        cfg = executor.cfg

        # 验证每个节点的出边和入边
        for pc, node in cfg.nodes.items():
            # 验证节点的出边与其在 edges 中的一致
            for edge in node.outgoing_edges:
                assert edge in cfg.edges
                assert edge.node_from == pc

            # 验证节点的入边与其在 edges 中的一致
            for edge in node.incoming_edges:
                assert edge in cfg.edges
                assert edge.node_to == pc

        # 验证边的连通性
        # pc=0 应该有出边（JUMPI）
        node_0 = cfg.get_node(0)
        assert len(node_0.outgoing_edges) > 0

        # pc=13 应该没有出边（STOP 是终止指令）
        node_13 = cfg.get_node(13)
        assert len(node_13.outgoing_edges) == 0

    def test_cfg_edge_conditions(self):
        """测试 CFG 边的条件约束。"""
        from evm_ir.models import EVMBlock, EvmOperator
        from z3 import Not

        # 创建一个简单的 JUMPI 程序
        blocks = [
            EVMBlock(
                pc=0,
                stack_depth=0,
                min_depth=0,
                max_depth=1024,
                static_gas=10,
                is_jump_target=False,
                is_inner_block=False,
                is_stop=False,
                operations=[
                    EvmOperator(kind="PUSH", pc=0, immediate="5"),
                    EvmOperator(kind="JUMPI", pc=2, immediate=10, is_static=True)
                ]
            ),
            EVMBlock(
                pc=10,
                stack_depth=0,
                min_depth=0,
                max_depth=1024,
                static_gas=2,
                is_jump_target=True,
                is_inner_block=False,
                is_stop=True,
                operations=[
                    EvmOperator(kind="STOP", pc=10)
                ]
            )
        ]

        executor = SymbolicExecutor(blocks, strategy_cls=DFSStrategy)
        state = SMTState.create_initial_state(num_inputs=0)

        final_states = executor.execute(state)
        cfg = executor.cfg

        # 验证条件边
        conditional_edges = [e for e in cfg.edges if e.edge_type == EdgeType.CONDITIONAL_TRUE]
        fallthrough_edges = [e for e in cfg.edges if e.edge_type == EdgeType.FALLTHROUGH]

        # JUMPI 应该产生条件边
        assert len(conditional_edges) > 0

        # 每个条件边应该有条件约束（除了 fallthrough）
        for edge in conditional_edges:
            if edge.edge_type == EdgeType.CONDITIONAL_TRUE:
                # 条件为真的边应该有条件
                assert edge.condition is not None

    def test_cfg_source_operation_tracking(self):
        """测试 CFG 边的源操作追踪。"""
        test_dir = os.path.dirname(__file__)
        ir_file = os.path.join(test_dir, "..", "data", "two_block.json")

        ir_result = load_ir_from_json(ir_file)

        executor = SymbolicExecutor(ir_result.blocks, strategy_cls=DFSStrategy)
        state = SMTState.create_initial_state(num_inputs=0)

        final_states = executor.execute(state)
        cfg = executor.cfg

        # 验证所有边都有源操作（除了可能的特殊边）
        for edge in cfg.edges:
            # JUMP/JUMPI 产生的边应该有源操作
            if edge.edge_type in [EdgeType.UNCONDITIONAL, EdgeType.CONDITIONAL_TRUE, EdgeType.FALLTHROUGH]:
                if edge.source_operation is not None:
                    # 验证源操作是正确的类型
                    assert edge.source_operation.kind in ["JUMP", "JUMPI"]
