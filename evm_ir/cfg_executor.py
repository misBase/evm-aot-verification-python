"""
符号执行引擎（参考 mythril 的 LaserEVM）。

定义 SymbolicExecutor 类，实现 worklist 驱动的符号执行。
"""

from typing import List, Dict, Optional, Tuple
from z3 import BitVecVal, Not

from .models import EVMBlock
from .cfg_structures import DynamicCFG, EdgeType
from .cfg_state import GlobalState
from .cfg_strategies import DFSStrategy
from state.smt_state import SMTState


class SymbolicExecutor:
    """基于 worklist 的符号执行引擎。

    完全参考 mythril 的 LaserEVM 设计：
    - work_list 管理待执行状态
    - 动态构建 CFG
    - 策略模式控制搜索顺序
    - 可达性检查剪枝不可达状态
    """

    def __init__(self,
                 blocks: List[EVMBlock],
                 strategy_cls: type = DFSStrategy,
                 max_depth: int = 100,
                 use_reachability_check: bool = True):
        """初始化符号执行引擎。

        Args:
            blocks: 所有 EVM 块列表
            strategy_cls: 搜索策略类
            max_depth: 最大执行深度
            use_reachability_check: 是否使用可达性检查
        """
        self.blocks = blocks
        self.blocks_by_pc: Dict[int, EVMBlock] = {block.pc: block for block in blocks}
        self.max_depth = max_depth
        self.use_reachability_check = use_reachability_check

        # 创建动态 CFG
        self.cfg = DynamicCFG(blocks)

        # work_list：待执行的全局状态列表
        self.work_list: List[GlobalState] = []

        # 创建搜索策略
        self.strategy = strategy_cls(self.work_list, max_depth)

        # 统计信息
        self.total_states = 0
        self.pruned_states = 0

        # 终止状态列表
        self.final_states: List[GlobalState] = []

    def manage_cfg(self, opcode: str, new_states: List[GlobalState]) -> None:
        """管理 CFG 构建。

        在执行过程中动态添加边。

        Args:
            opcode: 操作码（JUMP/JUMPI 等）
            new_states: 新生成的状态
        """
        if not new_states:
            return

        # 获取当前节点的 PC
        current_pc = new_states[0].node.pc if new_states[0].node else None
        if current_pc is None:
            return

        if opcode == "JUMP":
            # 无条件跳转：添加单条边
            if len(new_states) == 1:
                target_pc = new_states[0].node.pc
                self.cfg.add_edge(current_pc, target_pc, EdgeType.UNCONDITIONAL)

        elif opcode == "JUMPI":
            # 条件跳转：添加两条边（跳转和顺序执行）
            for state in new_states:
                if state.node:
                    target_pc = state.node.pc
                    # 从状态中获取条件
                    condition = self._extract_jumpi_condition(state)
                    self.cfg.add_edge(current_pc, target_pc, EdgeType.CONDITIONAL, condition)

    def _extract_jumpi_condition(self, state: GlobalState):
        """从状态中提取 JUMPI 条件。

        Args:
            state: 全局状态

        Returns:
            条件 BoolRef 或 None
        """
        # 从世界状态的约束中获取最后的条件
        constraints = state.get_constraints()
        if len(constraints) > 0:
            return list(constraints)[-1]
        return None

    def execute(self, initial_state: SMTState, entry_pc: Optional[int] = None) -> List[GlobalState]:
        """执行符号执行。

        Args:
            initial_state: 初始机器状态
            entry_pc: 入口块 PC（默认为第一个块）

        Returns:
            所有终止状态列表
        """
        # 确定入口点
        if entry_pc is None:
            if not self.blocks:
                raise ValueError("No blocks to execute")
            entry_pc = self.blocks[0].pc

        entry_block = self.blocks_by_pc.get(entry_pc)
        if entry_block is None:
            raise ValueError(f"Entry block not found: pc={entry_pc}")

        # 创建初始全局状态
        entry_node = self.cfg.get_or_create_node(entry_pc)
        initial_global_state = GlobalState(
            mstate=initial_state,
            node=entry_node
        )
        initial_global_state.depth = 0

        # 添加到 work_list
        self.work_list.append(initial_global_state)

        # 主执行循环
        for global_state in self.strategy:
            # 执行单个状态
            new_states = self.execute_state(global_state)

            if new_states:
                # 可达性检查和剪枝
                if self.use_reachability_check and len(new_states) > 1:
                    old_count = len(new_states)
                    new_states = [
                        state for state in new_states
                        if state.get_constraints().is_possible()
                    ]
                    pruned = old_count - len(new_states)
                    self.pruned_states += pruned

                # 更新 CFG
                last_op = self._get_last_operation(global_state)
                if last_op:
                    opcode = last_op.kind.upper()
                    self.manage_cfg(opcode, new_states)

                # 添加新状态到 work_list
                self.work_list.extend(new_states)
                self.total_states += len(new_states)

            # 如果是终止状态，保存
            if self._is_terminal_state(global_state):
                self.final_states.append(global_state)

        return self.final_states

    def execute_state(self, global_state: GlobalState) -> List[GlobalState]:
        """执行单个全局状态。

        Args:
            global_state: 要执行的全局状态

        Returns:
            新生成的全局状态列表
        """
        node = global_state.node
        if node is None:
            return []

        block = node.block
        mstate = global_state.mstate

        # 执行块中的所有操作
        new_mstate = mstate.copy()

        for op in block.operations:
            kind = op.kind.upper()

            # 跳过标记操作
            if kind in ["TAG", "BLOCKEND"]:
                continue

            # 检查终止指令
            if kind in ["STOP", "RETURN", "REVERT", "SELFDESTRUCT"]:
                # 返回空列表（无后继状态）
                return []

            # 执行操作
            new_mstate = op.to_z3(new_mstate)

        # 获取最后一个操作来确定控制流
        if not block.operations:
            # 空块，顺序执行到下一个块
            return self._handle_fallthrough(global_state, new_mstate, block)

        last_op = block.operations[-1]
        last_kind = last_op.kind.upper()

        if last_kind == "JUMP":
            return self._handle_jump(global_state, new_mstate, block)
        elif last_kind == "JUMPI":
            return self._handle_jumpi(global_state, new_mstate, block)
        else:
            # 顺序执行到下一个块
            return self._handle_fallthrough(global_state, new_mstate, block)

    def _handle_jump(self, global_state: GlobalState, mstate: SMTState, block: EVMBlock) -> List[GlobalState]:
        """处理 JUMP 指令。

        Args:
            global_state: 当前全局状态
            mstate: 执行后的机器状态
            block: 当前块

        Returns:
            新全局状态列表
        """
        last_op = block.operations[-1]

        if last_op.immediate is None or not last_op.is_static:
            # 动态跳转，不支持
            from utils.exceptions import UnsupportedJumpError
            raise UnsupportedJumpError(
                "dynamic_jump",
                f"Dynamic JUMP at pc={last_op.pc} in block pc={block.pc}",
                "Dynamic jumps are not supported"
            )

        target_pc = last_op.immediate
        target_block = self.blocks_by_pc.get(target_pc)

        if target_block is None:
            # 跳转目标未找到
            from utils.exceptions import LogicError
            raise LogicError(
                f"Static JUMP at pc={last_op.pc} targets pc={target_pc}, "
                f"but target block not found"
            )

        # 创建新的全局状态
        import copy
        target_node = self.cfg.get_or_create_node(target_pc)
        new_state = GlobalState(
            mstate=mstate,
            world_state=copy(global_state.world_state),
            node=target_node
        )
        new_state.depth = global_state.depth + 1

        return [new_state]

    def _handle_jumpi(self, global_state: GlobalState, mstate: SMTState, block: EVMBlock) -> List[GlobalState]:
        """处理 JUMPI 指令。

        Args:
            global_state: 当前全局状态
            mstate: 执行后的机器状态
            block: 当前块

        Returns:
            新全局状态列表（两个分支）
        """
        import copy

        last_op = block.operations[-1]

        if last_op.immediate is None or not last_op.is_static:
            # 动态跳转，不支持
            from utils.exceptions import UnsupportedJumpError
            raise UnsupportedJumpError(
                "dynamic_jumpi",
                f"Dynamic JUMPI at pc={last_op.pc} in block pc={block.pc}",
                "Dynamic conditional jumps are not supported"
            )

        target_pc = last_op.immediate
        target_block = self.blocks_by_pc.get(target_pc)

        if target_block is None:
            # 跳转目标未找到
            from utils.exceptions import LogicError
            raise LogicError(
                f"Static JUMPI at pc={last_op.pc} targets pc={target_pc}, "
                f"but target block not found"
            )

        # 从栈中提取条件（在 JUMPI 执行前）
        condition_value = global_state.mstate.evm_stack.peek(0)

        # 转换为布尔条件：非零 = True
        jump_condition = condition_value != BitVecVal(0, 256)
        fallthrough_condition = Not(jump_condition)

        new_states = []

        # 分支 1：跳转到目标
        if target_block is not None:
            target_node = self.cfg.get_or_create_node(target_pc)

            # 深拷贝状态
            jump_world_state = copy.deepcopy(global_state.world_state)
            jump_world_state.constraints.add(jump_condition)

            jump_state = GlobalState(
                mstate=mstate.copy(),
                world_state=jump_world_state,
                node=target_node
            )
            jump_state.depth = global_state.depth + 1
            new_states.append(jump_state)

        # 分支 2：顺序执行
        current_idx = self.blocks.index(block)
        if current_idx + 1 < len(self.blocks):
            fallthrough_pc = self.blocks[current_idx + 1].pc
            fallthrough_node = self.cfg.get_or_create_node(fallthrough_pc)

            # 深拷贝状态
            fallthrough_world_state = copy.deepcopy(global_state.world_state)
            fallthrough_world_state.constraints.add(fallthrough_condition)

            fallthrough_state = GlobalState(
                mstate=mstate.copy(),
                world_state=fallthrough_world_state,
                node=fallthrough_node
            )
            fallthrough_state.depth = global_state.depth + 1
            new_states.append(fallthrough_state)
        else:
            # 没有下一个块，当前状态是终止状态
            pass

        return new_states

    def _handle_fallthrough(self, global_state: GlobalState, mstate: SMTState, block: EVMBlock) -> List[GlobalState]:
        """处理顺序执行（fallthrough）。

        Args:
            global_state: 当前全局状态
            mstate: 执行后的机器状态
            block: 当前块

        Returns:
            新全局状态列表
        """
        import copy

        # 找到下一个块
        current_idx = self.blocks.index(block)
        if current_idx + 1 >= len(self.blocks):
            # 没有下一个块，返回空列表
            return []

        next_pc = self.blocks[current_idx + 1].pc
        next_node = self.cfg.get_or_create_node(next_pc)

        new_state = GlobalState(
            mstate=mstate,
            world_state=copy(global_state.world_state),
            node=next_node
        )
        new_state.depth = global_state.depth + 1

        return [new_state]

    def _get_last_operation(self, global_state: GlobalState) -> Optional:
        """获取块中的最后一个操作。

        Args:
            global_state: 全局状态

        Returns:
            最后一个操作或 None
        """
        node = global_state.node
        if node is None or not node.block.operations:
            return None
        return node.block.operations[-1]

    def _is_terminal_state(self, global_state: GlobalState) -> bool:
        """检查是否是终止状态。

        Args:
            global_state: 全局状态

        Returns:
            如果是终止状态则返回 True
        """
        node = global_state.node
        if node is None or not node.block.operations:
            return False

        last_op = node.block.operations[-1]
        last_kind = last_op.kind.upper()
        return last_kind in ["STOP", "RETURN", "REVERT", "SELFDESTRUCT"]


def build_dynamic_cfg(blocks: List[EVMBlock],
                      initial_state: SMTState,
                      strategy_cls: type = DFSStrategy,
                      max_depth: int = 100) -> Tuple[List[GlobalState], DynamicCFG]:
    """构建动态 CFG 并执行符号执行。

    Args:
        blocks: EVM 块列表
        initial_state: 初始机器状态
        strategy_cls: 搜索策略类
        max_depth: 最大执行深度

    Returns:
        (final_states, cfg) 元组
    """
    executor = SymbolicExecutor(blocks, strategy_cls=strategy_cls, max_depth=max_depth)
    final_states = executor.execute(initial_state)
    return final_states, executor.cfg
