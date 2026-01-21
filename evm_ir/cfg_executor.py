"""
符号执行引擎（参考 mythril 的 LaserEVM）。

定义 SymbolicExecutor 类，实现 worklist 驱动的符号执行。
"""

from typing import List, Dict, Optional, Tuple, TYPE_CHECKING, Any
from z3 import BitVecVal, Not

if TYPE_CHECKING:
    from .models import EvmOperator

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
                 use_reachability_check: bool = False):
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

    def manage_cfg(self, opcode: str, new_states: List[GlobalState],
                   from_pc: int,
                   source_op: Optional[Any] = None) -> None:
        """管理 CFG 构建。

        在执行过程中动态添加边。

        Args:
            opcode: 操作码（JUMP/JUMPI 等）
            new_states: 新生成的状态
            from_pc: 源节点 PC
            source_op: 产生这条边的源操作（EvmOperator）
        """
        if not new_states:
            return

        current_pc = from_pc

        if opcode == "JUMP":
            # 无条件跳转：添加单条边
            if len(new_states) == 1 and new_states[0].node:
                target_pc = new_states[0].node.pc
                self.cfg.add_edge(current_pc, target_pc, EdgeType.UNCONDITIONAL,
                                source_operation=source_op)

        elif opcode == "JUMPI":
            # 条件跳转：添加两条边（跳转和顺序执行）
            # 第一个状态是跳转分支（条件为真），第二个是 fallthrough（条件为假）
            for i, state in enumerate(new_states):
                if not state.node:
                    continue
                target_pc = state.node.pc

                if i == 0:
                    # 跳转分支（条件为真）
                    edge_type = EdgeType.CONDITIONAL_TRUE
                    condition = self._extract_jumpi_condition(state)
                else:
                    # Fallthrough 分支（条件为假）
                    edge_type = EdgeType.CONDITIONAL_FALSE
                    condition = None  # 条件为假的边不需要额外条件

                self.cfg.add_edge(current_pc, target_pc, edge_type, condition,
                                source_operation=source_op)

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
            # 【预留】循环检测调用点（TODO: 实现检测逻辑）
            self._detect_and_handle_loops(global_state)

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
                if last_op and global_state.node:
                    opcode = last_op.kind.upper()
                    from_pc = global_state.node.pc
                    self.manage_cfg(opcode, new_states, from_pc, source_op=last_op)

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
        current_mstate = mstate.copy()

        # 过滤出实际执行的操作（跳过标记）
        ops = [op for op in block.operations if op.kind.upper() not in ["TAG", "BLOCKEND"]]
        
        if not ops:
            # 空块，顺序执行到下一个块
            global_state.mstate = current_mstate
            return self._handle_fallthrough(global_state, current_mstate, block)

        # 检查最后一个指令是否是跳转指令
        last_op = ops[-1]
        last_kind = last_op.kind.upper()
        
        # 执行除最后一个跳转指令以外的所有指令
        main_ops = ops[:-1] if last_kind in ["JUMP", "JUMPI"] else ops
        
        for op in main_ops:
            kind = op.kind.upper()
            
            # 检查终止指令
            if kind in ["STOP", "RETURN", "REVERT", "SELFDESTRUCT"]:
                # 执行终止指令（可能包含堆栈弹出，如 RETURN/REVERT）
                current_mstate = op.to_z3(current_mstate)
                # 更新全局状态为终止时的状态
                global_state.mstate = current_mstate
                # 返回空列表（无后继状态）
                return []

            # 执行操作
            current_mstate = op.to_z3(current_mstate)

        # 处理跳转或顺序执行
        if last_kind == "JUMP":
            # 执行跳转指令（更新堆栈）
            final_mstate = last_op.to_z3(current_mstate)
            global_state.mstate = final_mstate
            return self._handle_jump(global_state, final_mstate, block)
            
        elif last_kind == "JUMPI":
            # 在执行 JUMPI 弹出前提取条件
            # 对于静态跳转，dest 已折叠，栈顶是条件
            condition_value = current_mstate.evm_stack.peek(0)
            
            # 执行 JUMPI 指令（更新堆栈，弹出条件）
            final_mstate = last_op.to_z3(current_mstate)
            global_state.mstate = final_mstate
            
            # 传递提取的条件给处理器
            return self._handle_jumpi(global_state, final_mstate, block, condition_value)
            
        else:
            # 顺序执行到下一个块（已经在 main_ops 中执行完所有指令）
            global_state.mstate = current_mstate
            return self._handle_fallthrough(global_state, current_mstate, block)

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
            world_state=copy.copy(global_state.world_state),
            node=target_node
        )
        new_state.depth = global_state.depth + 1

        return [new_state]

    def _handle_jumpi(self, global_state: GlobalState, mstate: SMTState, block: EVMBlock, condition_value: Optional[Any] = None) -> List[GlobalState]:
        """处理 JUMPI 指令。

        Args:
            global_state: 当前全局状态
            mstate: 执行后的机器状态
            block: 当前块
            condition_value: 预先提取的跳转条件（如果为 None 则从 mstate 中提取）

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

        # 确定跳转条件
        if condition_value is None:
            # 如果没有传入提取好的条件，则尝试从 mstate 中 peek（此时 JUMPI 可能还未执行）
            condition_value = mstate.evm_stack.peek(0)

        # 转换为布尔条件：非零 = True
        jump_condition = condition_value != BitVecVal(0, 256)
        fallthrough_condition = Not(jump_condition)

        new_states = []

        # 分支 1：跳转到目标
        if target_block is not None:
            target_node = self.cfg.get_or_create_node(target_pc)

            # 深拷贝状态（JUMPI 分支必须深拷贝，参考 Mythril）
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
        current_idx = self.blocks.index(block) # TODO: make it more efficient
        if current_idx + 1 < len(self.blocks):
            fallthrough_pc = self.blocks[current_idx + 1].pc
            fallthrough_node = self.cfg.get_or_create_node(fallthrough_pc)

            # 深拷贝状态（JUMPI 分支必须深拷贝，参考 Mythril）
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
            world_state=copy.copy(global_state.world_state),
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

    def _detect_and_handle_loops(self, global_state: GlobalState) -> None:
        """检测当前状态是否形成循环，并根据类型分类处理。

        TODO: 实现循环检测逻辑
        - PC 重复检测
        - 循环分类（静态/动态/无界）
        - 静态有界循环展开
        - 其他循环类型抛出 UnsupportedLoopError

        Args:
            global_state: 当前全局状态

        Raises:
            UnsupportedLoopError: 检测到不支持的循环类型时抛出
        """
        # TODO: 实现循环检测
        pass

    def _classify_loop(self, loop_pc: int, path_context: Dict) -> str:
        """判断循环类型。

        TODO: 实现循环分类逻辑
        - 静态有界：检查循环条件是否为常量比较
        - 动态有界：条件与符号变量比较
        - 无界：无法确定循环边界

        Args:
            loop_pc: 循环头的 PC
            path_context: 执行路径上下文信息

        Returns:
            "static_bounded" | "dynamic_bounded" | "unbounded"
        """
        # TODO: 实现循环分类
        return "dynamic_bounded"  # 默认返回


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
