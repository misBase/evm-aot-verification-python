"""
符号执行引擎（参考 mythril 的 LaserEVM）。

定义 SymbolicExecutor 类，实现 worklist 驱动的符号执行。
"""

import copy

from typing import List, Dict, Optional, Tuple, TYPE_CHECKING, Any
from z3 import And, BitVecVal, BoolVal, IntVal, Not, is_false, is_true, simplify
from evm_ir.status_code import EvmStatusCode, set_terminal_status

if TYPE_CHECKING:
    from .models import EvmOperator

from .models import EVMBlock
from .cfg_structures import DynamicCFG, EdgeType
from .cfg_state import GlobalState
from .cfg_strategies import DFSStrategy
from common.path_observation import PathCoverageCertificate
from state.smt_state import SMTState


class SymbolicExecutor:
    """基于 worklist 的符号执行引擎。

    完全参考 mythril 的 LaserEVM 设计：
    - work_list 管理待执行状态
    - 动态构建 CFG
    - 策略模式控制搜索顺序
    - 可达性检查剪枝不可达状态
    """

    _CONTROL_OPS = frozenset({"JUMP", "JUMPI", "STOP", "RETURN", "REVERT", "SELFDESTRUCT", "INVALID"})
    _TERMINAL_OPS = frozenset({"STOP", "RETURN", "REVERT", "SELFDESTRUCT", "INVALID"})

    def __init__(self,
                 blocks: List[EVMBlock],
                 strategy_cls: type = DFSStrategy,
                 max_depth: int = 100,
                 use_reachability_check: bool = False,
                 stop_pcs: Optional[set] = None):
        """初始化符号执行引擎。

        Args:
            blocks: 所有 EVM 块列表
            strategy_cls: 搜索策略类
            max_depth: 最大执行深度
            use_reachability_check: 是否使用可达性检查
            stop_pcs: cutpoint 集合。到达这些 pc 的非入口状态不再执行，
                收进 ``cut_states``——供循环归纳引擎在 cutpoint 处截断段执行。
        """
        # todo: max_depth > max_iteration * blocks in loop body
        #       max_depth only used in test, will be deleted

        self.blocks = blocks
        self.blocks_by_pc: Dict[int, EVMBlock] = {block.pc: block for block in blocks}
        self.max_depth = max_depth
        self.use_reachability_check = use_reachability_check

        # 合法跳转目标集合（JUMPDEST 的 PC），对应 amd64 后端的 c.jumpTable / c.jumpList。
        # 必须是全集：跳转目标校验据此判定 INVALID_JUMP，部分集合会把合法跳转判成非法。
        self.valid_jump_targets = {block.pc for block in blocks if block.is_jump_target}

        # 创建动态 CFG
        self.cfg = DynamicCFG(blocks)

        self.static_loop_headers = self._pre_analyze_static_loop_headers()
        self.max_iteration = 500 

        # work_list：待执行的全局状态列表
        self.work_list: List[GlobalState] = []

        # 创建搜索策略
        self.strategy = strategy_cls(self.work_list, max_depth)

        # 统计信息
        self.total_states = 0
        self.pruned_states = 0
        self.coverage_incomplete_reasons: List[str] = []

        # 终止状态列表
        self.final_states: List[GlobalState] = []

        # cutpoint 截断
        self.stop_pcs = stop_pcs or set()
        self.cut_states: List[GlobalState] = []

    def _mark_coverage_incomplete(self, reason: str) -> None:
        if reason not in self.coverage_incomplete_reasons:
            self.coverage_incomplete_reasons.append(reason)

    def path_coverage_certificate(self) -> PathCoverageCertificate:
        """返回终止路径覆盖性的 fail-closed 证书。

        对齐 x86 侧 ``X86SymbolicExecutor.path_coverage_certificate()``：
        证书只声明 executor 已探索所有未被证明不可达的建模控制流后继，
        不证明指令语义本身的正确性。可达性剪枝（UNSAT 路径）不影响
        完整性，只进 details。
        """
        depth_pruned = getattr(self.strategy, "depth_pruned_count", 0)
        reasons = list(self.coverage_incomplete_reasons)
        if depth_pruned:
            reasons.append(f"depth-pruned state count: {depth_pruned}")
        if self.work_list:
            reasons.append(f"work-list not drained: {len(self.work_list)} state(s)")

        details = (
            ("terminal_paths", len(self.final_states)),
            ("total_states", self.total_states),
            ("unsat_pruned_states", self.pruned_states),
            ("depth_pruned_states", depth_pruned),
        )
        if reasons:
            return PathCoverageCertificate(
                complete=False,
                reason="; ".join(reasons),
                source="evm-symbolic-executor",
                details=details,
            )
        return PathCoverageCertificate.by_construction(
            "EVM CFG executor explored all modeled successors",
            source="evm-symbolic-executor",
            details=details,
        )

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
            # JUMP 指令：直接使用状态中的边类型提示
            for state in new_states:
                if state.node:
                    target_pc = state.node.pc
                    # 使用状态中的边类型提示，如果没有则默认为 UNCONDITIONAL
                    edge_type = state.edge_type_hint or EdgeType.UNCONDITIONAL
                    # 获取条件（如果有）
                    condition = self._extract_jump_condition_from_state(state)
                    self.cfg.add_edge(current_pc, target_pc, edge_type, condition,
                                    source_operation=source_op)

        elif opcode == "JUMPI":
            # JUMPI 指令：直接使用状态中的边类型提示
            for state in new_states:
                if not state.node:
                    continue
                target_pc = state.node.pc
                # 使用状态中的边类型提示，如果没有则默认为 CONDITIONAL_TRUE
                edge_type = state.edge_type_hint or EdgeType.CONDITIONAL_TRUE
                # 获取条件（如果有）
                condition = self._extract_jump_condition_from_state(state)
                self.cfg.add_edge(current_pc, target_pc, edge_type, condition,
                                source_operation=source_op)

    def _extract_jump_condition_from_state(self, state: GlobalState):
        """从状态中提取跳转条件（用于从 If 表达式解析的多分支）。

        Args:
            state: 全局状态

        Returns:
            条件 BoolRef 或 None
        """
        from z3 import BoolVal, eq
        constraints = state.get_constraints()
        # 过滤掉初始的 True 约束，获取实际添加的约束
        real_constraints = [c for c in constraints if not (isinstance(c, type(BoolVal(True))) and eq(c, BoolVal(True)))]
        if real_constraints:
            return real_constraints[-1]
        return None

    def _get_next_block_pc(self, from_pc: int) -> Optional[int]:
        """获取给定 PC 的下一个块的 PC。

        Args:
            from_pc: 源块 PC

        Returns:
            下一个块的 PC，如果不存在则返回 None
        """
        for i, block in enumerate(self.blocks):
            if block.pc == from_pc and i + 1 < len(self.blocks):
                return self.blocks[i + 1].pc
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

        # 在执行任何块之前预填充合法跳转目标全集，供 JUMP/JUMPI 的目标校验使用。
        initial_state.valid_jump_targets = set(self.valid_jump_targets)

        # 创建初始全局状态
        entry_node = self.cfg.get_or_create_node(entry_pc)
        initial_global_state = GlobalState(
            mstate=initial_state,
            node=entry_node
        )
        initial_global_state.depth = 0
        for headers in self.static_loop_headers:
            initial_global_state.loop_time[headers] = 0

        # 注入 caller 设定的全局先验（precondition assumptions）。详见
        # SMTState.assumptions 注释。
        for assumption in getattr(initial_state, 'assumptions', None) or []:
            initial_global_state.world_state.constraints.add(assumption)

        # 添加到 work_list
        self.work_list.append(initial_global_state)

        # 主执行循环
        for global_state in self.strategy:
            # cutpoint 截断：到达 stop pc 的状态不再展开。判别"非入口状态
            # 对象"（允许从 cutpoint 自身作为入口启动段执行）；不能用
            # depth>0——fallthrough 后继不增 depth，直落进 cutpoint 的
            # 状态会带着 depth=0 漏过截断、穿透 cutpoint 继续执行。
            if (self.stop_pcs and global_state is not initial_global_state
                    and global_state.node
                    and global_state.node.pc in self.stop_pcs):
                self.cut_states.append(global_state)
                continue

            # 循环检测调用
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
                if self._path_is_impossible(global_state.world_state):
                    self.pruned_states += 1
                else:
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

        # TAG 序言守卫，镜像 impl_amd64.go compileEVMTag(tag *ir.Block) 的检查次序：
        #   1. makeStaticUseGas(tag.StaticGas) → jmpIfGasNotEnough → OUT_OF_GAS
        #   2. CMP MinDepth; JCS               → STACK_UNDERFLOW
        #   3. CMP MaxDepth+1; JCC             → STACK_REACHED_LIMIT
        # 次序体现为后一个条件都带上前面所有条件的否定，否则会产出条件重叠、状态码
        # 互相矛盾的终态。后两个检查在 Go 侧无条件发射、无 1024 阈值，sp 以字节计
        # （×32），这里以栈项计。无 TAG 即无检查；恒不成立的条件由 simplify +
        # is_false 剪掉，不建路径。
        if any(op.kind.upper() == "TAG" for op in block.operations):
            # gas 检查**无条件**建模：下面的扣减是无条件的纯减法，不分叉就会在 gas
            # 不足时回绕续跑（IR 给 STOPPED 而 AOT 给 OUT_OF_GAS）。钳零在解释器里没有
            # 对应物——UseGas 失败是**终止**，不是归零续跑。
            #
            # 代价可控：具体 gas 预算（GasCheck.OFF / FIXED_BUDGET）下条件在 simplify
            # 阶段折成 False，连路径都不建；符号 gas（FULL）下这条分支正是要验的东西。
            if getattr(block, "static_gas", 0):
                from z3 import ULT
                is_oog = simplify(
                    ULT(current_mstate.evm_gas.Gas, BitVecVal(block.static_gas, 64))
                )
            else:
                is_oog = BoolVal(False)

            sp = current_mstate.evm_stack.SP

            # Go 是无符号比较，MinDepth==0 时恒假 —— 跳过是等价变换。
            # （Z3 Int 有符号，负 SP 会被误判；负 SP 靠本守卫维持不可达，
            #   SP 若改 BitVec 或引入符号入口 SP，这里要补无符号语义。）
            if block.min_depth > 0:
                is_underflow = simplify(And(Not(is_oog), sp < IntVal(block.min_depth)))
            else:
                is_underflow = BoolVal(False)

            # MaxDepth < 0（ir.InvalidMax）时恒真，对应 Go 的无条件 exit。
            is_overflow = simplify(
                And(Not(is_oog), Not(is_underflow), sp > IntVal(block.max_depth))
            )

            # append 顺序即 Go 的检查顺序。
            self._append_tag_depth_error_state(
                global_state, current_mstate, node,
                is_oog, EvmStatusCode.OUT_OF_GAS,
            )
            self._append_tag_depth_error_state(
                global_state, current_mstate, node,
                is_underflow, EvmStatusCode.STACK_UNDERFLOW,
            )
            self._append_tag_depth_error_state(
                global_state, current_mstate, node,
                is_overflow, EvmStatusCode.STACK_REACHED_LIMIT,
            )

            # 先加约束再 return：_is_terminal_state 只看块的控制流指令，与返回值无关，
            # 少了这条约束，以 RETURN/STOP 结尾的块会留下一条可满足的假正常终止路径。
            normal_cond = simplify(
                And(Not(is_oog), Not(is_underflow), Not(is_overflow))
            )
            if not is_true(normal_cond):
                global_state.world_state.constraints.add(normal_cond)
            if is_false(normal_cond):
                # 本块不可能被正常进入，停止执行与后继传播。
                return []

        # block 入口一次性扣静态 gas，镜像 makeStaticUseGas 与 x86 侧的
        # `SUBQ staticGas; MOVQ -> [R13+0x70]`（编译期已把块内各指令的静态 gas 求和
        # 成一个常量，所以这里也必须按块扣、不能逐 opcode 扣）。
        # 无条件扣减：动态 gas 的 OOG 阈值必须建立在"静态 gas 已扣"之上，少扣一块阈值
        # 就是错的。具体预算下扣减后仍是常量，不会引入 If-chain。
        if getattr(block, "static_gas", 0):
            current_mstate.evm_gas = current_mstate.evm_gas.consume_static(block.static_gas)

        # 过滤出实际执行的操作（跳过标记）
        ops = [op for op in block.operations if op.kind.upper() not in ["TAG", "BLOCKEND"]]
        
        if not ops:
            # 空块，顺序执行到下一个块
            global_state.mstate = current_mstate
            return self._handle_fallthrough(global_state, current_mstate, block)

        # 找到第一个控制流操作（JUMP/JUMPI/终止指令）
        # 控制流操作之后的指令视为死代码，忽略
        ctrl_idx, ctrl_op = self._find_control_flow_op(ops)

        if ctrl_op is None:
            # 没有控制流操作，顺序执行所有指令
            for op in ops:
                current_mstate = self._execute_op_with_outcome(
                    global_state, current_mstate, op, node,
                )
                if current_mstate is None:
                    return []   # 错误条件恒真，本路径已全部变成错误终态
            global_state.mstate = current_mstate
            return self._handle_fallthrough(global_state, current_mstate, block)

        ctrl_kind = ctrl_op.kind.upper()
        # 控制流操作之前的普通指令
        main_ops = ops[:ctrl_idx]

        for op in main_ops:
            current_mstate = self._execute_op_with_outcome(
                global_state, current_mstate, op, node,
            )
            if current_mstate is None:
                return []

        # 处理跳转或终止
        if ctrl_kind == "JUMP":
            # 只有在非静态跳转时才从栈中提取目标值
            # 静态跳转的目标在 immediate 中，栈不会被弹出
            if ctrl_op.immediate is None or not ctrl_op.is_static:
                target_value = current_mstate.evm_stack.peek(0)
            else:
                target_value = None

            # 目标非法时 INVALID_JUMP 在这里就分裂成终止路径，
            # _handle_jump 只会看到合法目标的正常路径。
            final_mstate = self._execute_op_with_outcome(
                global_state, current_mstate, ctrl_op, node,
            )
            if final_mstate is None:
                return []
            global_state.mstate = final_mstate

            # 传递提取的目标值给处理器
            return self._handle_jump(global_state, final_mstate, block, ctrl_op, target_value)

        elif ctrl_kind == "JUMPI":
            # 在执行 JUMPI 弹出前提取条件和目标
            # index=0: 条件值
            # index=1: 跳转目标（如果非静态）
            condition_value = current_mstate.evm_stack.peek(0)

            # 如果是非静态跳转，还需要提取目标值
            if ctrl_op.immediate is None or not ctrl_op.is_static:
                target_value = current_mstate.evm_stack.peek(1)
            else:
                target_value = None

            # 执行 JUMPI 指令（更新堆栈，弹出条件）
            final_mstate = self._execute_op_with_outcome(
                global_state, current_mstate, ctrl_op, node,
            )
            if final_mstate is None:
                return []
            global_state.mstate = final_mstate

            # 传递提取的值给处理器
            return self._handle_jumpi(global_state, final_mstate, block, ctrl_op, condition_value, target_value)

        else:
            # 终止指令（STOP/RETURN/REVERT/SELFDESTRUCT）
            current_mstate = self._execute_op_with_outcome(
                global_state, current_mstate, ctrl_op, node,
            )
            if current_mstate is None:
                return []
            global_state.mstate = current_mstate
            return []

    @staticmethod
    def _branch_is_excluded(world_state, condition) -> bool:
        """在当前路径约束下，分支条件是否已不可满足。

        用于区分"分支已被先前的约束排除"与"IR/CFG 真的不一致"：JUMPI 目标非法时
        正常路径已带 ¬taken，但符号 condition 让 jump_condition 自身 simplify
        不出 False，仅凭它会把 taken 误当成可行。
        """
        combined = simplify(And(world_state.constraints.as_bool(), condition))
        if is_false(combined):
            return True
        probe = copy.copy(world_state)
        probe.constraints.add(condition)
        return not probe.constraints.is_possible()

    @staticmethod
    def _path_is_impossible(world_state) -> bool:
        """路径条件被化简成字面 False —— 该终态永远走不到。

        终态一旦进 final_states 就会参与下游 path-pair 的笛卡尔积，所以在入口统一剪掉。
        典型来源：TAG 守卫判定本块必然报错后写进的 False 约束（见 execute_state）。
        """
        return is_false(simplify(world_state.constraints.as_bool()))

    def _append_error_terminal_state(self,
                                     global_state: GlobalState,
                                     error_mstate: SMTState,
                                     node,
                                     condition,
                                     status_code: EvmStatusCode) -> None:
        """追加一条错误终止路径。

        ``error_mstate`` 必须已归属于这条错误路径（调用方负责快照/复制）。

        只丢弃可证不可满足的路径（simplify 折成字面 False，或开启可达性检查后判 UNSAT）：
        留着它们只会撑大 final_states，放大下游 path-pair 的笛卡尔积。
        """
        if is_false(condition):
            return

        set_terminal_status(error_mstate, status_code)
        error_mstate.return_offset = BitVecVal(0, 64)
        error_mstate.return_length = BitVecVal(0, 64)

        # 浅拷贝够用：Constraints.__copy__ 会新建列表，Z3 表达式不可变，且终态不再被写。
        error_world = copy.copy(global_state.world_state)
        error_world.constraints.add(condition)

        if self._path_is_impossible(error_world):
            self.pruned_states += 1
            return

        if self.use_reachability_check and not error_world.constraints.is_possible():
            self.pruned_states += 1
            return

        error_state = GlobalState(
            mstate=error_mstate,
            world_state=error_world,
            node=node,
        )
        error_state.depth = global_state.depth
        error_state.loop_time = global_state.loop_time.copy()
        self.final_states.append(error_state)

    def _append_tag_depth_error_state(self,
                                      global_state: GlobalState,
                                      mstate: SMTState,
                                      node,
                                      condition,
                                      status_code: EvmStatusCode) -> None:
        """为 TAG 栈深度守卫的一个错误分支追加终止状态。

        必须先复制：两个错误分支共用调用方的 current_mstate，
        直接改会让 underflow 污染 overflow，并把错误码漏给正常路径。
        """
        if is_false(condition):
            return
        self._append_error_terminal_state(
            global_state, mstate.copy(), node, condition, status_code,
        )

    def _execute_op_with_outcome(self,
                                 global_state: GlobalState,
                                 mstate: SMTState,
                                 op: 'EvmOperator',
                                 node) -> Optional[SMTState]:
        """执行一条 opcode，并把它产生的错误分支立即分裂成终止路径。

        这是**所有** opcode 执行的唯一入口——漏掉一个执行点，那里的错误分支就会
        静默消失（copy() 的检查拦不住"执行完直接丢弃 pending_errors"）。

        多个错误分支按 append 顺序互斥化，对齐 codegen 的检查先后：

            effective_error_i = error_i ∧ ¬error_0 ∧ ... ∧ ¬error_{i-1}
            normal_cond       = ¬error_0 ∧ ... ∧ ¬error_n

        Returns:
            正常路径的后继状态；``None`` 表示错误条件恒真、本路径已被完全吸收，
            调用方应当停止执行并返回空后继列表。
        """
        if mstate.pending_errors:
            from utils.exceptions import LogicError
            raise LogicError(
                "unconsumed_pending_errors",
                f"op {op.kind} at pc={op.pc} received a state with "
                f"{len(mstate.pending_errors)} unconsumed error branch(es)",
            )
        # 同理：上一条 op 挂的路径约束若没被下面 drain 走，说明 drain 漏了。丢约束本身
        # 只是少剪枝（安全方向），但机制会静默失效，只能靠这个入口检查暴露。
        if mstate.pending_constraints:
            from utils.exceptions import LogicError
            raise LogicError(
                "unconsumed_pending_constraints",
                f"op {op.kind} at pc={op.pc} received a state with "
                f"{len(mstate.pending_constraints)} undrained path constraint(s)",
            )

        new_mstate = op.to_z3(mstate)

        # 在错误分支分裂**之前**并入：_append_error_terminal_state 会
        # copy.copy(global_state.world_state)，此刻加进去，正常后继与各错误终态都能继承。
        for constraint in new_mstate.pending_constraints:
            global_state.world_state.constraints.add(constraint)
        new_mstate.pending_constraints = []

        pending = list(new_mstate.pending_errors)
        new_mstate.pending_errors = []   # 状态要交给后继，队列必须先消费干净
        if not pending:
            return new_mstate

        negations = []
        seen_snapshots: List[int] = []
        for branch in pending:
            # 每个分支必须独占自己的快照：_append_error_terminal_state 直接在上面
            # 写状态码，共用一个对象会让后一个分支覆盖前一个（前者已进 final_states，
            # 改的是同一个引用），且不会有任何报错。
            if id(branch.terminal_state) in seen_snapshots:
                from utils.exceptions import LogicError
                raise LogicError(
                    "shared_error_snapshot",
                    f"op {op.kind} at pc={op.pc} reused one terminal_state across "
                    f"multiple error branches",
                )
            seen_snapshots.append(id(branch.terminal_state))

            effective = branch.condition
            if negations:
                effective = And(effective, *negations)
            effective = simplify(effective)
            self._append_error_terminal_state(
                global_state, branch.terminal_state, node, effective, branch.status_code,
            )
            negations.append(Not(branch.condition))

        normal_cond = simplify(And(*negations)) if len(negations) > 1 else simplify(negations[0])

        # 先加约束再 return：少了这条约束，以 STOP/RETURN 结尾的块会在错误区域上
        # 留下一条可满足的假正常终止路径（与 TAG 守卫同一个坑）。
        if not is_true(normal_cond):
            global_state.world_state.constraints.add(normal_cond)
        if is_false(normal_cond):
            return None
        return new_mstate

    def _handle_jump(self, global_state: GlobalState, mstate: SMTState, block: EVMBlock,
                     ctrl_op: Optional['EvmOperator'] = None,
                     target_value: Optional[Any] = None) -> List[GlobalState]:
        """处理 JUMP 指令。

        Args:
            global_state: 当前全局状态
            mstate: 执行后的机器状态
            block: 当前块
            ctrl_op: 产生控制流的 JUMP 操作（由调用者传入）；若为 None 则从 block 中查找
            target_value: 预先提取的跳转目标值（如果为 None 则尝试从 immediate 获取）

        Returns:
            新全局状态列表
        """
        import copy
        from utils.exceptions import UnsupportedJumpError, LogicError
        from utils.z3_helpers import analyze_jump_target

        if ctrl_op is None:
            ops = [op for op in block.operations if op.kind.upper() not in ["TAG", "BLOCKEND"]]
            _, ctrl_op = self._find_control_flow_op(ops)
        if ctrl_op is None:
            from utils.exceptions import LogicError
            raise LogicError("missing_ctrl_op", f"Block at pc={block.pc} has no JUMP control flow operation")
        last_op = ctrl_op

        # 首先检查是否有 immediate（静态跳转）
        if last_op.immediate is not None and last_op.is_static:
            target_pc = last_op.immediate
            target_block = self.blocks_by_pc.get(target_pc)
            if target_block is None:
                raise LogicError(
                    "missing_jump_target",
                    f"Static JUMP at pc={last_op.pc} targets pc={target_pc}, but target block not found"
                )
            target_node = self.cfg.get_or_create_node(target_pc)
            new_state = GlobalState(
                mstate=mstate,
                world_state=copy.copy(global_state.world_state),
                node=target_node
            )
            new_state.depth = global_state.depth + 1
            new_state.loop_time = global_state.loop_time.copy()

            # 静态跳转是无条件的
            from .cfg_structures import EdgeType
            new_state.edge_type_hint = EdgeType.UNCONDITIONAL
            return [new_state]

        # 分析提取的目标值
        if target_value is None:
            raise UnsupportedJumpError(
                "dynamic_jump",
                f"JUMP at pc={last_op.pc} has no target value",
                "Cannot resolve jump target"
            )

        analysis = analyze_jump_target(target_value)

        if not analysis.is_static and last_op.immediate_set:
            # resolved_multi JUMP 且目标值是纯符号（如循环归纳 havoc 后的
            # caller-frame 返回地址）：按 IR 保证（resolveSymbolicJumps 已证
            # 目标 ∈ immediate_set）对每个候选目标分叉，路径带 value==target
            # 约束。x86 侧编译产物（CMPQ+JEQ 比较链）对同一符号值自然分叉，
            # 两侧对齐。
            from z3 import BitVecVal
            fork_states = []
            from .cfg_structures import EdgeType as _EdgeType
            for target_pc in dict.fromkeys(last_op.immediate_set):
                target_block = self.blocks_by_pc.get(target_pc)
                if target_block is None:
                    raise LogicError(
                        "missing_jump_target",
                        f"resolved_multi JUMP at pc={last_op.pc} targets "
                        f"pc={target_pc}, but target block not found",
                    )
                target_node = self.cfg.get_or_create_node(target_pc)
                fork_world_state = copy.deepcopy(global_state.world_state)
                fork_world_state.constraints.add(
                    target_value == BitVecVal(target_pc, 256)
                )
                fork_state = GlobalState(
                    mstate=mstate.copy(),
                    world_state=fork_world_state,
                    node=target_node,
                )
                fork_state.depth = global_state.depth + 1
                fork_state.loop_time = global_state.loop_time.copy()
                fork_state.edge_type_hint = _EdgeType.UNCONDITIONAL
                fork_states.append(fork_state)
            return fork_states

        if not analysis.is_static:
            # 真正的动态跳转，不支持
            raise UnsupportedJumpError(
                "dynamic_jump",
                f"Dynamic JUMP at pc={last_op.pc} in block pc={block.pc}",
                "Dynamic jumps are not supported"
            )

        new_states = []
        
        # 判断是否来自 If 表达式
        # 如果只有一个目标且无条件，是简单的无条件跳转
        # 如果有多个目标或有条件，说明是从 If 表达式解析的
        from .cfg_structures import EdgeType
        is_if_expression = len(analysis.targets) > 1 or (
            len(analysis.targets) == 1 and analysis.targets[0][1] is not None
        )

        for i, (target_pc, condition) in enumerate(analysis.targets):
            target_block = self.blocks_by_pc.get(target_pc)
            if target_block is None:
                raise LogicError(
                    "missing_jump_target",
                    f"Resolved JUMP at pc={last_op.pc} targets pc={target_pc}, but target block not found"
                )

            target_node = self.cfg.get_or_create_node(target_pc)

            # 深拷贝状态（多分支需要深拷贝）
            jump_world_state = copy.deepcopy(global_state.world_state)

            # 如果有条件（从 If 表达式解析），添加约束
            if condition is not None:
                jump_world_state.constraints.add(condition)

            jump_state = GlobalState(
                mstate=mstate.copy(),
                world_state=jump_world_state,
                node=target_node
            )
            jump_state.depth = global_state.depth + 1
            jump_state.loop_time = global_state.loop_time.copy()
            # 设置边类型提示
            if is_if_expression:
                # 从 If 表达式解析：第一个目标是 then 分支，第二个是 else 分支
                jump_state.edge_type_hint = EdgeType.IF_THEN if i == 0 else EdgeType.IF_ELSE
            else:
                # 简单的无条件跳转
                jump_state.edge_type_hint = EdgeType.UNCONDITIONAL
            
            new_states.append(jump_state)

        return new_states

    def _handle_jumpi(self, global_state: GlobalState, mstate: SMTState, block: EVMBlock,
                      ctrl_op: Optional['EvmOperator'] = None,
                      condition_value: Optional[Any] = None,
                      target_value: Optional[Any] = None) -> List[GlobalState]:
        """处理 JUMPI 指令。

        Args:
            global_state: 当前全局状态
            mstate: 执行后的机器状态
            block: 当前块
            ctrl_op: 产生控制流的 JUMPI 操作（由调用者传入）；若为 None 则从 block 中查找
            condition_value: 预先提取的跳转条件
            target_value: 预先提取的跳转目标值（如果是静态跳转则为 None）

        Returns:
            新全局状态列表（两个或更多分支）
        """
        import copy
        from utils.exceptions import UnsupportedJumpError, LogicError
        from utils.z3_helpers import analyze_jump_target
        from z3 import And

        if ctrl_op is None:
            ops = [op for op in block.operations if op.kind.upper() not in ["TAG", "BLOCKEND"]]
            _, ctrl_op = self._find_control_flow_op(ops)
        if ctrl_op is None:
            from utils.exceptions import LogicError
            raise LogicError("missing_ctrl_op", f"Block at pc={block.pc} has no JUMPI control flow operation")
        last_op = ctrl_op

        # 确定跳转条件
        if condition_value is None:
            raise UnsupportedJumpError(
                "dynamic_jumpi",
                f"JUMPI at pc={last_op.pc} has no condition value",
                "Cannot resolve jumpi condition"
            )

        jump_condition = condition_value != BitVecVal(0, 256)
        fallthrough_condition = Not(jump_condition)

        new_states = []

        # 处理跳转分支
        from .cfg_structures import EdgeType
        from z3 import simplify,is_false
        jump = simplify(jump_condition)
        if not is_false(jump):
            if last_op.immediate is not None and last_op.is_static:
                # 静态跳转：使用 immediate 作为目标
                target_pc = last_op.immediate
                target_block = self.blocks_by_pc.get(target_pc)

                if target_block is None and not self._branch_is_excluded(
                    global_state.world_state, jump_condition
                ):
                    raise LogicError(
                        "missing_jump_target",
                        f"Static JUMPI at pc={last_op.pc} targets pc={target_pc}, but target block not found"
                    )

                # 目标非法且 taken 已被排除：INVALID_JUMP 终态已分裂出去，只留 fallthrough。
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
                    jump_state.loop_time = global_state.loop_time.copy()
                    # 静态跳转目标，使用 CONDITIONAL_TRUE
                    jump_state.edge_type_hint = EdgeType.CONDITIONAL_TRUE
                    new_states.append(jump_state)
            else:
                # 尝试解析目标值
                if target_value is None:
                    raise UnsupportedJumpError(
                        "dynamic_jumpi",
                        f"Dynamic JUMPI at pc={last_op.pc} has no target value",
                        "Dynamic conditional jumps are not supported"
                    )

                analysis = analyze_jump_target(target_value)

                if not analysis.is_static:
                    raise UnsupportedJumpError(
                        "dynamic_jumpi",
                        f"Dynamic JUMPI at pc={last_op.pc} in block pc={block.pc}",
                        "Dynamic conditional jumps are not supported"
                    )

                # 判断目标是否来自 If 表达式
                is_if_target = len(analysis.targets) > 1 or (
                    len(analysis.targets) == 1 and analysis.targets[0][1] is not None
                )
                
                # 为每个解析出的目标创建跳转分支
                for i, (target_pc, target_condition) in enumerate(analysis.targets):
                    # 组合条件：jump_condition AND target_condition（如果有）
                    combined_jump_condition = jump_condition
                    if target_condition is not None:
                        combined_jump_condition = And(jump_condition, target_condition)

                    target_block = self.blocks_by_pc.get(target_pc)
                    if target_block is None:
                        # 同静态分支：目标非法时这条分支已被 ¬taken 排除。
                        if self._branch_is_excluded(
                            global_state.world_state, combined_jump_condition
                        ):
                            continue
                        raise LogicError(
                            "missing_jump_target",
                            f"Resolved JUMPI at pc={last_op.pc} targets pc={target_pc}, but target block not found"
                        )

                    target_node = self.cfg.get_or_create_node(target_pc)

                    jump_world_state = copy.deepcopy(global_state.world_state)
                    jump_world_state.constraints.add(combined_jump_condition)

                    jump_state = GlobalState(
                        mstate=mstate.copy(),
                        world_state=jump_world_state,
                        node=target_node
                    )
                    jump_state.depth = global_state.depth + 1
                    jump_state.loop_time = global_state.loop_time.copy()
                    # 设置边类型提示
                    if is_if_target:
                        # 目标是 If 表达式，使用 IF_THEN/IF_ELSE
                        jump_state.edge_type_hint = EdgeType.IF_THEN if i == 0 else EdgeType.IF_ELSE
                    else:
                        # 目标是常量，使用 CONDITIONAL_TRUE
                        jump_state.edge_type_hint = EdgeType.CONDITIONAL_TRUE
                    
                    new_states.append(jump_state)

        # 分支 2：顺序执行（fallthrough）
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
            fallthrough_state.loop_time = global_state.loop_time.copy()
            # Fallthrough 始终使用 CONDITIONAL_FALSE
            fallthrough_state.edge_type_hint = EdgeType.CONDITIONAL_FALSE
            new_states.append(fallthrough_state)
        else:
            # 没有下一个块：JUMPI 的 fallthrough 分支越过末块被丢弃。
            # 该路径不会进入 final_states（块的控制流操作是 JUMPI 而非终止
            # 指令），fail-closed 记入证书。
            self._mark_coverage_incomplete(
                f"JUMPI fallthrough past last block dropped at pc={block.pc}"
            )

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
            # 没有下一个块：该状态既不产生后继也不会进入 final_states
            # （块无终止指令），fail-closed 记入证书。
            self._mark_coverage_incomplete(
                f"fallthrough past last block dropped at pc={block.pc}"
            )
            return []

        next_pc = self.blocks[current_idx + 1].pc
        next_node = self.cfg.get_or_create_node(next_pc)

        new_state = GlobalState(
            mstate=mstate,
            world_state=copy.copy(global_state.world_state),
            node=next_node
        )
        new_state.depth = global_state.depth + 1
        new_state.loop_time = global_state.loop_time.copy()
        return [new_state]

    def _find_control_flow_op(self, ops: List['EvmOperator']) -> Tuple[Optional[int], Optional['EvmOperator']]:
        """在过滤后的操作列表中，找到第一个控制流操作（JUMP/JUMPI/终止指令）。

        控制流操作之后的指令视为死代码，应忽略。

        Returns:
            (index, operation)，若未找到则返回 (None, None)
        """
        for i, op in enumerate(ops):
            if op.kind.upper() in self._CONTROL_OPS:
                return i, op
        return None, None

    def _get_last_operation(self, global_state: GlobalState) -> Optional['EvmOperator']:
        """获取块中的第一个控制流操作（JUMP/JUMPI/终止指令）。

        控制流操作之后的指令视为死代码，以此确定实际控制流。

        Args:
            global_state: 全局状态

        Returns:
            第一个控制流操作或 None
        """
        node = global_state.node
        if node is None or not node.block.operations:
            return None
        ops = [op for op in node.block.operations if op.kind.upper() not in ["TAG", "BLOCKEND"]]
        _, ctrl_op = self._find_control_flow_op(ops)
        return ctrl_op

    def _pre_analyze_static_loop_headers(self) -> set:
        """全局拓扑预分析，通过静态 DFS 找出所有的循环头 (Back-edge 目标)。"""
        adjacency_list = {}
        for i, block in enumerate(self.blocks):
            targets = []
            ops = [op for op in block.operations if op.kind.upper() not in ["TAG", "BLOCKEND"]]
            ctrl_idx, ctrl_op = self._find_control_flow_op(ops)

            if ctrl_op is None:
                if i + 1 < len(self.blocks):
                    targets.append(self.blocks[i+1].pc)
            else:
                kind = ctrl_op.kind.upper()
                if kind in ("JUMP", "JUMPI") and ctrl_op.is_static and ctrl_op.immediate is not None:
                    targets.append(ctrl_op.immediate)
                if kind == "JUMPI":
                    if i + 1 < len(self.blocks):
                        targets.append(self.blocks[i+1].pc)

            adjacency_list[block.pc] = targets

        loop_headers = set()
        visited_state = {}

        def dfs(pc):
            visited_state[pc] = 1
            for target_pc in adjacency_list.get(pc, []):
                state = visited_state.get(target_pc, 0)
                if state == 0:
                    dfs(target_pc)
                elif state == 1:
                    loop_headers.add(target_pc)
            visited_state[pc] = 2

        if self.blocks:
            dfs(self.blocks[0].pc)

        return loop_headers

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

        ops = [op for op in node.block.operations if op.kind.upper() not in ["TAG", "BLOCKEND"]]
        _, ctrl_op = self._find_control_flow_op(ops)
        if ctrl_op is None:
            return False
        return ctrl_op.kind.upper() in self._TERMINAL_OPS

    def _detect_and_handle_loops(self, global_state: GlobalState) -> None:
        """检测当前状态是否形成循环，并根据类型分类处理。

        Args:
            global_state: 当前全局状态

        Raises:
            UnsupportedLoopError: 检测到不支持的循环类型时抛出
        """
        from utils.exceptions import UnsupportedLoopError
        node = global_state.node
        if node is None:
            return
        current_pc = node.pc
        if current_pc in self.static_loop_headers:
            global_state.loop_time[current_pc] = global_state.loop_time[current_pc] + 1
            if global_state.loop_time[current_pc] > self.max_iteration:
                raise UnsupportedLoopError("overflow", f"Loop at {current_pc}")
        return

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
