"""
x86-64 符号执行引擎（参考 evm_ir）。

定义 X86SymbolicExecutor 类，实现 worklist 驱动的符号执行。
"""

from typing import List, Dict, Optional, Tuple
from z3 import BitVecVal, Not, And, Or

from .models import X86Block, X86Instruction
from .cfg_structures import X86DynamicCFG, X86EdgeType
from .cfg_state import X86GlobalState
from .cfg_strategies import X86DFSStrategy
from .disassembler import parse_operands
from state.smt_state import SMTState


class X86SymbolicExecutor:
    """基于 worklist 的 x86-64 符号执行引擎。

    完全参考 evm_ir 的设计：
    - work_list 管理待执行状态
    - 动态构建 CFG
    - 策略模式控制搜索顺序
    - 可达性检查剪枝不可达状态
    """

    def __init__(self,
                 blocks: List[X86Block],
                 strategy_cls: type = X86DFSStrategy,
                 max_depth: int = 100,
                 use_reachability_check: bool = True):
        """初始化符号执行引擎。

        Args:
            blocks: 所有 x86-64 块列表
            strategy_cls: 搜索策略类
            max_depth: 最大执行深度
            use_reachability_check: 是否使用可达性检查
        """
        self.blocks = blocks
        self.blocks_by_addr: Dict[int, X86Block] = {block.start_addr: block for block in blocks}
        self.max_depth = max_depth
        self.use_reachability_check = use_reachability_check

        # 创建动态 CFG
        self.cfg = X86DynamicCFG(blocks)

        # work_list：待执行的全局状态列表
        self.work_list: List[X86GlobalState] = []

        # 创建搜索策略
        self.strategy = strategy_cls(self.work_list, max_depth)

        # 统计信息
        self.total_states = 0
        self.pruned_states = 0

        # 终止状态列表
        self.final_states: List[X86GlobalState] = []

    def manage_cfg(self, insn: X86Instruction, new_states: List[X86GlobalState],
                   from_addr: int) -> None:
        """管理 CFG 构建。

        在执行过程中动态添加边。

        Args:
            insn: 当前执行的指令
            new_states: 新生成的状态列表
            from_addr: 前驱节点地址（当前块地址）
        """
        if not new_states:
            return

        mnemonic = insn.mnemonic.lower()

        if mnemonic == 'jmp':
            # 无条件跳转：添加单条边
            if len(new_states) == 1 and new_states[0].node:
                to_addr = new_states[0].node.address
                self.cfg.add_edge(from_addr, to_addr, X86EdgeType.UNCONDITIONAL,
                                source_instruction=insn)

        elif mnemonic in ['jb', 'jae', 'je', 'jne', 'jl', 'jle', 'jg', 'jge']:
            # 条件跳转：添加两条边（跳转和 fallthrough）
            for i, state in enumerate(new_states):
                if not state.node:
                    continue
                to_addr = state.node.address

                # 第一个状态是跳转分支，第二个是 fallthrough
                if i == 0:
                    edge_type = X86EdgeType.CONDITIONAL_TRUE
                    # 从状态约束中提取条件
                    condition = self._extract_jcc_condition(state)
                else:
                    edge_type = X86EdgeType.CONDITIONAL_FALSE
                    condition = None  # fallthrough 条件是跳转条件的否定，在边类型中体现

                self.cfg.add_edge(from_addr, to_addr, edge_type, condition,
                                source_instruction=insn)

        else:
            # Fallthrough：添加顺序执行边
            if len(new_states) == 1 and new_states[0].node:
                to_addr = new_states[0].node.address
                self.cfg.add_edge(from_addr, to_addr, X86EdgeType.FALLTHROUGH,
                                source_instruction=insn)

    def execute(self, initial_state: SMTState, entry_addr: Optional[int] = None) -> List[X86GlobalState]:
        """执行符号执行。

        Args:
            initial_state: 初始机器状态
            entry_addr: 入口块地址（默认为第一个块）

        Returns:
            所有终止状态列表
        """
        # 确定入口点
        if entry_addr is None:
            if not self.blocks:
                raise ValueError("No blocks to execute")
            entry_addr = self.blocks[0].start_addr

        entry_block = self.blocks_by_addr.get(entry_addr)
        if entry_block is None:
            raise ValueError(f"Entry block not found: addr=0x{entry_addr:x}")

        # 创建初始全局状态
        entry_node = self.cfg.get_or_create_node(entry_addr)
        initial_global_state = X86GlobalState(
            mstate=initial_state,
            node=entry_node
        )
        initial_global_state.depth = 0

        # 添加到 work_list
        self.work_list.append(initial_global_state)

        # 主执行循环
        for global_state in self.strategy:
            # 循环检测调用点（TODO: 实现检测逻辑）
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
                if global_state.node and global_state.node.block.instructions:
                    last_insn = global_state.node.block.instructions[-1]
                    from_addr = global_state.node.address
                    self.manage_cfg(last_insn, new_states, from_addr)

                # 添加新状态到 work_list
                self.work_list.extend(new_states)
                self.total_states += len(new_states)

            # 如果是终止状态，保存
            if self._is_terminal_state(global_state):
                self.final_states.append(global_state)

        return self.final_states

    def execute_state(self, global_state: X86GlobalState) -> List[X86GlobalState]:
        """执行单个全局状态。

        Args:
            global_state: 要执行的全局状态

        Returns:
            新生成的全局状态列表
        """
        node = global_state.node
        if node is None:
            return []

        # 将当前状态添加到节点的状态列表（用于追踪和调试）
        node.states.append(global_state)

        block = node.block
        mstate = global_state.mstate

        # 执行块中的所有指令
        new_mstate = mstate.copy()

        for insn in block.instructions:
            new_mstate = insn.to_z3(new_mstate)

        # 获取最后一条指令来确定控制流
        if not block.instructions:
            # 空块，顺序执行到下一个块
            return self._handle_fallthrough(global_state, new_mstate, block)

        last_insn = block.instructions[-1]
        mnemonic = last_insn.mnemonic.lower()

        if mnemonic == 'jmp':
            return self._handle_jmp(global_state, new_mstate, block, last_insn)
        elif mnemonic in ['jb', 'jae', 'je', 'jne', 'jl', 'jle', 'jg', 'jge']:
            return self._handle_jcc(global_state, new_mstate, block, last_insn)
        elif mnemonic == 'ret':
            return []  # 终止状态
        else:
            # 顺序执行到下一个块
            return self._handle_fallthrough(global_state, new_mstate, block)

    def _handle_jmp(self, global_state: X86GlobalState, mstate: SMTState,
                    block: X86Block, insn: X86Instruction) -> List[X86GlobalState]:
        """处理 JMP 指令。

        Args:
            global_state: 当前全局状态
            mstate: 执行后的机器状态
            block: 当前块
            insn: JMP 指令

        Returns:
            新全局状态列表

        Note:
            根据编译器实现，机器码中没有间接跳转，
            所有跳转目标都是静态确定的。
        """
        import copy as copy_module

        # 解析跳转目标
        operands = parse_operands(insn)

        target_addr = operands.get('jump_target')
        
        if target_addr is None:
            # 无法解析目标，可能是间接跳转或解析错误
            # 检查是否是明确的间接跳转（寄存器/内存跳转）
            if operands.get('is_indirect'):
                from utils.exceptions import UnsupportedJumpError
                raise UnsupportedJumpError(
                    "indirect_jump",
                    f"Indirect JMP at address 0x{insn.addr:x}",
                    "x86 indirect jumps are not supported by the compiler"
                )
            # 否则返回空列表（可能是解析失败或外部目标）
            return []

        # 直接跳转（静态目标）
        target_block = self.blocks_by_addr.get(target_addr)

        if target_block is None:
            # 目标块不存在，可能是外部跳转或超出范围
            return []

        target_node = self.cfg.get_or_create_node(target_addr)
        new_state = X86GlobalState(
            mstate=mstate,
            world_state=copy_module.copy(global_state.world_state),  # 单路径使用 copy（参考 mythril）
            node=target_node
        )
        new_state.depth = global_state.depth + 1
        return [new_state]

    def _handle_jcc(self, global_state: X86GlobalState, mstate: SMTState,
                    block: X86Block, insn: X86Instruction) -> List[X86GlobalState]:
        """处理条件跳转指令（Jcc）。

        支持的条件跳转指令：
        - JE/JNE: 等于/不等于
        - JB/JAE: 无符号小于/大于等于
        - JL/JGE: 有符号小于/大于等于
        - JLE/JG: 有符号小于等于/大于

        Args:
            global_state: 当前全局状态
            mstate: 执行后的机器状态
            block: 当前块
            insn: Jcc 指令

        Returns:
            新全局状态列表（两个分支）

        Note:
            根据编译器实现：
            - 所有跳转目标都是静态确定的
            - 没有间接跳转
        """
        import copy as copy_module

        # 解析跳转目标
        operands = parse_operands(insn)
        target_addr = operands.get('jump_target')
        
        # 检测间接跳转（真正的间接寻址）
        if target_addr is None:
            # 检查是否是明确的间接跳转
            if operands.get('is_indirect'):
                from utils.exceptions import UnsupportedJumpError
                raise UnsupportedJumpError(
                    "indirect_conditional_jump",
                    f"Indirect conditional jump at address 0x{insn.addr:x}",
                    "x86 indirect conditional jumps are not supported by the compiler"
                )
            # 如果只是解析失败，目标块设为 None（后续处理会跳过该分支）
        
        target_block = self.blocks_by_addr.get(target_addr) if target_addr else None

        mnemonic = insn.mnemonic.lower()

        # 构建跳转条件
        # 注意：当前实现使用符号变量作为占位符
        # 完整实现需要从 CPU 标志寄存器（CF, ZF, SF, OF）中提取条件
        jump_condition = self._build_jump_condition(mnemonic, mstate)
        fallthrough_condition = Not(jump_condition)

        new_states = []

        # 分支 1：跳转到目标（条件为真）
        if target_block is not None:
            target_node = self.cfg.get_or_create_node(target_addr)

            # 深拷贝状态
            jump_world_state = copy_module.deepcopy(global_state.world_state)
            jump_world_state.constraints.add(jump_condition)

            jump_state = X86GlobalState(
                mstate=mstate.copy(),
                world_state=jump_world_state,
                node=target_node
            )
            jump_state.depth = global_state.depth + 1
            new_states.append(jump_state)

        # 分支 2：顺序执行（条件为假）
        current_idx = self.blocks.index(block)
        if current_idx + 1 < len(self.blocks):
            fallthrough_addr = self.blocks[current_idx + 1].start_addr
            fallthrough_node = self.cfg.get_or_create_node(fallthrough_addr)

            # 深拷贝状态
            fallthrough_world_state = copy_module.deepcopy(global_state.world_state)
            fallthrough_world_state.constraints.add(fallthrough_condition)

            fallthrough_state = X86GlobalState(
                mstate=mstate.copy(),
                world_state=fallthrough_world_state,
                node=fallthrough_node
            )
            fallthrough_state.depth = global_state.depth + 1
            new_states.append(fallthrough_state)

        return new_states

    def _build_jump_condition(self, mnemonic: str, mstate: SMTState):
        """为条件跳转构建符号条件。

        Args:
            mnemonic: 指令助记符（jb、jae等）
            mstate: 机器状态

        Returns:
            符号条件（BoolRef）

        Note:
            从 CPU 标志寄存器（CF, ZF, SF, OF）中提取实际条件。
            标志位是 1 位 BitVec，使用 == 运算符比较得到 BoolRef。
        """
        # 获取 CPU 标志位（1 位 BitVec）
        cf = mstate.x86_registers.get_flag('CF')
        zf = mstate.x86_registers.get_flag('ZF')
        sf = mstate.x86_registers.get_flag('SF')
        of = mstate.x86_registers.get_flag('OF')

        # 将 1 位 BitVec 转换为 BoolRef
        # (flag == BitVecVal(1, 1)) 返回 BoolRef
        cf_true = (cf == BitVecVal(1, 1))
        cf_false = (cf == BitVecVal(0, 1))
        zf_true = (zf == BitVecVal(1, 1))
        zf_false = (zf == BitVecVal(0, 1))
        sf_eq_of = (sf == of)
        sf_ne_of = Not(sf == of)

        # 根据助记符构建条件
        # jl/jle/jg/jge 涉及 SF 和 OF 的关系
        conditions = {
            'jb': cf_true,           # CF == 1 (无符号小于)
            'jae': cf_false,         # CF == 0 (无符号大于等于)
            'je': zf_true,           # ZF == 1 (等于)
            'jne': zf_false,         # ZF == 0 (不等于)
            'jl': sf_ne_of,          # SF != OF (有符号小于)
            'jle': Or(zf_true, sf_ne_of),  # ZF == 1 or SF != OF (有符号小于等于)
            'jg': And(zf_false, sf_eq_of),  # ZF == 0 and SF == OF (有符号大于)
            'jge': sf_eq_of,         # SF == OF (有符号大于等于)
        }

        return conditions.get(mnemonic, zf_true)

    def _extract_jcc_condition(self, state: X86GlobalState):
        """从状态中提取 Jcc 条件（用于 CFG 边）。

        Args:
            state: 全局状态

        Returns:
            条件 BoolRef 或 None
        """
        from z3 import BoolVal, eq, And
        
        constraints = state.get_constraints()
        
        # 过滤掉初始的 True 约束，只获取实际添加的约束
        real_constraints = [
            c for c in constraints 
            if not (isinstance(c, type(BoolVal(True))) and eq(c, BoolVal(True)))
        ]
        
        if real_constraints:
            # 返回最后一个添加的约束（即跳转条件）
            return real_constraints[-1]
        
        # 如果没有实际约束，检查 flag_constraints
        if hasattr(constraints, 'flag_constraints'):
            flag_constraints = constraints.flag_constraints
            if flag_constraints:
                # 返回合并的标志约束
                return And(*flag_constraints.values())
        
        # 如果没有任何约束，返回最后一个约束（可能是初始的 True）
        if len(constraints) > 0:
            return list(constraints)[-1]
        
        return None

    def _handle_fallthrough(self, global_state: X86GlobalState, mstate: SMTState,
                           block: X86Block) -> List[X86GlobalState]:
        """处理顺序执行（fallthrough）。

        Args:
            global_state: 当前全局状态
            mstate: 执行后的机器状态
            block: 当前块

        Returns:
            新全局状态列表
        """
        import copy as copy_module

        # 找到下一个块
        current_idx = self.blocks.index(block)
        if current_idx + 1 >= len(self.blocks):
            # 没有下一个块，返回空列表
            return []

        next_addr = self.blocks[current_idx + 1].start_addr
        next_node = self.cfg.get_or_create_node(next_addr)

        new_state = X86GlobalState(
            mstate=mstate,
            world_state=copy_module.copy(global_state.world_state),
            node=next_node
        )
        new_state.depth = global_state.depth + 1

        return [new_state]

    def _is_terminal_state(self, global_state: X86GlobalState) -> bool:
        """检查是否是终止状态。

        Args:
            global_state: 全局状态

        Returns:
            如果是终止状态则返回 True
        """
        node = global_state.node
        if node is None or not node.block.instructions:
            return False

        last_insn = node.block.instructions[-1]
        return last_insn.mnemonic.lower() == 'ret'

    def _detect_and_handle_loops(self, global_state: X86GlobalState) -> None:
        """检测当前状态是否形成循环，并根据类型分类处理。

        TODO: 实现循环检测逻辑
        - 地址重复检测
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

    def _classify_loop(self, loop_addr: int, path_context: Dict) -> str:
        """判断循环类型。

        TODO: 实现循环分类逻辑
        - 静态有界：检查循环条件是否为常量比较
        - 动态有界：条件与符号变量比较
        - 无界：无法确定循环边界

        Args:
            loop_addr: 循环头的地址
            path_context: 执行路径上下文信息

        Returns:
            "static_bounded" | "dynamic_bounded" | "unbounded"
        """
        # TODO: 实现循环分类
        return "dynamic_bounded"  # 默认返回


def build_x86_dynamic_cfg(blocks: List[X86Block],
                          initial_state: SMTState,
                          strategy_cls: type = X86DFSStrategy,
                          max_depth: int = 100) -> Tuple[List[X86GlobalState], X86DynamicCFG]:
    """构建动态 CFG 并执行符号执行。

    Args:
        blocks: x86-64 块列表
        initial_state: 初始机器状态
        strategy_cls: 搜索策略类
        max_depth: 最大执行深度

    Returns:
        (final_states, cfg) 元组
    """
    executor = X86SymbolicExecutor(blocks, strategy_cls=strategy_cls, max_depth=max_depth)
    final_states = executor.execute(initial_state)
    return final_states, executor.cfg
