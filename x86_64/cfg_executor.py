"""
x86-64 符号执行引擎（参考 evm_ir）。

定义 X86SymbolicExecutor 类，实现 worklist 驱动的符号执行。
"""

from typing import List, Dict, Optional, Tuple
from z3 import BitVecVal, Not, Bool

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

    def manage_cfg(self, insn: X86Instruction, new_states: List[X86GlobalState]) -> None:
        """管理 CFG 构建。

        在执行过程中动态添加边。

        Args:
            insn: 当前执行的指令
            new_states: 新生成的状态
        """
        if not new_states:
            return

        # 获取当前节点的地址
        # 注意：我们需要在执行指令前获取当前地址，因为 new_states 已经指向后继节点
        # 这里需要从 global_state 中获取，但该方法签名没有提供
        # 我们需要从 new_states 反推，或者修改方法签名
        # 暂时假设所有 new_states 来自同一个前驱节点
        if not new_states[0].node:
            return

        # 实际上，我们需要从调用者传递当前节点地址
        # 这是一个设计问题，暂时注释掉 CFG 更新逻辑
        # TODO: 修复 manage_cfg 的设计，需要传递当前节点地址
        return

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

                # 更新 CFG (暂时禁用，因为设计需要修复)
                # if global_state.node and global_state.node.block.instructions:
                #     last_insn = global_state.node.block.instructions[-1]
                #     self.manage_cfg(last_insn, new_states, global_state.node.address)

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
        import copy

        # 解析跳转目标
        operands = parse_operands(insn)

        if operands.get('jump_target') is not None:
            # 直接跳转（静态目标）
            target_addr = operands['jump_target']
            target_block = self.blocks_by_addr.get(target_addr)

            if target_block is None:
                # 目标未找到，可能是外部跳转
                return []

            target_node = self.cfg.get_or_create_node(target_addr)
            new_state = X86GlobalState(
                mstate=mstate,
                world_state=copy(global_state.world_state),
                node=target_node
            )
            new_state.depth = global_state.depth + 1
            return [new_state]
        else:
            # 根据编译器实现，不应该出现间接跳转
            # 如果出现，返回空列表表示不支持
            return []

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
        import copy

        # 解析跳转目标
        operands = parse_operands(insn)
        target_addr = operands.get('jump_target')
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
            jump_world_state = copy.deepcopy(global_state.world_state)
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
            fallthrough_world_state = copy.deepcopy(global_state.world_state)
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
            当前实现存在局限性：
            - 创建的是自由变量（没有与实际 CPU 标志关联）
            - 完整实现需要从 CPU 标志寄存器（CF, ZF, SF, OF）中提取条件
            - 需要在 SMTState 或 x86_registers 中实现标志访问接口
        """
        from .models import Register

        # 映射助记符到标志
        # jl/jle/jg/jge 实际上涉及 SF 和 OF 的关系
        flag_map = {
            'jb': ('CF', True),      # CF == 1
            'jae': ('CF', False),    # CF == 0
            'je': ('ZF', True),      # ZF == 1
            'jne': ('ZF', False),    # ZF == 0
            'jl': ('SF', 'OF'),      # SF != OF
            'jle': ('ZF', 'SF'),     # ZF == 1 or SF != OF
            'jg': ('ZF', 'SF'),      # ZF == 0 and SF == OF
            'jge': ('SF', 'OF'),     # SF == OF
        }

        flag_info = flag_map.get(mnemonic, ('ZF', True))

        # TODO: 完整实现需要从 CPU 标志寄存器中提取实际条件
        # 当前简化实现：创建符号变量作为占位符
        # 这意味着约束求解时会产生自由变量，可能影响验证结果
        condition_var = Bool(f"jump_cond_{mnemonic}")

        return condition_var

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
        import copy

        # 找到下一个块
        current_idx = self.blocks.index(block)
        if current_idx + 1 >= len(self.blocks):
            # 没有下一个块，返回空列表
            return []

        next_addr = self.blocks[current_idx + 1].start_addr
        next_node = self.cfg.get_or_create_node(next_addr)

        new_state = X86GlobalState(
            mstate=mstate,
            world_state=copy(global_state.world_state),
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
