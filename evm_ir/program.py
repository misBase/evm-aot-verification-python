"""
EVM IR程序级模型。

本模块为EVM IR提供程序级语义，操作整个程序（块序列）而不是单个块。

使用基于 mythril 设计的动态 CFG 构建和 worklist 驱动的符号执行。
"""

from typing import List, Dict, Any, Optional, Tuple
from z3 import BitVecVal, If, BoolVal
from .models import EVMBlock
from .semantics import EVMIRSemantics
from .json_parser import CompilerEVMResult
from .cfg import SymbolicExecutor, DFSStrategy, BFSStrategy, GlobalState
from state.smt_state import SMTState


class EVMProgram:
    """表示包含多个块的完整EVM程序。

    这包装了CompilerEVMResult并为整个IR序列提供程序级验证能力。
    """

    def __init__(self, compiler_result: CompilerEVMResult):
        """初始化EVM程序。

        Args:
            compiler_result: 包含所有块的编译结果
        """
        self.compiler_result = compiler_result
        self.blocks = compiler_result.blocks
        self.semantics = EVMIRSemantics()

        # 按PC构建块查找表
        self.blocks_by_pc: Dict[int, EVMBlock] = {}
        for block in self.blocks:
            self.blocks_by_pc[block.pc] = block

    def get_entrypoint(self) -> EVMBlock:
        """获取程序入口点（第一个块）。

        Returns:
            程序中的第一个块（入口点）
        """
        if len(self.blocks) == 0:
            raise ValueError("Program has no blocks")
        return self.blocks[0]

    def get_block_by_pc(self, pc: int) -> Optional[EVMBlock]:
        """通过PC值获取块。

        Args:
            pc: 程序计数器值

        Returns:
            给定PC处的块，如果未找到则返回None
        """
        return self.blocks_by_pc.get(pc)

    def to_z3(self, state: SMTState,
             strategy_cls: type = DFSStrategy,
             max_depth: int = 100,
             use_reachability_check: bool = True) -> Tuple[SMTState, Dict[str, Any]]:
        """使用 worklist 驱动的符号执行为整个程序构建Z3公式。

        参考 mythril 的设计：
        - 动态构建 CFG
        - 使用 work_list 管理待执行状态
        - 支持可插拔的搜索策略（DFS/BFS/BoundedLoops）
        - 支持状态注释系统
        - 可达性检查剪枝不可达状态

        Args:
            state: 已准备好输入的初始SMT状态
            strategy_cls: 搜索策略类（默认 DFS）
            max_depth: 最大执行深度
            use_reachability_check: 是否使用可达性检查

        Returns:
            (final_state, result_dict)元组，其中：
            - final_state: 程序执行后的最终SMT状态（从所有路径合并）
            - result_dict: 包含合并返回值的字典（offset, length, memory, has_return）
        """
        # 创建符号执行引擎
        executor = SymbolicExecutor(
            blocks=self.blocks,
            strategy_cls=strategy_cls,
            max_depth=max_depth,
            use_reachability_check=use_reachability_check
        )

        # 执行符号执行
        final_global_states = executor.execute(state)

        if not final_global_states:
            # 没有终止状态，返回默认结果
            result = {
                'offset': BitVecVal(0, 64),
                'length': BitVecVal(0, 64),
                'memory': state.evm_memory.Memory,
                'base_addr': None,
                'has_return': BoolVal(False),
                'storage': state.evm_storage.Storage,
            }
            return state, result

        # 合并所有终止状态
        # 使用 If 表达式按路径条件合并
        merged_state = self._merge_global_states(final_global_states)

        # 提取结果
        has_return = merged_state.return_length != BitVecVal(0, 64)

        result = {
            'offset': merged_state.return_offset,
            'length': merged_state.return_length,
            'memory': merged_state.evm_memory.Memory,
            'base_addr': None,
            'has_return': has_return,
            'storage': merged_state.evm_storage.Storage,
        }

        return merged_state, result

    def _merge_global_states(self, global_states: List[GlobalState]) -> SMTState:
        """合并所有全局状态的机器状态。

        使用嵌套 If 表达式合并所有路径的结果。

        Args:
            global_states: GlobalState 列表

        Returns:
            合并后的 SMTState
        """
        from z3 import BitVecVal

        if not global_states:
            # 空列表，返回空状态
            return SMTState()

        if len(global_states) == 1:
            # 单一路径，直接返回机器状态
            return global_states[0].mstate

        # 多条路径，使用 If 表达式合并
        # 从后往前构建嵌套 If
        merged = SMTState()

        # 合并 return_offset
        expr = BitVecVal(0, 64)
        for gstate in reversed(global_states):
            condition = gstate.get_constraints().as_bool()
            expr = If(condition, gstate.mstate.return_offset, expr)
        merged.return_offset = expr

        # 合并 return_length
        expr = BitVecVal(0, 64)
        for gstate in reversed(global_states):
            condition = gstate.get_constraints().as_bool()
            expr = If(condition, gstate.mstate.return_length, expr)
        merged.return_length = expr

        # 合并 EVM 内存
        first_memory = global_states[0].mstate.evm_memory.Memory
        expr = first_memory
        for gstate in reversed(global_states):
            condition = gstate.get_constraints().as_bool()
            expr = If(condition, gstate.mstate.evm_memory.Memory, expr)
        merged.evm_memory.Memory = expr
        # 合并 MSize
        first_msize = global_states[0].mstate.evm_memory.MSize
        expr = first_msize
        for gstate in reversed(global_states):
            condition = gstate.get_constraints().as_bool()
            expr = If(condition, gstate.mstate.evm_memory.MSize, expr)
        merged.evm_memory.MSize = expr

        # 合并 EVM 栈
        first_stack = global_states[0].mstate.evm_stack.Stack
        expr = first_stack
        for gstate in reversed(global_states):
            condition = gstate.get_constraints().as_bool()
            expr = If(condition, gstate.mstate.evm_stack.Stack, expr)
        merged.evm_stack.Stack = expr

        # 合并 SP
        first_sp = global_states[0].mstate.evm_stack.SP
        expr = first_sp
        for gstate in reversed(global_states):
            condition = gstate.get_constraints().as_bool()
            expr = If(condition, gstate.mstate.evm_stack.SP, expr)
        merged.evm_stack.SP = expr

        # 合并其他字段（x86、storage、gas 等）
        merged.x86_memory = global_states[0].mstate.x86_memory
        merged.x86_registers = global_states[0].mstate.x86_registers
        merged.evm_gas = global_states[0].mstate.evm_gas

        # 合并 EVM storage（SLOAD/SSTORE 可能在不同路径产生不同的 storage）
        from state.smt_state import EVMStorageState
        if len(global_states) == 1:
            merged.evm_storage = global_states[0].mstate.evm_storage
        else:
            first_storage = global_states[0].mstate.evm_storage.Storage
            expr = first_storage
            for gstate in reversed(global_states):
                condition = gstate.get_constraints().as_bool()
                expr = If(condition, gstate.mstate.evm_storage.Storage, expr)
            merged.evm_storage = EVMStorageState(storage_array=expr)

        return merged

    def __repr__(self):
        blocks_info = f"blocks={len(self.blocks)}"
        if self.blocks:
            entry_pc = self.blocks[0].pc
            blocks_info += f", entry_pc=0x{entry_pc:x}"
            # 统计操作数
            total_ops = sum(len(block.operations) for block in self.blocks)
            blocks_info += f", operators={total_ops}"
        return f"EVMProgram({blocks_info})"
