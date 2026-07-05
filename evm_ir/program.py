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
from common.path_observation import PathObservation, PathSemantics
from state.smt_state import SMTState


def _dedup_z3_exprs(exprs):
    """按 Z3 AST hash 去重，避免同一 hi-192==0 假设在多路径上重复入栈。"""
    seen = set()
    out = []
    for e in exprs:
        key = e.hash()
        if key in seen:
            continue
        seen.add(key)
        out.append(e)
    return out


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

    def _execute_paths(
        self,
        state: SMTState,
        strategy_cls: type = DFSStrategy,
        max_depth: int = 100,
        use_reachability_check: bool = True,
    ) -> List[GlobalState]:
        """Execute the EVM CFG and return terminal global states."""
        executor = SymbolicExecutor(
            blocks=self.blocks,
            strategy_cls=strategy_cls,
            max_depth=max_depth,
            use_reachability_check=use_reachability_check,
        )
        return executor.execute(state)

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
            - result_dict: 包含合并返回值的字典（offset, length, memory, has_return_data）
        """
        final_global_states = self._execute_paths(
            state,
            strategy_cls=strategy_cls,
            max_depth=max_depth,
            use_reachability_check=use_reachability_check,
        )

        if not final_global_states:
            # 没有终止状态，返回默认结果
            result = {
                'offset': BitVecVal(0, 64),
                'length': BitVecVal(0, 64),
                'memory': state.evm_memory.Memory,
                'base_addr': None,
                'has_return_data': BoolVal(False),
                'storage': state.evm_storage.Storage,
                'transient_storage': state.evm_transient_storage.TransientStorage,
                'status_code': state.error_code,
            }
            return state, result

        # 合并所有终止状态
        # 使用 If 表达式按路径条件合并
        merged_state = self._merge_global_states(final_global_states)

        # 收集各终止路径在执行中累积的 SMTState.assumptions（CALLDATALOAD 等
        # 处追加的 hi-192==0 之类无损先验），合并到 merged_state.assumptions
        # 供 program_verifier 取出后注入 refinement solver。
        collected = list(getattr(state, 'assumptions', None) or [])
        for gstate in final_global_states:
            for a in (getattr(gstate.mstate, 'assumptions', None) or []):
                collected.append(a)
        # 去重（同一个 hi-192==0 表达式可能在多条路径上同时产生）。
        merged_state.assumptions = _dedup_z3_exprs(collected) if collected else None

        # 提取结果
        has_return_data = merged_state.return_length != BitVecVal(0, 64)

        result = {
            'offset': merged_state.return_offset,
            'length': merged_state.return_length,
            'memory': merged_state.evm_memory.Memory,
            'base_addr': None,
            'has_return_data': has_return_data,
            'storage': merged_state.evm_storage.Storage,
            'transient_storage': merged_state.evm_transient_storage.TransientStorage,
            'status_code': merged_state.error_code,
        }

        return merged_state, result

    def to_z3_paths(
        self,
        state: SMTState,
        strategy_cls: type = DFSStrategy,
        max_depth: int = 100,
        use_reachability_check: bool = True,
        merge_state: bool = False,
    ) -> PathSemantics:
        """Build terminal path observations for the EVM program.

        Unlike ``to_z3()``, this keeps terminal paths separate and only builds a
        merged state when explicitly requested for debug-only stack checks.
        """
        final_global_states = self._execute_paths(
            state,
            strategy_cls=strategy_cls,
            max_depth=max_depth,
            use_reachability_check=use_reachability_check,
        )
        observations = [
            self._path_observation(gstate)
            for gstate in final_global_states
        ]
        merged_state = (
            self._merge_global_states(final_global_states)
            if merge_state and final_global_states
            else None
        )
        return PathSemantics(
            global_states=final_global_states,
            observations=observations,
            merged_state=merged_state,
        )

    def _path_observation(self, gstate: GlobalState) -> PathObservation:
        """Extract the observable result of one terminal EVM path.

        把 mstate.assumptions（CALLDATALOAD 处累积的 hi-192==0 等无损先验）
        And 进 path condition，保证 path_observations 模式下的 refinement
        check 也看到这些 precondition——否则 drop 掉的 If(offset_overflow,...)
        守卫会让 refinement 在 hi-192!=0 分支下 unsound（EVM 返 0，x86 返
        byte-wrap 值，必定 SAT 反例）。
        """
        from z3 import And
        state = gstate.mstate
        condition = gstate.get_constraints().as_bool()
        path_assumptions = getattr(state, 'assumptions', None)
        if path_assumptions:
            condition = And(condition, *path_assumptions)
        return PathObservation(
            condition=condition,
            offset=state.return_offset,
            length=state.return_length,
            memory=state.evm_memory.Memory,
            base_addr=None,
            has_return_data=state.return_length != BitVecVal(0, 64),
            storage=state.evm_storage.Storage,
            transient_storage=state.evm_transient_storage.TransientStorage,
            status_code=state.error_code,
        )

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
        # 显式 .copy() 避免共享同一 X86MemoryState 实例
        merged.x86_memory = global_states[0].mstate.x86_memory.copy()
        merged.x86_registers = global_states[0].mstate.x86_registers
        merged.evm_gas = global_states[0].mstate.evm_gas
        # 保留 create_initial_state() 注入的调试元数据。
        # 这些字段是路径不变量，后续 fixed-slot 栈检查会使用。
        merged.stack_base = global_states[0].mstate.stack_base
        merged.stack_num_inputs = global_states[0].mstate.stack_num_inputs

        # 合并 EVM storage（SLOAD/SSTORE 可能在不同路径产生不同的 storage）
        from state.smt_state import EVMStorageState, EVMTransientStorageState
        if len(global_states) == 1:
            merged.evm_storage = global_states[0].mstate.evm_storage
        else:
            first_storage = global_states[0].mstate.evm_storage.Storage
            expr = first_storage
            for gstate in reversed(global_states):
                condition = gstate.get_constraints().as_bool()
                expr = If(condition, gstate.mstate.evm_storage.Storage, expr)
            merged.evm_storage = EVMStorageState(storage_array=expr)

        # 合并 EVM transient storage（TSTORE/TLOAD 可能在不同路径产生不同的 transient storage）
        if len(global_states) == 1:
            merged.evm_transient_storage = global_states[0].mstate.evm_transient_storage
        else:
            first_ts = global_states[0].mstate.evm_transient_storage.TransientStorage
            expr = first_ts
            for gstate in reversed(global_states):
                condition = gstate.get_constraints().as_bool()
                expr = If(condition, gstate.mstate.evm_transient_storage.TransientStorage, expr)
            merged.evm_transient_storage = EVMTransientStorageState(storage_array=expr)

        # 合并 error_code
        expr = BitVecVal(0, 8)  # default 0 = RETURNED
        for gstate in reversed(global_states):
            condition = gstate.get_constraints().as_bool()
            expr = If(condition, gstate.mstate.error_code, expr)
        merged.error_code = expr


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
