"""
x86-64程序级模型。

本模块为x86-64机器码提供程序级语义，
操作整个程序（块序列）而不是单个块。

使用基于 evm_ir 设计的动态 CFG 构建和 worklist 驱动的符号执行。
"""

from typing import List, Dict, Any, Optional, Tuple
from z3 import BitVec, BitVecVal, Concat, If, BoolVal, And, Not
from .aot_profile import GO_HPC_EVM_PROFILE, X86AOTProfile
from .models import X86Block, X86Instruction, Register
from .semantics import X86SemanticsModel
from .disassembler import disassemble_hex
from .cfg import identify_basic_blocks
from .cfg_executor import X86SymbolicExecutor
from .cfg_strategies import X86DFSStrategy
from .cfg_state import X86GlobalState
from state.smt_state import SMTState


class X86Program:
    """表示包含多个块的完整x86-64程序。
    
    这为整个编译的机器码序列提供程序级验证能力。
    """
    
    def __init__(self, 
                 blocks: Optional[List[X86Block]] = None,
                 hex_sequence: Optional[str] = None,
                 base_addr: int = 0,
                 aot_profile: Optional[X86AOTProfile] = None):
        """初始化x86程序。
        
        Args:
            blocks: 预解析的X86Block对象列表（可选）
            hex_sequence: 十六进制编码的机器码字符串（可选）
            base_addr: 程序的基址（默认：0）
        """
        self.blocks = blocks or []
        self.hex_sequence = hex_sequence
        self.base_addr = base_addr
        self.aot_profile = aot_profile or GO_HPC_EVM_PROFILE
        self.semantics = X86SemanticsModel()
        
        # 如果提供了hex_sequence但没有块，则反汇编它
        if hex_sequence and not blocks:
            self.instructions = disassemble_hex(hex_sequence, base_addr=base_addr)
        else:
            self.instructions = []
            for block in self.blocks:
                self.instructions.extend(block.instructions)
        
        # 按起始地址构建块查找表
        self.blocks_by_addr: Dict[int, X86Block] = {}
        for block in self.blocks:
            self.blocks_by_addr[block.start_addr] = block
    
    @classmethod
    def from_hex(cls, hex_sequence: str, base_addr: int = 0,
                 aot_profile: Optional[X86AOTProfile] = None) -> 'X86Program':
        """从十六进制编码的机器码创建X86Program。
        
        Args:
            hex_sequence: 十六进制编码的机器码字符串
            base_addr: 程序的基址
            
        Returns:
            X86Program实例
        """
        return cls(hex_sequence=hex_sequence, base_addr=base_addr, aot_profile=aot_profile)
    
    @classmethod
    def from_blocks(cls, blocks: List[X86Block],
                    aot_profile: Optional[X86AOTProfile] = None) -> 'X86Program':
        """从块列表创建X86Program。
        
        Args:
            blocks: X86Block对象列表
            
        Returns:
            X86Program实例
        """
        return cls(blocks=blocks, aot_profile=aot_profile)
    
    def get_entrypoint(self) -> Optional[X86Block]:
        """获取程序入口点（第一个块）。
        
        Returns:
            程序中的第一个块，如果没有块则返回None
        """
        if len(self.blocks) == 0:
            return None
        return self.blocks[0]
    
    def get_block_by_addr(self, addr: int) -> Optional[X86Block]:
        """通过起始地址获取块。
        
        Args:
            addr: 块起始地址
            
        Returns:
            给定地址处的块，如果未找到则返回None
        """
        return self.blocks_by_addr.get(addr)
    
    def build_program_semantics(self, initial_memory: Dict[int, BitVec]) -> Dict[str, Any]:
        """为整个程序构建语义公式。
        
        此方法按顺序执行所有指令，构建程序行为的完整语义模型。
        
        目前，我们支持直线执行（无分支）。
        未来版本将支持控制流分析。
        
        Args:
            initial_memory: 初始内存状态（将偏移量映射到BitVec值的字典）
            
        Returns:
            包含以下内容的字典：
            - output_memory: 最终内存状态
            - semantic_formula: 程序的总体语义公式
            - executed_instructions: 已执行指令的列表
        """
        instructions = self.instructions if self.instructions else [
            insn for block in self.blocks for insn in block.instructions
        ]
        semantic_formula = self.semantics.execute_instruction_sequence(
            instructions, initial_memory
        )
        return {
            'output_memory': {},
            'semantic_formula': semantic_formula,
            'executed_instructions': instructions,
            'output_count': 1
        }
    
    def to_z3(self, state: SMTState,
             strategy_cls: type = X86DFSStrategy,
             max_depth: int = 100,
             use_reachability_check: bool = True,
             enable_go_bridge: bool = True,
             enable_merge: bool = False,
             call_site_mapping=None) -> Tuple[SMTState, Dict[str, Any]]:
        """使用 worklist 驱动的符号执行为整个程序构建Z3公式。

        参考 evm_ir 的设计：
        - 动态构建 CFG
        - 使用 work_list 管理待执行状态
        - 支持可插拔的搜索策略（DFS/BFS/BoundedLoops）
        - 支持状态注解系统
        - 可达性检查剪枝不可达状态

        Args:
            state: 已准备好输入的初始SMT状态
            strategy_cls: 搜索策略类（默认 DFS）
            max_depth: 最大执行深度
            use_reachability_check: 是否使用可达性检查
            enable_go_bridge: 是否启用 ret -> GO_HOST -> returnAddress 建模
            enable_merge: 是否启用合流点合并优化（大规模 CFG 推荐开启）

        Returns:
            (final_state, result_dict)元组，其中：
            - final_state: 程序执行后的最终SMT状态（从所有路径合并）
            - result_dict: 包含合并返回值的字典（offset, length, memory, base_addr, has_return）
        """
        # 获取要执行的指令
        instructions_to_execute = self._get_instructions()

        if not instructions_to_execute:
            # 无指令：返回默认结果
            return self._empty_result(state)

        # 识别基本块
        blocks = identify_basic_blocks(instructions_to_execute)

        if not blocks:
            # 没有块，回退到顺序执行
            return self._to_z3_sequential(state, instructions_to_execute)

        # 创建符号执行引擎
        executor = X86SymbolicExecutor(
            blocks=blocks,
            strategy_cls=strategy_cls,
            max_depth=max_depth,
            use_reachability_check=use_reachability_check,
            enable_go_bridge=enable_go_bridge,
            enable_merge=enable_merge,
            call_site_mapping=call_site_mapping,
            aot_profile=self.aot_profile,
        )

        # 执行符号执行
        final_global_states = executor.execute(state)

        if not final_global_states:
            # 没有终止状态，返回默认结果
            return self._empty_result(state)

        # 合并所有终止状态
        # 使用 If 表达式按路径条件合并
        merged_state = self._merge_global_states(final_global_states)

        # 提取结果
        r15_value = merged_state.x86_registers.get_register(Register.R15)
        has_return = merged_state.return_length != BitVecVal(0, 64)

        result = {
            'offset': merged_state.return_offset,
            'length': merged_state.return_length,
            'memory': merged_state.x86_memory.Memory,
            'base_addr': r15_value,
            'has_return': has_return,
            'storage': merged_state.evm_storage.Storage,
            'transient_storage': merged_state.evm_transient_storage.TransientStorage,
        }

        return merged_state, result

    def _get_instructions(self) -> List[X86Instruction]:
        """获取要执行的指令列表。

        Returns:
            指令列表
        """
        if self.instructions:
            return self.instructions
        result = []
        for block in self.blocks:
            result.extend(block.instructions)
        return result

    def _empty_result(self, state: SMTState) -> Tuple[SMTState, Dict[str, Any]]:
        """返回空结果（无指令时）。

        Args:
            state: 初始SMT状态

        Returns:
            (final_state, result_dict)元组
        """
        r15_value = state.x86_registers.get_register(Register.R15)
        result = {
            'offset': BitVecVal(0, 64),
            'length': BitVecVal(0, 64),
            'memory': state.x86_memory.Memory,
            'base_addr': r15_value,
            'has_return': BoolVal(False),
            'storage': state.evm_storage.Storage,
            'transient_storage': state.evm_transient_storage.TransientStorage,
        }
        return state, result

    def _merge_global_states(self, global_states: List[X86GlobalState]) -> SMTState:
        """合并所有全局状态的机器状态。

        使用嵌套 If 表达式合并所有路径的结果。

        Args:
            global_states: X86GlobalState 列表

        Returns:
            合并后的 SMTState
        """
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

        # 合并 callEngine side-channel 字段（与 return_offset/length 同模式）
        callengine_states = [gstate.mstate for gstate in global_states]
        callengine_conditions = [gstate.get_constraints().as_bool() for gstate in global_states]
        SMTState.merge_callengine_side_channels(
            merged,
            callengine_states,
            callengine_conditions,
        )

        # 合并 x86 内存
        first_memory = global_states[0].mstate.x86_memory.Memory
        expr = first_memory
        for gstate in reversed(global_states):
            condition = gstate.get_constraints().as_bool()
            expr = If(condition, gstate.mstate.x86_memory.Memory, expr)
        merged.x86_memory.Memory = expr

        # 合并寄存器 (RBX, RDX, RCX, RAX)
        for reg in [Register.RBX, Register.RDX, Register.RCX, Register.RAX]:
            first_val = global_states[0].mstate.x86_registers.get_register(reg)
            expr = first_val
            for gstate in reversed(global_states):
                condition = gstate.get_constraints().as_bool()
                expr = If(condition, gstate.mstate.x86_registers.get_register(reg), expr)
            merged.x86_registers.set_register(reg, expr)

        # 合并 R15（基址寄存器）
        first_r15 = global_states[0].mstate.x86_registers.get_register(Register.R15)
        expr = first_r15
        for gstate in reversed(global_states):
            condition = gstate.get_constraints().as_bool()
            expr = If(condition, gstate.mstate.x86_registers.get_register(Register.R15), expr)
        merged.x86_registers.set_register(Register.R15, expr)

        # 合并 EVM storage（Go函数调用可能修改storage）
        from state.smt_state import EVMStorageState, EVMTransientStorageState
        first_storage = global_states[0].mstate.evm_storage.Storage
        expr = first_storage
        for gstate in reversed(global_states):
            condition = gstate.get_constraints().as_bool()
            expr = If(condition, gstate.mstate.evm_storage.Storage, expr)
        merged.evm_storage = EVMStorageState(storage_array=expr)

        # 合并 EVM transient storage
        first_ts = global_states[0].mstate.evm_transient_storage.TransientStorage
        expr = first_ts
        for gstate in reversed(global_states):
            condition = gstate.get_constraints().as_bool()
            expr = If(condition, gstate.mstate.evm_transient_storage.TransientStorage, expr)
        merged.evm_transient_storage = EVMTransientStorageState(storage_array=expr)

        # 保留 create_initial_state() 注入的调试元数据。
        merged.stack_base = global_states[0].mstate.stack_base
        merged.stack_num_inputs = global_states[0].mstate.stack_num_inputs

        return merged
    
    def _to_z3_sequential(self, state: SMTState, instructions: List[X86Instruction]) -> Tuple[SMTState, Dict[str, Any]]:
        """回退：无路径分析的顺序执行。
        
        Args:
            state: 初始SMT状态
            instructions: 要执行的指令
            
        Returns:
            (final_state, result_dict)元组
        """
        # 处理每条指令
        for insn in instructions:
            state = insn.to_z3(state)
        
        # 提取结果
        from z3 import BitVecVal
        r15_value = state.x86_registers.get_register(Register.R15)
        has_return = state.return_length != BitVecVal(0, 64)
        
        result = {
            'offset': state.return_offset,
            'length': state.return_length,
            'memory': state.x86_memory.Memory,
            'base_addr': r15_value,
            'has_return': has_return,
            'storage': state.evm_storage.Storage,
            'transient_storage': state.evm_transient_storage.TransientStorage,
        }

        return state, result

    def _merge_path_results(self, path_results: List[Tuple[Any, Dict[str, Any]]]) -> Dict[str, Any]:
        """使用嵌套If表达式合并路径结果。
        
        Args:
            path_results: (condition, result_dict)元组列表
            
        Returns:
            合并的结果字典
        """
        if not path_results:
            # 如果没有路径，返回默认结果
            from z3 import BitVecVal
            from .models import Register
            r15_default = BitVecVal(0, 64)  # 默认R15值
            return {
                'offset': BitVecVal(0, 64),
                'length': BitVecVal(0, 64),
                'memory': None,  # 将由调用者设置
                'base_addr': r15_default,
                'has_return': BoolVal(False)
            }
        
        if len(path_results) == 1:
            # 单条路径：返回其结果
            _, result = path_results[0]
            return result
        
        # 为每个字段构建嵌套If表达式
        def build_nested_if(field_name: str, default_value):
            """为字段构建嵌套If表达式。"""
            expr = default_value
            # 从后往前构建（右结合）
            for i in range(len(path_results) - 1, -1, -1):
                condition, result = path_results[i]
                field_value = result.get(field_name, default_value)
                expr = If(condition, field_value, expr)
            return expr
        
        from z3 import BitVecVal, Array
        from state.smt_state import X86MemoryState
        from .models import Register
        
        # 从第一条路径结果获取内存数组类型
        first_memory = path_results[0][1]['memory']
        if first_memory is None:
            # 创建默认内存数组
            mem_state = X86MemoryState()
            first_memory = mem_state.Memory
        
        # 获取默认base_addr
        first_base_addr = path_results[0][1].get('base_addr', BitVecVal(0, 64))
        
        # 合并每个字段
        merged_offset = build_nested_if('offset', BitVecVal(0, 64))
        merged_length = build_nested_if('length', BitVecVal(0, 64))
        merged_memory = build_nested_if('memory', first_memory)
        merged_base_addr = build_nested_if('base_addr', first_base_addr)
        merged_has_return = build_nested_if('has_return', BoolVal(False))
        
        return {
            'offset': merged_offset,
            'length': merged_length,
            'memory': merged_memory,
            'base_addr': merged_base_addr,
            'has_return': merged_has_return
        }
    
    def __repr__(self):
        info = f"instructions={len(self.instructions)}, base_addr=0x{self.base_addr:x}"
        if self.blocks:
            entry_addr = self.blocks[0].start_addr
            info = f"blocks={len(self.blocks)}, entry_addr=0x{entry_addr:x}, " + info
        else:
            info = f"blocks=0 (sequential), " + info
        return f"X86Program({info})"
