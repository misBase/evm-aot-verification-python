"""
x86-64程序级模型。

本模块为x86-64机器码提供程序级语义，
操作整个程序（块序列）而不是单个块。
"""

from typing import List, Dict, Any, Optional, Tuple
from z3 import BitVec, BitVecVal, Concat, If, BoolVal, And, Not
from .models import X86Block, X86Instruction, Register
from .semantics import X86SemanticsModel
from .disassembler import disassemble_hex
from .cfg import build_x86_cfg, identify_basic_blocks
from state.smt_state import SMTState


class X86Program:
    """表示包含多个块的完整x86-64程序。
    
    这为整个编译的机器码序列提供程序级验证能力。
    """
    
    def __init__(self, 
                 blocks: Optional[List[X86Block]] = None,
                 hex_sequence: Optional[str] = None,
                 base_addr: int = 0):
        """初始化x86程序。
        
        Args:
            blocks: 预解析的X86Block对象列表（可选）
            hex_sequence: 十六进制编码的机器码字符串（可选）
            base_addr: 程序的基址（默认：0）
        """
        self.blocks = blocks or []
        self.hex_sequence = hex_sequence
        self.base_addr = base_addr
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
    def from_hex(cls, hex_sequence: str, base_addr: int = 0) -> 'X86Program':
        """从十六进制编码的机器码创建X86Program。
        
        Args:
            hex_sequence: 十六进制编码的机器码字符串
            base_addr: 程序的基址
            
        Returns:
            X86Program实例
        """
        return cls(hex_sequence=hex_sequence, base_addr=base_addr)
    
    @classmethod
    def from_blocks(cls, blocks: List[X86Block]) -> 'X86Program':
        """从块列表创建X86Program。
        
        Args:
            blocks: X86Block对象列表
            
        Returns:
            X86Program实例
        """
        return cls(blocks=blocks)
    
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
        from .execution_state import ExecutionState
        
        # 创建执行状态
        state = ExecutionState(initial_memory=initial_memory.copy())
        
        # 执行所有指令
        if self.instructions:
            self.semantics.executor.execute_sequence(state, self.instructions)
        else:
            # 从块中执行指令
            for block in self.blocks:
                self.semantics.executor.execute_sequence(state, block.instructions)
        
        # 从默认寄存器中提取结果（用于256位结果）
        result_registers = [Register.RBX, Register.RDX, Register.RCX, Register.RAX]
        reg_values = [state.get_register(reg) for reg in result_registers]
        semantic_formula = Concat(*reg_values)

        return {
            'output_memory': state.memory,
            'semantic_formula': semantic_formula,
            'executed_instructions': self.instructions if self.instructions else
                                    [insn for block in self.blocks for insn in block.instructions],
            'output_count': 1
        }
    
    def to_z3(self, state: SMTState) -> Tuple[SMTState, Dict[str, Any]]:
        """使用路径感知执行为整个程序构建Z3公式。
        
        此方法识别所有执行路径，符号地执行每条路径，
        并使用Z3 If表达式合并结果。
        
        Args:
            state: 已准备好输入的初始SMT状态
        
        Returns:
            (final_state, result_dict)元组，其中：
            - final_state: 程序执行后的最终SMT状态
            - result_dict: 包含合并返回值的字典（offset, length, memory, base_addr, has_return）
        """
        # 获取要执行的指令
        instructions_to_execute = self.instructions if self.instructions else []
        if not instructions_to_execute:
            # 从块中提取
            for block in self.blocks:
                instructions_to_execute.extend(block.instructions)
        
        if not instructions_to_execute:
            # 无指令：返回默认结果
            from z3 import BitVecVal
            r15_value = state.x86_registers.get_register(Register.R15)
            result = {
                'offset': BitVecVal(0, 64),
                'length': BitVecVal(0, 64),
                'memory': state.x86_memory.Memory,
                'base_addr': r15_value,
                'has_return': BoolVal(False)
            }
            return state, result
        
        # 从指令构建CFG
        cfg = build_x86_cfg(instructions_to_execute)
        
        # 查找从入口到返回块的所有路径
        entry = cfg.get_entry_block()
        terminals = cfg.get_return_blocks()
        paths = cfg.find_all_paths(entry, terminals)
        
        if not paths:
            # 回退：如果未找到路径，使用简单的顺序执行
            return self._to_z3_sequential(state, instructions_to_execute)
        
        # 执行每条路径并收集结果
        path_results = []
        for path_blocks, path_condition in paths:
            # 执行路径
            path_state = state.copy()
            
            # 按顺序执行路径中的所有指令
            for block in path_blocks:
                for insn in block.instructions:
                    path_state = insn.to_z3(path_state)
            
            # 提取此路径的结果
            from z3 import BitVecVal
            r15_value = path_state.x86_registers.get_register(Register.R15)
            has_return = path_state.return_length != BitVecVal(0, 64)
            
            path_result = {
                'offset': path_state.return_offset,
                'length': path_state.return_length,
                'memory': path_state.x86_memory.Memory,
                'base_addr': r15_value,
                'has_return': has_return
            }
            
            path_results.append((path_condition, path_result))
        
        # 使用If表达式合并所有路径结果
        merged_result = self._merge_path_results(path_results)
        
        # 创建最终状态（使用最后一条路径的状态作为基础，但结果是合并的）
        final_state = state.copy()
        final_state.return_offset = merged_result['offset']
        final_state.return_length = merged_result['length']
        final_state.x86_memory.Memory = merged_result['memory']
        # 如果需要则更新R15（尽管它通常是常量）
        
        return final_state, merged_result
    
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
            'has_return': has_return
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
        return f"X86Program(blocks={len(self.blocks)}, instructions={len(self.instructions)}, base_addr=0x{self.base_addr:x})"

