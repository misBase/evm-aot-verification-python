"""
EVM IR程序级模型。

本模块为EVM IR提供程序级语义，操作整个程序（块序列）而不是单个块。
"""

from typing import List, Dict, Any, Optional, Tuple, Set
from z3 import BitVec, BitVecVal, Solver, If, BoolVal, And
from .models import EVMBlock
from .semantics import EVMIRSemantics, execute_block_with_tag
from .json_parser import CompilerEVMResult
from .cfg import build_ir_cfg, IRCFG
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
    
    def to_z3(self, state: SMTState) -> Tuple[SMTState, Dict[str, Any]]:
        """使用基于CFG的符号执行为整个程序构建Z3公式。
        
        此方法使用符号执行而不是路径枚举：
        - 级别1：使用TAG路径合并执行每个块（每个块3条路径）
        - 级别2：执行基于CFG的符号执行，使用If表达式合并分支
        
        Args:
            state: 已准备好输入的初始SMT状态
        
        Returns:
            (final_state, result_dict)元组，其中：
            - final_state: 程序执行后的最终SMT状态（从所有路径合并）
            - result_dict: 包含合并返回值的字典（offset, length, memory, has_return）
        """
        # 构建CFG
        cfg = build_ir_cfg(self.blocks)
        
        # 验证循环（检测并拒绝不支持的循环）
        try:
            cfg.validate_loops()
        except Exception as e:
            # 重新抛出异常（可能是UnsupportedLoopError）
            raise e
        
        # 获取入口和终止块
        entry = cfg.get_entry_block()
        terminals = cfg.get_terminal_blocks()
        
        # 符号执行：从入口开始，使用If表达式合并分支
        merged_state = self._execute_symbolic_with_cfg(
            entry, state, cfg, terminals
        )
        
        # 从合并状态中提取结果
        from z3 import BitVecVal
        has_return = merged_state.return_length != BitVecVal(0, 64)
        
        result = {
            'offset': merged_state.return_offset,
            'length': merged_state.return_length,
            'memory': merged_state.evm_memory.Memory,
            'base_addr': None,
            'has_return': has_return
        }
        
        return merged_state, result
    
    def _to_z3_sequential(self, state: SMTState) -> Tuple[SMTState, Dict[str, Any]]:
        """回退：无路径分析的顺序执行。
        
        Args:
            state: 初始SMT状态
        
        Returns:
            (final_state, result_dict)元组
        """
        # 按顺序处理所有块
        for block in self.blocks:
            # 使用TAG路径合并执行块（级别1）
            state, _ = execute_block_with_tag(block, state)
            
            # 检查块是否以终止指令结束
            if block.operations:
                last_op = block.operations[-1]
                if last_op.kind.upper() in ['STOP', 'RETURN', 'REVERT', 'SELFDESTRUCT']:
                    break
        
        # 提取结果
        from z3 import BitVecVal
        has_return = state.return_length != BitVecVal(0, 64)
        
        result = {
            'offset': state.return_offset,
            'length': state.return_length,
            'memory': state.evm_memory.Memory,
            'base_addr': None,
            'has_return': has_return
        }
        
        return state, result
    
    def _execute_symbolic_with_cfg(
        self, 
        start_block: EVMBlock, 
        state: SMTState, 
        cfg: IRCFG,
        terminals: List[EVMBlock],
        visited: Optional[Set[int]] = None
    ) -> SMTState:
        """基于CFG的符号执行：遇到分支时使用If表达式合并分支。
        
        这不是路径枚举，而是：
        - 遇到条件分支时，递归执行两个分支，然后使用If表达式合并
        - 使用CFG的后继信息指导执行方向
        
        Args:
            start_block: 起始块
            state: 当前状态
            cfg: 控制流图
            terminals: 终止块列表
            visited: 已访问的块PC集合（用于循环检测）
        
        Returns:
            合并后的状态（通过If表达式包含所有可能路径的信息）
        """
        from z3 import BoolVal
        
        if visited is None:
            visited = set()
        
        # 检测循环：如果块已在visited中，我们检测到了循环
        if start_block.pc in visited:
            # 这是一个循环！目前，我们将抛出错误
            # 将来，我们可以通过展开来处理静态有界循环
            raise ValueError(
                f"Loop detected while executing block PC={start_block.pc}. "
                "Loop detection should be completed via validate_loops() before symbolic execution."
            )
        
        visited.add(start_block.pc)
        
        # 执行当前块（级别1：TAG路径合并）
        executed_state, _ = execute_block_with_tag(start_block, state)
        
        # 检查这是否是终止块
        if start_block in terminals:
            # 到达终止块：返回当前状态（已包含所有路径信息）
            return executed_state
        
        # 获取后继块
        successors = cfg.get_successors(start_block)
        
        if len(successors) == 0:
            # 无后继：返回当前状态
            return executed_state
        
        elif len(successors) == 1:
            # 无条件跳转或顺序执行：继续到下一个块
            next_block = successors[0]
            return self._execute_symbolic_with_cfg(
                next_block, executed_state, cfg, terminals, visited.copy()
            )
        
        elif len(successors) == 2:
            # 条件跳转（JUMPI）：递归执行两个分支，然后使用If合并
            # 假设successors[0]是跳转目标，successors[1]是顺序执行
            jump_target = successors[0]
            fallthrough_target = successors[1]
            
            # 从JUMPI指令中提取条件
            # 注意：JUMPI不修改状态，所以条件应该仍在栈顶
            # 在块执行之后
            condition = self._extract_jumpi_condition(start_block, executed_state)
            
            # 重要：每个分支必须从状态的独立副本开始
            # 这确保一个分支中的修改不会影响另一个分支
            # 尽管Z3表达式是符号的，我们需要独立的状态对象
            # 以确保与If表达式正确合并
            jump_state_input = executed_state.copy()
            fallthrough_state_input = executed_state.copy()
            
            # 递归执行两个分支，每个返回一个合并状态
            jump_state = self._execute_symbolic_with_cfg(
                jump_target, jump_state_input, cfg, terminals, visited.copy()
            )
            
            fallthrough_state = self._execute_symbolic_with_cfg(
                fallthrough_target, fallthrough_state_input, cfg, terminals, visited.copy()
            )
            
            # 使用If表达式合并两个分支状态，返回合并状态
            merged_state = self._merge_states_with_if(
                condition, jump_state, fallthrough_state
            )
            
            return merged_state
        
        else:
            # 多个后继（不应该发生）
            raise ValueError(f"Block {start_block.pc} has {len(successors)} successors")
    
    def _extract_jumpi_condition(self, block: EVMBlock, state: SMTState):
        """从JUMPI指令中提取条件。
        
        JUMPI从栈中弹出两个值：条件（栈顶）和目标地址（次栈顶）。
        条件在栈顶，目标地址在次栈顶。
        
        Args:
            block: 包含JUMPI指令的块
            state: JUMPI执行前的状态（条件应在栈顶）
        
        Returns:
            BoolRef: 条件表达式（非零 = True，零 = False）
        """
        from z3 import BitVecVal
        
        # 在块中查找JUMPI指令
        # JUMPI应该是块中的最后一个操作
        if not block.operations:
            return BoolVal(True)
        
        last_op = block.operations[-1]
        if last_op.kind.upper() != "JUMPI":
            # 不是JUMPI块，返回True（无条件）
            return BoolVal(True)
        
        # 在JUMPI执行之前，条件应该在栈顶
        # 从栈顶获取条件值
        condition_value = state.evm_stack.peek(0)  # 栈顶值
        
        # 将条件值转换为BoolRef：非零 = True，零 = False
        zero = BitVecVal(0, 256)
        condition = condition_value != zero
        
        return condition
    
    def _merge_states_with_if(self, condition, state1: SMTState, state2: SMTState) -> SMTState:
        """使用If表达式合并两个状态，返回合并状态。
        
        Args:
            condition: BoolRef条件（True -> 使用state1，False -> 使用state2）
            state1: 第一个状态（当条件为True时）
            state2: 第二个状态（当条件为False时）
        
        Returns:
            使用If表达式合并所有字段的合并状态
        """
        from z3 import If
        
        merged = state1.copy()
        
        # 合并简单字段
        merged.return_offset = If(condition, state1.return_offset, state2.return_offset)
        merged.return_length = If(condition, state1.return_length, state2.return_length)
        
        # 合并Array类型（Memory和Stack）
        merged.evm_memory.Memory = If(condition, state1.evm_memory.Memory, state2.evm_memory.Memory)
        merged.evm_memory.MSize = If(condition, state1.evm_memory.MSize, state2.evm_memory.MSize)
        
        # 栈合并：需要合并Stack数组和SP指针
        merged.evm_stack.Stack = If(condition, state1.evm_stack.Stack, state2.evm_stack.Stack)
        merged.evm_stack.SP = If(condition, state1.evm_stack.SP, state2.evm_stack.SP)
        
        # 注意：其他状态字段（x86_memory, x86_registers）在EVM执行中不使用
        # 但为了完整性，我们应该合并它们
        merged.x86_memory.Memory = If(condition, state1.x86_memory.Memory, state2.x86_memory.Memory)
        
        return merged
    
    def _merge_path_results(self, path_results: List[Tuple[Any, Dict[str, Any]]]) -> Dict[str, Any]:
        """使用嵌套If表达式合并路径结果。
        
        Args:
            path_results: (condition, result_dict)元组列表
            
        Returns:
            合并后的结果字典
        """
        if not path_results:
            # 如果没有路径，返回默认结果
            from z3 import BitVecVal
            return {
                'offset': BitVecVal(0, 64),
                'length': BitVecVal(0, 64),
                'memory': None,  # 将由调用者设置
                'base_addr': None,
                'has_return': BoolVal(False)
            }
        
        if len(path_results) == 1:
            # 单一路径：返回其结果
            _, result = path_results[0]
            return result
        
        # 为每个字段构建嵌套If表达式
        # 结构：If(path1_cond, path1_result, If(path2_cond, path2_result, ...))
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
        from state.smt_state import EVMMemoryState
        
        # 从第一个路径结果获取内存数组类型
        first_memory = path_results[0][1]['memory']
        if first_memory is None:
            # 创建默认内存数组
            mem_state = EVMMemoryState()
            first_memory = mem_state.Memory
        
        # 合并每个字段
        merged_offset = build_nested_if('offset', BitVecVal(0, 64))
        merged_length = build_nested_if('length', BitVecVal(0, 64))
        merged_memory = build_nested_if('memory', first_memory)
        merged_has_return = build_nested_if('has_return', BoolVal(False))
        
        return {
            'offset': merged_offset,
            'length': merged_length,
            'memory': merged_memory,
            'base_addr': None,
            'has_return': merged_has_return
        }
    
    def __repr__(self):
        return f"EVMProgram(blocks={len(self.blocks)})"

