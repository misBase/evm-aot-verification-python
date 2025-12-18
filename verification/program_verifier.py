"""
程序等价性验证器。

本模块提供程序级验证功能，
操作整个程序而不是单个块。
"""

from z3 import BitVec, IntVal
from typing import Tuple, Optional
from evm_ir.program import EVMProgram
from x86_64.program import X86Program
from .refinement_checker import RefinementChecker
from state.smt_state import SMTState
from verification.memory_mapping import StackMemoryMapper
from common.uint256 import Uint256


class ProgramEquivalenceChecker:
    """验证EVM和x86程序之间的等价性。"""
    
    def __init__(self, timeout_ms: int = 60000, verbose: bool = False):
        """初始化程序等价性检查器。
        
        Args:
            timeout_ms: SMT求解器超时（毫秒）
            verbose: 启用详细输出
        """
        self.refinement_checker = RefinementChecker(timeout_ms=timeout_ms, verbose=verbose)
        self.verbose = verbose
    
    @staticmethod
    def create_default_initial_state() -> SMTState:
        """创建具有符号输入的默认初始SMT状态。
        
        创建一个新状态，包含：
        - EVM栈上的两个符号256位值
        - 映射到x86内存布局的EVM栈
        
        Returns:
            具有符号输入的已初始化SMTState
        """
        initial_state = SMTState()
        
        # 为EVM栈创建符号输入
        val1 = Uint256.symbolic("program_val1")
        val2 = Uint256.symbolic("program_val2")
        input_stack = [val1.to_bv256(), val2.to_bv256()]
        
        # 使用SP = 0初始化EVM栈
        initial_state.evm_stack.SP = IntVal(0)
        
        # 推送初始栈值
        for stack_val in input_stack:
            initial_state.evm_stack = initial_state.evm_stack.push(stack_val)
        
        # 将EVM栈输入映射到x86内存布局
        for stack_index, stack_value in enumerate(input_stack):
            layout = StackMemoryMapper.stack_to_memory_layout(stack_value, stack_index)
            for offset, limb in layout.items():
                initial_state.x86_memory = initial_state.x86_memory.store_limb(offset, limb)
        
        return initial_state
    
    def verify_program_pair(self,
                           evm_program: EVMProgram,
                           x86_program: X86Program,
                           initial_state: SMTState) -> Tuple[bool, Optional[str]]:
        """验证EVM程序和x86程序在语义上等价。
        
        使用Alive2风格的直接公式构建执行全程序验证：
        1. 公式构建：使用to_z3()为两个程序构建Z3公式
        2. 输出提取：从EVM栈和x86寄存器/内存中提取结果
        3. 等价性检查：使用Z3证明等价性
        
        Args:
            evm_program: 要验证的EVM程序
            x86_program: 对应的x86程序
            initial_state: 已准备好输入的初始SMT状态
            
        Returns:
            (verified, message)，如果程序等价则verified为True
        """
        if self.verbose:
            print(f"\n=== Program-Level Verification (Alive2-style) ===")
            print(f"EVM Program: {evm_program}")
            print(f"x86 Program: {x86_program}")
        
        # 步骤1：公式构建 - EVM（两级路径感知）
        if self.verbose:
            print("\n[1] Building EVM program formula (two-level path-aware)...")
            print("    Level 1: Block-level TAG path merging (3 paths per block)")
            print("    Level 2: CFG-level path merging")
        
        evm_state, evm_result = evm_program.to_z3(initial_state)
        
        if self.verbose:
            print(f"    EVM stack depth: {evm_state.evm_stack.depth}")
            from z3 import BitVecVal
            evm_has_return = evm_state.return_length != BitVecVal(0, 64)
            print(f"    EVM return condition: length != 0 (symbolic, merged from all paths)")
            print(f"    EVM formula built (all paths merged)")
        
        # 步骤2：公式构建 - x86（单级路径感知）
        if self.verbose:
            print("\n[2] Building x86 program formula (path-aware)...")
            print("    Identifying basic blocks and CFG paths")
        
        x86_state, x86_result = x86_program.to_z3(initial_state)
        
        if self.verbose:
            from z3 import BitVecVal
            x86_has_return = x86_state.return_length != BitVecVal(0, 64)
            print(f"    x86 return condition: length != 0 (symbolic, merged from all paths)")
            print(f"    x86 formula built (all paths merged)")
        
        # 步骤3：输出提取（已在to_z3中完成，但验证）
        if self.verbose:
            print("\n[3] Extracting outputs...")
            if isinstance(evm_result, dict):
                print(f"    EVM result: direct memory comparison (offset, length, memory)")
            elif isinstance(evm_result, tuple):
                evm_data, evm_length = evm_result
                print(f"    EVM result: data ({evm_data.size()} bits), length ({evm_length.size()} bits)")
            else:
                print(f"    EVM result: {evm_result.size()}-bit BitVec")
            if isinstance(x86_result, dict):
                print(f"    x86 result: direct memory comparison (offset, length, memory, base_addr)")
            elif isinstance(x86_result, tuple):
                x86_data, x86_length = x86_result
                print(f"    x86 result: data ({x86_data.size()} bits), length ({x86_length.size()} bits)")
            else:
                print(f"    x86 result: {x86_result.size()}-bit BitVec")
        
        # 步骤4：等价性检查
        if self.verbose:
            print("\n[4] Checking program equivalence with Z3...")
            print("    Comparing merged results from all paths (1-to-1 semantic matching)")
        
        return self.refinement_checker.check_refinement(evm_result, x86_result)
    
