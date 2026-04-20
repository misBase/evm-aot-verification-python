"""
程序等价性验证器。

本模块提供程序级验证功能，
操作整个程序而不是单个块。
"""

import time
from typing import Tuple, Optional, Dict, Any
from evm_ir.program import EVMProgram
from x86_64.program import X86Program
from .refinement_checker import RefinementChecker
from .call_site_mapping import build_call_site_mapping
from state.smt_state import SMTState


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
            print(f"┌─ EVM Program: {evm_program}")
            print(f"└─ x86 Program: {x86_program}")

        # 步骤1：公式构建 - EVM（两级路径感知）
        if self.verbose:
            print("\n[1] Building EVM program formula (two-level path-aware)...")
            print("    ├─ Level 1: Block-level TAG path merging")
            print("    ├─ Level 2: CFG-level path merging")

        evm_start = time.time()
        evm_state, evm_result = evm_program.to_z3(initial_state)
        evm_build_time = time.time() - evm_start

        if self.verbose:
            print(f"    ├─ EVM stack depth: {evm_state.evm_stack.depth}")
            from z3 import BitVecVal, simplify
            evm_has_return = simplify(evm_state.return_length != BitVecVal(0, 64))
            print(f"    ├─ EVM has return: {evm_has_return}")
            # 估算公式复杂度
            formula_size = self._estimate_formula_size(evm_result)
            print(f"    ├─ Formula size: ~{formula_size} expressions")
            print(f"    └─ ✓ Built in {evm_build_time:.3f}s")

        # 步骤2：公式构建 - x86（单级路径感知）
        if self.verbose:
            print("\n[2] Building x86 program formula (path-aware)...")
            print("    ├─ Identifying basic blocks and CFG paths")

        x86_start = time.time()
        call_site_mapping = build_call_site_mapping(evm_program, x86_program)
        x86_state, x86_result = x86_program.to_z3(initial_state, call_site_mapping=call_site_mapping)
        x86_build_time = time.time() - x86_start

        if self.verbose:
            x86_has_return = simplify(x86_state.return_length != BitVecVal(0, 64))
            print(f"    ├─ x86 has return: {x86_has_return}")
            print(f"    ├─ Shared host call-site mappings: {len(call_site_mapping)}")
            # 估算公式复杂度
            formula_size = self._estimate_formula_size(x86_result)
            print(f"    ├─ Formula size: ~{formula_size} expressions")
            print(f"    └─ ✓ Built in {x86_build_time:.3f}s")

        # 步骤3：输出提取（已在to_z3中完成，但验证）
        if self.verbose:
            print("\n[3] Extracting outputs...")
            keys = ", ".join(evm_result.keys())
            print(f"    ├─ EVM result: dict with keys: ({keys})")
            keys = ", ".join(x86_result.keys())
            print(f"    └─ x86 result: dict with keys: ({keys})")

        # 步骤4：等价性检查
        if self.verbose:
            print("\n[4] Checking program equivalence with Z3...")
            print("    ├─ Comparing merged results from all paths (1-to-1 semantic matching)")

        check_start = time.time()
        verified, message = self.refinement_checker.check_refinement(evm_result, x86_result)
        check_time = time.time() - check_start

        if self.verbose:
            print(f"    ├─ Check time: {check_time:.3f}s")
            print(f"    └─ Result: {message}")

        return verified, message

    def _estimate_formula_size(self, result: dict) -> str:
        """估算公式大小（表达式数量）。"""
        count = sum(1 for key in ('offset', 'length', 'has_return') if key in result)
        if 'memory' in result:
            count += 20
        return f"{count}"
    
