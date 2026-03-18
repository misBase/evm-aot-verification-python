"""
用于验证x86和EVM语义之间精化关系的精化检查器。

验证x86精化EVM：对所有输入，x86_output = EVM_output。
"""

import time
from z3 import BitVec, SolverFor, Distinct, unsat, sat, set_option, Array, Select, And, ForAll
from typing import Tuple, Optional


class RefinementChecker:
    """检查x86和EVM语义之间的精化关系。
    
    验证x86精化EVM：对所有输入，x86_output = EVM_output。
    """
    
    def __init__(self, timeout_ms: int = 60000, verbose: bool = False):
        """初始化精化检查器。
        
        Args:
            timeout_ms: SMT求解器超时（毫秒）
            verbose: 启用详细输出
        """
        self.timeout_ms = timeout_ms
        self.verbose = verbose

        # NOTE: Z3 set_option 是全局设置。这里显式在每个实例中设置，避免
        # 前一个 verbose=True 的测试污染后续 verbose=False 的测试。
        set_option(verbose=10 if verbose else 0)
        set_option(proof=bool(verbose))
        
        # 使用QF_AUFBV（数组、未解释函数、位向量）以支持Array比较
        # QF_BV不支持Arrays，所以我们需要QF_AUFBV
        self.solver = SolverFor("QF_AUFBV")
        self.solver.set("timeout", timeout_ms)

    def _timeout_message(self) -> str:
        return f"? TIMEOUT: Solver exceeded overall timeout ({self.timeout_ms} ms)"

    def _unknown_message(self) -> str:
        reason = self.solver.reason_unknown()
        if reason == "timeout":
            return self._timeout_message()
        if reason:
            return f"? UNKNOWN: Solver could not determine refinement (reason: {reason})"
        return "? UNKNOWN: Solver could not determine refinement"

    def _reset_solver_with_budget(self, deadline: Optional[float]) -> bool:
        """重置求解器并为本次 check 设置剩余预算。"""
        now = time.time()
        if deadline is not None and now >= deadline:
            return False

        self.solver.reset()
        if deadline is None:
            timeout_ms = self.timeout_ms
        else:
            timeout_ms = int((deadline - now) * 1000)
            timeout_ms = max(timeout_ms, 1)
        self.solver.set("timeout", timeout_ms)
        return True
    
    def check_refinement(self, evm_result, x86_result) -> Tuple[bool, Optional[str]]:
        """检查x86是否精化EVM（对所有输入，x86_result = evm_result）。
        
        此方法验证精化关系：
          ∀ inputs. x86_output(inputs) = evm_output(inputs)
          
        支持旧格式（单个BitVec）和新格式（数据和长度的元组）。
        
        Args:
            evm_result: 以下之一：
                - EVM输出的逻辑公式（256位BitVec）- 旧格式
                - (data, length)元组，其中：
                    - data: EVM输出的逻辑公式（固定大小BitVec）
                    - length: EVM输出长度的逻辑公式（64位BitVec）
            x86_result: 以下之一：
                - x86输出的逻辑公式（256位BitVec）- 旧格式
                - (data, length)元组，其中：
                    - data: x86输出的逻辑公式（固定大小BitVec）
                    - length: x86输出长度的逻辑公式（64位BitVec）
            
        Returns:
            (verified, message)，如果精化关系成立则verified为True
        """
        # 将 timeout_ms 作为整个 refine 检查流程的总预算（而不是每次 check 的预算）。
        deadline = time.time() + (self.timeout_ms / 1000.0)

        # 处理新格式：带内存引用的字典（直接内存比较）
        if isinstance(evm_result, dict) and isinstance(x86_result, dict):
            return self._check_refinement_direct_memory(evm_result, x86_result, deadline)
        # 处理中间格式：带Array/BitVec的元组
        elif isinstance(evm_result, tuple) and isinstance(x86_result, tuple):
            return self._check_refinement_with_length(evm_result, x86_result, deadline)
        else:
            # 旧格式：向后兼容
            return self._check_refinement_legacy(evm_result, x86_result, deadline)
    
    def _check_refinement_legacy(self, evm_result: BitVec, x86_result: BitVec,
                                 deadline: Optional[float] = None) -> Tuple[bool, Optional[str]]:
        """用于单个BitVec结果的旧版精化检查（向后兼容）。"""
        if evm_result.size() != 256 or x86_result.size() != 256:
            raise ValueError("Both results must be 256-bit BitVecs")

        # 为了证明精化关系：证明不存在使它们不同的输入
        # 我们检查：∃ inputs. evm_result ≠ x86_result
        # 如果UNSAT，则精化关系成立（它们总是相等）

        if not self._reset_solver_with_budget(deadline):
            msg = self._timeout_message()
            if self.verbose:
                print(f"    └─ {msg}")
            return False, msg
        self.solver.add(Distinct(evm_result, x86_result))

        start_time = time.time()
        result = self.solver.check()
        solve_time = time.time() - start_time

        if self.verbose:
            stats = self.solver.statistics()
            print(f"    ├─ Solve time: {solve_time:.3f}s")
            print(f"    ├─ Z3 result: {result}")

        if result == unsat:
            msg = "✓ VERIFIED: x86 refines EVM (semantically equivalent for all inputs)"
            if self.verbose:
                print(f"    └─ {msg}")
            return True, msg
        elif result == sat:
            model = self.solver.model()
            msg = "✗ COUNTEREXAMPLE FOUND: x86 does not refine EVM"
            if self.verbose:
                print(f"    └─ {msg}")
            return False, msg
        else:
            msg = self._unknown_message()
            if self.verbose:
                print(f"    └─ {msg}")
            return False, msg
    
    def _check_refinement_with_length(self, evm_result,
                                     x86_result,
                                     deadline: Optional[float] = None) -> Tuple[bool, Optional[str]]:
        """通过长度和数据比较检查精化关系。

        Args:
            evm_result: (data, length)元组，其中：
                - data: Array[BitVec[64], BitVec[8]]或BitVec（用于向后兼容）
                - length: EVM输出长度的逻辑公式（64位BitVec）
            x86_result: (data, length)元组，其中：
                - data: Array[BitVec[64], BitVec[8]]或BitVec（用于向后兼容）
                - length: x86输出长度的逻辑公式（64位BitVec）

        Returns:
            (verified, message)，如果精化关系成立则verified为True
        """
        evm_data, evm_length = evm_result
        x86_data, x86_length = x86_result

        if evm_length.size() != 64 or x86_length.size() != 64:
            raise ValueError("Length must be 64-bit BitVec")

        # 第一次检查：长度必须相等
        # 如果长度不同，程序不等价
        if not self._reset_solver_with_budget(deadline):
            msg = self._timeout_message()
            if self.verbose:
                print(f"    └─ {msg}")
            return False, msg
        self.solver.add(evm_length != x86_length)

        start_time = time.time()
        result = self.solver.check()
        solve_time = time.time() - start_time

        if self.verbose:
            print(f"    ├─ Length equality check: {solve_time:.3f}s, result={result}")

        if result == sat:
            # 长度可能不同 - 不等价
            msg = "✗ COUNTEREXAMPLE: Return lengths differ"
            if self.verbose:
                print(f"    └─ {msg}")
            return False, msg
        elif result != unsat:
            msg = self._unknown_message()
            if self.verbose:
                print(f"    └─ {msg}")
            return False, msg

        # 第二次检查：如果长度相等，数据必须相等
        # 处理Array和BitVec两种格式
        if not self._reset_solver_with_budget(deadline):
            msg = self._timeout_message()
            if self.verbose:
                print(f"    └─ {msg}")
            return False, msg
        self.solver.add(evm_length == x86_length)  # 长度相等

        # 检查数据是Array还是BitVec
        if isinstance(evm_data, Array) and isinstance(x86_data, Array):
            # Array格式：仅比较到length字节
            # 我们想检查：Exists i. (i < length) && (evm_data[i] != x86_data[i])
            # 如果UNSAT，则ForAll i. (i < length) => (evm_data[i] == x86_data[i])
            from z3 import BitVecVal, ULT

            # 创建符号索引变量
            i = BitVec('return_data_index', 64)

            # 约束：i < length
            index_in_range = ULT(i, evm_length)

            # 比较位置i处的字节
            evm_byte = Select(evm_data, i)
            x86_byte = Select(x86_data, i)

            # 添加约束：i < length AND evm_data[i] != x86_data[i]
            # 如果这是可满足的，我们找到了反例
            self.solver.add(index_in_range)
            self.solver.add(evm_byte != x86_byte)

        else:
            # BitVec格式（向后兼容）：比较整个固定大小数据
            if evm_data.size() != x86_data.size():
                raise ValueError(f"Data sizes must match: EVM={evm_data.size()}, x86={x86_data.size()}")
            self.solver.add(Distinct(evm_data, x86_data))  # But data differs

        start_time = time.time()
        result = self.solver.check()
        solve_time = time.time() - start_time

        if self.verbose:
            print(f"    ├─ Data equality check: {solve_time:.3f}s, result={result}")

        if result == unsat:
            msg = "✓ VERIFIED: x86 refines EVM (lengths and data are equivalent for all inputs)"
            if self.verbose:
                print(f"    └─ {msg}")
            return True, msg
        elif result == sat:
            model = self.solver.model()
            msg = "✗ COUNTEREXAMPLE FOUND: x86 does not refine EVM (data differs)"
            if self.verbose:
                print(f"    └─ {msg}")
            return False, msg
        else:
            msg = self._unknown_message()
            if self.verbose:
                print(f"    └─ {msg}")
            return False, msg
    
    def _check_refinement_direct_memory(self, evm_result: dict, x86_result: dict,
                                        deadline: Optional[float] = None) -> Tuple[bool, Optional[str]]:
        """通过直接比较内存内容检查精化关系。

        这是优化的方法：不是将所有字节提取到Array中，
        而是使用量词直接比较内存内容：
          ForAll i. (0 <= i < length) =>
            EVM_memory[evm_offset + i] == x86_memory[x86_base_addr + x86_offset + i]

        Args:
            evm_result: 包含以下键的字典：
                - 'offset': EVM内存中的64位BitVec偏移量（0 = 无返回）
                - 'length': 64位BitVec长度（0 = 无返回）
                - 'memory': Array[BitVec[64], BitVec[8]] - EVM内存
                - 'base_addr': None（EVM使用直接偏移量，None表示直接寻址）
                - 'has_return': BitVec条件（length != 0）
            x86_result: 包含以下键的字典：
                - 'offset': 64位BitVec偏移量（0 = 无返回）
                - 'length': 64位BitVec长度（0 = 无返回）
                - 'memory': Array[BitVec[64], BitVec[8]] - x86内存
                - 'base_addr': 64位BitVec（R15寄存器值，EVM内存基址指针）
                - 'has_return': BitVec条件（length != 0）

        Returns:
            (verified, message)，如果精化关系成立则verified为True
        """
        from z3 import ForAll, Implies, And, ULT, UGE, BitVec, Select, BitVecVal, sat, unsat

        evm_offset = evm_result['offset']
        evm_length = evm_result['length']
        evm_memory = evm_result['memory']
        evm_has_return = evm_result.get('has_return', evm_length != BitVecVal(0, 64))

        x86_offset = x86_result['offset']
        x86_length = x86_result['length']
        x86_memory = x86_result['memory']
        x86_base_addr = x86_result['base_addr']
        x86_has_return = x86_result.get('has_return', x86_length != BitVecVal(0, 64))

        # 第一次检查：返回条件必须等价
        # EVM返回当且仅当x86返回
        if not self._reset_solver_with_budget(deadline):
            msg = self._timeout_message()
            if self.verbose:
                print(f"    └─ {msg}")
            return False, msg
        self.solver.add(evm_has_return != x86_has_return)

        start_time = time.time()
        result = self.solver.check()
        solve_time = time.time() - start_time

        if self.verbose:
            print(f"    ├─ Return condition check: {solve_time:.3f}s, result={result}")

        if result == sat:
            msg = "✗ COUNTEREXAMPLE: Return conditions differ (one returns, the other doesn't)"
            if self.verbose:
                print(f"    └─ {msg}")
            return False, msg
        elif result != unsat:
            msg = self._unknown_message()
            if self.verbose:
                print(f"    └─ {msg}")
            return False, msg

        # 第二次检查：如果两者都返回（或都不返回），长度必须相等
        if not self._reset_solver_with_budget(deadline):
            msg = self._timeout_message()
            if self.verbose:
                print(f"    └─ {msg}")
            return False, msg
        self.solver.add(evm_has_return)  # 假设两者都返回
        self.solver.add(x86_has_return)
        self.solver.add(evm_length != x86_length)

        start_time = time.time()
        result = self.solver.check()
        solve_time = time.time() - start_time

        if self.verbose:
            print(f"    ├─ Length equality check: {solve_time:.3f}s, result={result}")

        if result == sat:
            msg = "✗ COUNTEREXAMPLE: Return lengths differ"
            if self.verbose:
                print(f"    └─ {msg}")
            return False, msg
        elif result != unsat:
            msg = self._unknown_message()
            if self.verbose:
                print(f"    └─ {msg}")
            return False, msg

        # 第三次检查：如果长度相等且两者都返回，内存内容必须相等
        # 我们想检查：ForAll i. (0 <= i < length) =>
        #   EVM_memory[evm_offset + i] == x86_memory[x86_base_addr + x86_offset + i]
        #
        # 我们检查否定：Exists i. (0 <= i < length) AND
        #   EVM_memory[evm_offset + i] != x86_memory[x86_base_addr + x86_offset + i]
        # 如果这是UNSAT，则ForAll成立。

        if not self._reset_solver_with_budget(deadline):
            msg = self._timeout_message()
            if self.verbose:
                print(f"    └─ {msg}")
            return False, msg
        self.solver.add(evm_has_return)  # 两者都返回
        self.solver.add(x86_has_return)
        self.solver.add(evm_length == x86_length)  # 长度相等

        # 创建符号索引变量
        i = BitVec('return_data_index', 64)

        # 约束：0 <= i < length
        index_in_range = And(UGE(i, BitVecVal(0, 64)), ULT(i, evm_length))

        # 计算内存地址
        evm_addr = evm_offset + i
        x86_addr = x86_base_addr + x86_offset + i

        # 从内存读取字节
        evm_byte = Select(evm_memory, evm_addr)
        x86_byte = Select(x86_memory, x86_addr)

        # 添加约束：i在范围内 AND evm_byte != x86_byte
        # 如果这是可满足的，我们找到了反例
        self.solver.add(index_in_range)
        self.solver.add(evm_byte != x86_byte)

        start_time = time.time()
        result = self.solver.check()
        solve_time = time.time() - start_time

        if self.verbose:
            print(f"    ├─ Memory content check: {solve_time:.3f}s, result={result}")

        if result == unsat:
            pass  # Memory contents equivalent, continue to storage check
        elif result == sat:
            model = self.solver.model()
            msg = "✗ COUNTEREXAMPLE FOUND: x86 does not refine EVM (memory contents differ)"
            if self.verbose:
                print(f"    └─ {msg}")
            return False, msg
        else:
            msg = self._unknown_message()
            if self.verbose:
                print(f"    └─ {msg}")
            return False, msg

        # 第四次检查：Storage等价性（如果结果中包含storage）
        evm_storage = evm_result.get('storage')
        x86_storage = x86_result.get('storage')

        if evm_storage is not None and x86_storage is not None:
            verified, msg = self._check_storage_equivalence(
                evm_storage, x86_storage, deadline
            )
            if not verified:
                return False, msg

        msg = "✓ VERIFIED: x86 refines EVM (return conditions, lengths, memory contents, and storage are equivalent for all inputs)"
        if self.verbose:
            print(f"    └─ {msg}")
        return True, msg

    def _check_storage_equivalence(self, evm_storage, x86_storage,
                                   deadline=None):
        """检查EVM和x86的Storage是否等价。

        反证法：是否存在key使得 Select(evm_storage, key) != Select(x86_storage, key)
        如果UNSAT，则storage等价。

        Args:
            evm_storage: EVM侧的Storage Z3 Array
            x86_storage: x86侧的Storage Z3 Array
            deadline: 超时截止时间

        Returns:
            (verified, message)
        """
        from z3 import BitVec, Select, sat, unsat

        if not self._reset_solver_with_budget(deadline):
            msg = self._timeout_message()
            if self.verbose:
                print(f"    └─ {msg}")
            return False, msg

        key = BitVec('storage_check_key', 256)
        self.solver.add(Select(evm_storage, key) != Select(x86_storage, key))

        import time
        start_time = time.time()
        result = self.solver.check()
        solve_time = time.time() - start_time

        if self.verbose:
            print(f"    ├─ Storage equivalence check: {solve_time:.3f}s, result={result}")

        if result == unsat:
            return True, "Storage equivalent"
        elif result == sat:
            msg = "✗ COUNTEREXAMPLE FOUND: x86 does not refine EVM (storage differs)"
            if self.verbose:
                print(f"    └─ {msg}")
            return False, msg
        else:
            msg = self._unknown_message()
            if self.verbose:
                print(f"    └─ {msg}")
            return False, msg
