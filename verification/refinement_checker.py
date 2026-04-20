"""
用于验证x86和EVM语义之间精化关系的精化检查器。

验证x86精化EVM：对所有输入，x86_output = EVM_output。
"""

import time
from z3 import BitVec, SolverFor, Distinct, unsat, sat, set_option, Select, And, ForAll
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
    
    def check_refinement(self, evm_result: dict, x86_result: dict) -> Tuple[bool, Optional[str]]:
        """检查x86是否精化EVM（对所有输入，x86_result = evm_result）。

        此方法验证精化关系：
          ∀ inputs. x86_output(inputs) = evm_output(inputs)

        Args:
            evm_result: 包含 offset, length, memory, base_addr, has_return, storage, transient_storage 的字典
            x86_result: 同上格式的字典

        Returns:
            (verified, message)，如果精化关系成立则verified为True
        """
        # 将 timeout_ms 作为整个 refine 检查流程的总预算（而不是每次 check 的预算）。
        deadline = time.time() + (self.timeout_ms / 1000.0)

        return self._check_refinement_direct_memory(evm_result, x86_result, deadline)
    
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

        # 第五次检查：Transient Storage等价性（如果结果中包含transient_storage）
        evm_ts = evm_result.get('transient_storage')
        x86_ts = x86_result.get('transient_storage')

        if evm_ts is not None and x86_ts is not None:
            verified, msg = self._check_transient_storage_equivalence(
                evm_ts, x86_ts, deadline
            )
            if not verified:
                return False, msg

        msg = "✓ VERIFIED: x86 refines EVM (return conditions, lengths, memory contents, storage, and transient storage are equivalent for all inputs)"
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

    def _check_transient_storage_equivalence(self, evm_ts, x86_ts,
                                              deadline=None):
        """检查EVM和x86的Transient Storage是否等价。

        反证法：是否存在key使得 Select(evm_ts, key) != Select(x86_ts, key)
        如果UNSAT，则transient storage等价。

        Args:
            evm_ts: EVM侧的TransientStorage Z3 Array
            x86_ts: x86侧的TransientStorage Z3 Array
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

        key = BitVec('transient_storage_check_key', 256)
        self.solver.add(Select(evm_ts, key) != Select(x86_ts, key))

        import time
        start_time = time.time()
        result = self.solver.check()
        solve_time = time.time() - start_time

        if self.verbose:
            print(f"    ├─ Transient storage equivalence check: {solve_time:.3f}s, result={result}")

        if result == unsat:
            return True, "Transient storage equivalent"
        elif result == sat:
            msg = "✗ COUNTEREXAMPLE FOUND: x86 does not refine EVM (transient storage differs)"
            if self.verbose:
                print(f"    └─ {msg}")
            return False, msg
        else:
            msg = self._unknown_message()
            if self.verbose:
                print(f"    └─ {msg}")
            return False, msg
