"""
程序等价性验证器。

本模块提供程序级验证功能，
操作整个程序而不是单个块。
"""

import time
from typing import Tuple, Optional
from evm_ir.program import EVMProgram
from x86_64.program import X86Program
from x86_64.summaries import X86SummaryConfig
from .refinement_checker import RefinementChecker
from .call_site_mapping import build_call_site_mapping
from state.smt_state import SMTState


def _collect_assumptions(*states):
    """Collect dedup'd SMTState.assumptions from a list of states (skip None)."""
    seen = set()
    out = []
    for s in states:
        if s is None:
            continue
        for a in getattr(s, 'assumptions', None) or []:
            key = a.hash()
            if key in seen:
                continue
            seen.add(key)
            out.append(a)
    return out


# 循环上界系数：cfg_executor 的 max_iteration 硬上界（超过即被特殊处理），
# 故任一 block 最多被经过这么多次。用作 gas 恒足 bound 的保守乘子。
_GAS_BOUND_MAX_ITERATION = 500


# 已建模动态 gas 的 opcode（逐阶段转正后从 unsupported 移除）：
#   阶段 1：MSTORE, RETURN, MLOAD, MSTORE8（内存扩展动态 gas）
#           SHA3/KECCAK256（内存扩展 + word gas，_charge_memory_and_word_gas）
# 其余仍 fail-closed 拒绝 gas 检查，直到对应阶段建模。
_DYNAMIC_GAS_UNSUPPORTED_KINDS = frozenset({
    # Data-dependent opcode gas.
    "EXP",
    # CALLDATACOPY/CODECOPY/RETURNDATACOPY/MCOPY/REVERT 已建模（内存扩展 + copy
    # word gas / REVERT 仅内存）。EXTCODECOPY 额外有冷热账户访问 gas（host），待后续。
    "EXTCODECOPY",
    # State / account access gas depends on warm/cold state and current values.
    "SLOAD",
    "SSTORE",
    "BALANCE",
    "EXTCODESIZE",
    "EXTCODEHASH",
    "SELFDESTRUCT",
    # CALL/CREATE 系列:gas 含 EIP-150 63/64 转发、value stipend、内存扩展、
    # CREATE 的 InitCodeWordGas、以及 host cost(Go runtime 职责，UF 信任边界)。
    # returnGas 常量链(dealWithAddGas/SubGas)在 host 调用前后相消——在「host gas
    # 当 UF」前提下，returnGas 链无法被非空独立验证（这是 A 强度的固有边界）。
    # EVM 侧尚未建模 CREATE 内存扩展 + InitCodeWordGas，故全部 fail-closed 拒绝，
    # 待后续阶段（含 host gas-delta UF 设计）再纳入。
    "CALL",
    "CALLCODE",
    "DELEGATECALL",
    "STATICCALL",
    "CREATE",
    "CREATE2",
})


def _find_unsupported_dynamic_gas_ops(evm_program: EVMProgram) -> list[str]:
    """Return dynamic-gas operators that stage-0 gas checking must reject.

    Stage 0 proves only static block gas.  Returning a non-empty list is a
    fail-closed guard against false greens when both sides currently omit the
    same dynamic gas side effect.
    """
    unsupported: list[str] = []
    for block in getattr(evm_program, "blocks", None) or []:
        for op in getattr(block, "operations", None) or []:
            kind = (getattr(op, "kind", "") or "").upper()
            if kind.startswith("LOG") or kind in _DYNAMIC_GAS_UNSUPPORTED_KINDS:
                pc = getattr(op, "pc", None)
                if pc is None:
                    unsupported.append(kind)
                else:
                    unsupported.append(f"{kind}@pc=0x{pc:x}")
    return unsupported


def _inject_gas_sufficiency_assumption(evm_program: EVMProgram, initial_state: SMTState) -> None:
    """注入「gas 恒足」前提 UGE(G, bound)，让 out-of-gas 分支恒假被剪。

    阶段 0 只比较 gas 终值（不验 OOG 行为），需保证两侧都不触发 out-of-gas，
    否则 EVM 侧 consume_static 钳零会与 x86 的 OOG 跳转语义分叉。

    bound = (∑ block.static_gas) × max_iteration 是程序实际可扣 static gas 的
    **可证上界**（每个 block 最多经过 max_iteration 次），不是魔法常量。
    - ∑static_gas == 0（无静态 gas）→ 不注入（无需约束）。
    - bound 接近/超过 2^64（会 wrap）→ **fail-closed 不注入**：宁可不剪 OOG 分支
      （检查更严，可能 SAT/unknown），也不注入错误的 wrap 约束。
    """
    from z3 import BitVecVal, UGE

    blocks = getattr(evm_program, "blocks", None)
    if not blocks:
        # 程序未暴露 blocks（如测试 stub）→ 无法算 bound，不注入假设。
        return
    total_static = sum(getattr(b, "static_gas", 0) or 0 for b in blocks)
    if total_static <= 0:
        return

    bound = total_static * _GAS_BOUND_MAX_ITERATION
    if bound >= (1 << 64):
        # 上界超出 64-bit gas 表示范围 → 无法给出健全的 bound，fail-closed。
        return

    gas_symbol = initial_state.evm_gas.Gas
    assumption = UGE(gas_symbol, BitVecVal(bound, 64))

    if initial_state.assumptions is None:
        initial_state.assumptions = []
    initial_state.assumptions.append(assumption)


class ProgramEquivalenceChecker:
    """验证EVM和x86程序之间的等价性。"""

    def __init__(self, timeout_ms: int = 60000, verbose: bool = False,
                 check_gas: bool = False):
        """初始化程序等价性检查器。

        Args:
            timeout_ms: SMT求解器超时（毫秒）
            verbose: 启用详细输出
            check_gas: 是否启用 gas 终值一致性检查（阶段 0，仅静态 gas）。
                默认 False；含动态 gas 指令的程序需到阶段 1 才支持。
        """
        self.refinement_checker = RefinementChecker(
            timeout_ms=timeout_ms, verbose=verbose, check_gas=check_gas
        )
        self.verbose = verbose
        self.check_gas = check_gas

    def verify_program_pair(self,
                           evm_program: EVMProgram,
                           x86_program: X86Program,
                           initial_state: SMTState,
                           stack_check: Optional[int] = None,
                           stack_check_timeout_ms: int = 300000,
                           path_observations: bool = False,
                           path_pair_workers: int = 1,
                           enable_merge: bool = True,
                           skip_feasibility: bool = False,
                           summary_config: Optional[X86SummaryConfig] = None,
                           x86_reachability_timeout_ms: Optional[int] = 50) -> Tuple[bool, Optional[str]]:
        """验证EVM程序和x86程序在语义上等价。

        默认使用旧的 merged-result 检查路径，保持原有 Alive2 风格的
        直接公式构建流程：
        1. 公式构建：使用 ``to_z3()`` 为两个程序构建 Z3 公式；
        2. 输出提取：从 EVM 终态和 x86 终态中提取 return data、memory、
           storage 等 observable；
        3. 等价性检查：使用 Z3 证明两个 merged result 等价。

        显式设置 ``path_observations=True`` 时，改用终止路径 observation
        直接检查，避免先合并完整内存 Array。

        Args:
            evm_program: 要验证的EVM程序
            x86_program: 对应的x86程序
            initial_state: 已准备好输入的初始SMT状态
            stack_check: 栈一致性检查的固定槽位数量；None 表示跳过步骤5
            stack_check_timeout_ms: 步骤5（debug 栈检查）的独立超时预算（毫秒）
            path_observations: 使用终止路径 observation 直接检查，避免完整 Array 终态合并；
                默认 False，保持旧 merged-result 行为
            path_pair_workers: path_observations=True 时用于 EVM/x86 terminal path
                pair 检查的 worker 数；默认 1，保持串行行为
            summary_config: x86 summary 插件配置；None 表示不启用 summary
            x86_reachability_timeout_ms: path_observations=True 时 x86 CFG
                executor 每次 reachability pruning 的局部 timeout；None 表示不设 cap

        Returns:
            (verified, message)，如果程序等价则verified为True
        """
        if stack_check is not None and stack_check <= 0:
            raise ValueError("stack_check must be a positive integer or None")
        if stack_check_timeout_ms <= 0:
            raise ValueError("stack_check_timeout_ms must be a positive integer")
        if path_pair_workers <= 0:
            raise ValueError("path_pair_workers must be a positive integer")

        # gas 一致性阶段 0：只支持静态 gas。遇到动态 gas opcode 必须 fail-closed，
        # 避免 EVM/x86 两侧都尚未建模动态扣减时出现假绿。
        if self.check_gas:
            unsupported_dynamic_gas = _find_unsupported_dynamic_gas_ops(evm_program)
            if unsupported_dynamic_gas:
                sample = ", ".join(unsupported_dynamic_gas[:8])
                if len(unsupported_dynamic_gas) > 8:
                    sample += f", ... (+{len(unsupported_dynamic_gas) - 8} more)"
                return (
                    False,
                    "✗ GAS CHECK UNSUPPORTED: dynamic gas operators are not "
                    f"modeled yet for stage 0: {sample}",
                )

        # gas 一致性阶段 0：仅在显式启用 gas 检查时注入「gas 恒足」前提
        # （UGE(G, bound)），让两侧 out-of-gas 分支恒假被剪，使 gas 终值等式
        # 比较成立。bound 由静态 gas 之和 × max_iteration 给出可证上界。
        if self.check_gas:
            _inject_gas_sufficiency_assumption(evm_program, initial_state)

        if self.verbose:
            print(f"\n=== Program-Level Verification (Alive2-style) ===")
            print(f"┌─ EVM Program: {evm_program}")
            print(f"└─ x86 Program: {x86_program}")

        if path_observations:
            return self._verify_program_pair_path_observations(
                evm_program,
                x86_program,
                initial_state,
                stack_check,
                stack_check_timeout_ms,
                path_pair_workers,
                enable_merge=enable_merge,
                skip_feasibility=skip_feasibility,
                summary_config=summary_config,
                x86_reachability_timeout_ms=x86_reachability_timeout_ms,
            )

        # 步骤1：公式构建 - EVM（两级路径感知）
        if self.verbose:
            print("\n[1] Building EVM program formula (two-level path-aware)...")
            print("    ├─ Level 1: Block-level TAG path merging")
            print("    ├─ Level 2: CFG-level path merging")

        evm_start = time.time()
        evm_state, evm_result = evm_program.to_z3(initial_state)
        evm_build_time = time.time() - evm_start

        if self.verbose:
            from z3 import BitVecVal, simplify
            evm_has_return_data = simplify(evm_state.return_length != BitVecVal(0, 64))
            print(f"    ├─ EVM has non-empty return data: {evm_has_return_data}")
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
        x86_state, x86_result = x86_program.to_z3(
            initial_state,
            call_site_mapping=call_site_mapping,
            enable_merge=enable_merge,
            summary_config=summary_config,
        )
        x86_build_time = time.time() - x86_start

        if self.verbose:
            x86_has_return_data = simplify(x86_state.return_length != BitVecVal(0, 64))
            print(f"    ├─ x86 has non-empty return data: {x86_has_return_data}")
            print(f"    ├─ Shared host call-site mappings: {len(call_site_mapping)}")
            for line in self._summary_stats_lines(
                getattr(x86_program, "last_summary_stats", {})
            ):
                print(line)
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
            print(f"    └─ Budget: {self.refinement_checker.timeout_ms} ms")

        check_start = time.time()
        # 把 initial_state、evm_state、x86_state 上累积的 assumptions（包括
        # CALLDATALOAD 处的 hi-192==0 等无损先验，以及 caller 设定的 calldatasize
        # 上界）作为顶层 precondition 传给 refinement check 的 solver。
        # merged-result 路径没有 path_condition 字段，但 solver 也会以
        # path_condition 形式接收。
        assumptions = _collect_assumptions(initial_state, evm_state, x86_state)
        if assumptions:
            from z3 import And, BoolVal
            extra_condition = And(BoolVal(True), *assumptions)
        else:
            extra_condition = None
        verified, message = self.refinement_checker.check_refinement(
            evm_result, x86_result, assumptions=extra_condition,
        )
        check_time = time.time() - check_start

        if self.verbose:
            print(f"    ├─ Check time: {check_time:.3f}s")
            print(f"    └─ Result: {message}")

        if not verified and message == self.refinement_checker._timeout_message():
            message = (
                f"? TIMEOUT: refinement check exceeded overall timeout "
                f"({self.refinement_checker.timeout_ms} ms)"
            )

        if not verified:
            return verified, message

        if stack_check is None:
            if self.verbose:
                print("\n[5] Skipping stack equivalence check (debug disabled).")
            return verified, message

        # 步骤5：栈一致性检查（调试用），使用独立 timeout budget
        if self.verbose:
            print("\n[5] Checking stack equivalence (debug)...")
            print(f"    └─ Budget: {stack_check_timeout_ms} ms")

        stack_start = time.time()
        stack_deadline = time.time() + (stack_check_timeout_ms / 1000.0)
        verified, message = self.refinement_checker.check_stack_equivalence(
            evm_state,
            x86_state,
            initial_state,
            n_elements=stack_check,
            deadline=stack_deadline,
        )
        stack_time = time.time() - stack_start

        if self.verbose:
            print(f"    ├─ Stack check time: {stack_time:.3f}s")
            print(f"    └─ Result: {message}")

        if not verified and message == self.refinement_checker._timeout_message():
            message = (
                f"? TIMEOUT: stack equivalence check exceeded overall timeout "
                f"({stack_check_timeout_ms} ms)"
            )

        return verified, message

    def _estimate_formula_size(self, result: dict) -> str:
        """估算公式大小（表达式数量）。"""
        count = sum(1 for key in ('offset', 'length', 'has_return_data') if key in result)
        if 'memory' in result:
            count += 20
        return f"{count}"

    def _summary_stats_lines(self, stats: dict) -> list[str]:
        if not stats:
            return ["    ├─ x86 summaries: none registered"]
        lines = []
        for kind, stat in sorted(stats.items()):
            hit_entries = stat.get("hit_entries", set())
            lines.append(
                f"    ├─ x86 summary {kind}: {len(hit_entries)} unique / "
                f"{stat.get('hits', 0)} hits "
                f"(discovered {stat.get('discovered', 0)}, "
                f"mode={stat.get('mode')})"
            )
        return lines

    def _verify_program_pair_path_observations(
        self,
        evm_program: EVMProgram,
        x86_program: X86Program,
        initial_state: SMTState,
        stack_check: Optional[int],
        stack_check_timeout_ms: int,
        path_pair_workers: int,
        enable_merge: bool = True,
        skip_feasibility: bool = False,
        summary_config: Optional[X86SummaryConfig] = None,
        x86_reachability_timeout_ms: Optional[int] = 50,
    ) -> Tuple[bool, Optional[str]]:
        """用终止路径 observations 直接验证程序等价。

        该路径避免先把所有 terminal states 合并成一个完整 memory Array；
        每条终止路径保留自己的 condition 和 observable，后续做 EVM/x86
        terminal path pair 的覆盖与精化检查。只有 debug stack_check 需要时，
        才额外要求执行器产出 merged_state 作为栈检查 fallback。
        """
        if self.verbose:
            print("\n[1] Building EVM terminal path observations...")

        evm_start = time.time()
        # stack_check 是调试辅助检查；只有它需要 merged terminal state。
        # 纯 observable 精化只消费 observations，避免不必要的 Array 合并。
        evm_paths = evm_program.to_z3_paths(
            initial_state,
            merge_state=stack_check is not None,
        )
        evm_build_time = time.time() - evm_start
        evm_state = evm_paths.merged_state

        if self.verbose:
            print(f"    ├─ Terminal paths: {len(evm_paths.observations)}")
            print(f"    └─ ✓ Built in {evm_build_time:.3f}s")

        if self.verbose:
            print("\n[2] Building x86 terminal path observations...")

        x86_start = time.time()
        call_site_mapping = build_call_site_mapping(evm_program, x86_program)
        # x86 path 构建同样保留 terminal observations；reachability pruning
        # 只影响路径枚举剪枝，不改变后续 refinement 的证明方式。
        x86_paths = x86_program.to_z3_paths(
            initial_state,
            call_site_mapping=call_site_mapping,
            merge_state=stack_check is not None,
            enable_merge=enable_merge,
            summary_config=summary_config,
            reachability_timeout_ms=x86_reachability_timeout_ms,
        )
        x86_build_time = time.time() - x86_start
        x86_state = x86_paths.merged_state

        if self.verbose:
            print(f"    ├─ Terminal paths: {len(x86_paths.observations)}")
            print(f"    ├─ Shared host call-site mappings: {len(call_site_mapping)}")
            for line in self._summary_stats_lines(
                getattr(x86_program, "last_summary_stats", {})
            ):
                print(line)
            print(f"    └─ ✓ Built in {x86_build_time:.3f}s")

        if self.verbose:
            print("\n[3] Extracting path observations...")
            observation_keys = (
                "condition, offset, length, memory, base_addr, "
                "has_return_data, storage, transient_storage"
            )
            print(f"    ├─ EVM observation keys: {observation_keys}")
            print(f"    └─ x86 observation keys: {observation_keys}")

        if self.verbose:
            print("\n[4] Checking program equivalence with Z3...")
            print("    ├─ Comparing terminal path observations without Array-level state merge")
            print(f"    ├─ Budget: {self.refinement_checker.timeout_ms} ms")
            print(f"    └─ Path pair workers: {path_pair_workers}")

        check_start = time.time()
        # path_observations 模式下，每个 observation 自带 path condition；
        # 顶层 assumptions 需要同时约束每条路径条件和 coverage 查询。
        # PathObservation 是 frozen dataclass，因此用 replace 生成新对象。
        path_assumptions = _collect_assumptions(initial_state, evm_state, x86_state)
        if path_assumptions:
            from dataclasses import replace
            from z3 import And, BoolVal
            coverage_precondition = And(BoolVal(True), *path_assumptions)
            evm_paths_obs = [
                replace(obs, condition=And(obs.condition, coverage_precondition))
                for obs in evm_paths.observations
            ]
            x86_paths_obs = [
                replace(obs, condition=And(obs.condition, coverage_precondition))
                for obs in x86_paths.observations
            ]
        else:
            coverage_precondition = None
            evm_paths_obs = evm_paths.observations
            x86_paths_obs = x86_paths.observations

        # 串行/并行共用同一个 refinement 入口；并行时只额外传 worker 数。
        if path_pair_workers == 1:
            verified, message = self.refinement_checker.check_refinement_paths(
                evm_paths_obs,
                x86_paths_obs,
                skip_feasibility=skip_feasibility,
                evm_coverage=evm_paths.coverage,
                x86_coverage=x86_paths.coverage,
                coverage_precondition=coverage_precondition,
            )
        else:
            verified, message = self.refinement_checker.check_refinement_paths(
                evm_paths_obs,
                x86_paths_obs,
                path_pair_workers=path_pair_workers,
                skip_feasibility=skip_feasibility,
                evm_coverage=evm_paths.coverage,
                x86_coverage=x86_paths.coverage,
                coverage_precondition=coverage_precondition,
            )
        check_time = time.time() - check_start

        if self.verbose:
            print(f"    ├─ Check time: {check_time:.3f}s")
            print(f"    └─ Result: {message}")

        if not verified and message == self.refinement_checker._timeout_message():
            # 将底层通用 timeout 文案改写为程序级 refinement timeout，便于定位阶段。
            message = (
                f"? TIMEOUT: refinement check exceeded overall timeout "
                f"({self.refinement_checker.timeout_ms} ms)"
            )

        if not verified:
            return verified, message

        if stack_check is None:
            if self.verbose:
                print("\n[5] Skipping stack equivalence check (debug disabled).")
            return verified, message

        if self.verbose:
            print("\n[5] Checking stack equivalence (debug, merged state fallback)...")
            print(f"    └─ Budget: {stack_check_timeout_ms} ms")

        # 正常 path observation 检查不依赖 merged_state；如果调用方要求 debug
        # stack_check，而执行器没有产出 merged_state，则只能明确失败。
        if evm_state is None or x86_state is None:
            return (
                False,
                "✗ STACK CHECK UNAVAILABLE: no merged terminal state was produced",
            )

        stack_start = time.time()
        stack_deadline = time.time() + (stack_check_timeout_ms / 1000.0)
        verified, message = self.refinement_checker.check_stack_equivalence(
            evm_state,
            x86_state,
            initial_state,
            n_elements=stack_check,
            deadline=stack_deadline,
        )
        stack_time = time.time() - stack_start

        if self.verbose:
            print(f"    ├─ Stack check time: {stack_time:.3f}s")
            print(f"    └─ Result: {message}")

        if not verified and message == self.refinement_checker._timeout_message():
            # stack_check 使用独立预算，timeout 文案也按独立阶段改写。
            message = (
                f"? TIMEOUT: stack equivalence check exceeded overall timeout "
                f"({stack_check_timeout_ms} ms)"
            )

        return verified, message
    
