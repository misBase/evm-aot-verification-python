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


def _merged_coverage_failure(evm_result: dict, x86_result: dict) -> Optional[str]:
    """merged 模式的 fail-closed coverage 检查。

    merged 语义把所有终止路径折叠进一个 If 表达式；被剪掉的路径会让合并
    结果只代表幸存路径的语义——这不只是覆盖缺口，而是可能假绿。因此任一
    侧证书缺失或 incomplete 时验证必须失败（path_observations 模式有 SMT
    coverage 兜底，merged 模式没有）。
    """
    for label, result in (("EVM", evm_result), ("x86", x86_result)):
        coverage = result.get('coverage')
        if coverage is None:
            return (
                f"✗ COVERAGE UNKNOWN: {label} merged semantics carries no "
                "path coverage certificate"
            )
        if not coverage.complete:
            return (
                f"✗ COVERAGE INCOMPLETE: {label} merged semantics may have "
                f"dropped paths ({coverage.reason})"
            )
    return None


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
                           initial_state: SMTState,
                           stack_check: Optional[int] = None,
                           stack_check_timeout_ms: int = 300000,
                           path_observations: bool = False,
                           path_pair_workers: int = 1,
                           enable_merge: bool = True,
                           skip_feasibility: bool = False,
                           summary_config: Optional[X86SummaryConfig] = None,
                           x86_reachability_timeout_ms: Optional[int] = 50,
                           max_depth: Optional[int] = None) -> Tuple[bool, Optional[str]]:
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
            max_depth: EVM 与 x86 符号执行的最大搜索深度；None 表示使用
                两侧 to_z3/to_z3_paths 的默认值。大合约需要更深搜索时
                （避免触发 coverage-incomplete）应显式传入更大的值，而不是
                依赖全局默认值。

        Returns:
            (verified, message)，如果程序等价则verified为True
        """
        if stack_check is not None and stack_check <= 0:
            raise ValueError("stack_check must be a positive integer or None")
        if stack_check_timeout_ms <= 0:
            raise ValueError("stack_check_timeout_ms must be a positive integer")
        if path_pair_workers <= 0:
            raise ValueError("path_pair_workers must be a positive integer")

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
                max_depth=max_depth,
            )

        # 步骤1：公式构建 - EVM（两级路径感知）
        if self.verbose:
            print("\n[1] Building EVM program formula (two-level path-aware)...")
            print("    ├─ Level 1: Block-level TAG path merging")
            print("    ├─ Level 2: CFG-level path merging")

        evm_start = time.time()
        evm_to_z3_kwargs = {}
        if max_depth is not None:
            evm_to_z3_kwargs["max_depth"] = max_depth
        evm_state, evm_result = evm_program.to_z3(
            initial_state,
            **evm_to_z3_kwargs,
        )
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
        x86_to_z3_kwargs = {}
        if max_depth is not None:
            x86_to_z3_kwargs["max_depth"] = max_depth
        x86_state, x86_result = x86_program.to_z3(
            initial_state,
            call_site_mapping=call_site_mapping,
            enable_merge=enable_merge,
            summary_config=summary_config,
            **x86_to_z3_kwargs,
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

        # merged 模式 fail-closed：被剪路径让合并语义失真，必须显式失败。
        coverage_failure = _merged_coverage_failure(evm_result, x86_result)
        if coverage_failure is not None:
            if self.verbose:
                print(f"\n[4] Coverage check failed: {coverage_failure}")
            return False, coverage_failure

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

    def _loop_guard_note(self, evm_program: EVMProgram,
                         x86_program: X86Program) -> Optional[str]:
        """coverage 失败时的循环守卫附注（§6 降级路径的可行动信息）。

        失败容忍：守卫分析自身出错不能掩盖原始失败消息。
        """
        try:
            from x86_64.loop_templates import make_tier2_matcher
            from .loop_pairing import analyze_program_pair

            x86_blocks = getattr(x86_program, "blocks", None) or []
            if not x86_blocks or not evm_program.blocks:
                return None
            by_addr = {b.start_addr: b for b in x86_blocks}
            report = analyze_program_pair(
                evm_program.blocks,
                x86_blocks,
                tier2_matcher=make_tier2_matcher(by_addr),
            )
            lines = [
                "  loop guard: "
                f"{len(report.evm_analysis.loops)} EVM natural loop(s), "
                f"{len(report.x86_analysis.loops)} x86 natural loop(s), "
                f"{len(report.pairs)} Tier-1 pair(s) available for induction"
            ]
            for reason in report.reasons():
                lines.append(f"  loop guard: {reason}")
            return "\n".join(lines)
        except Exception as exc:  # pragma: no cover - 诊断附注不阻塞主流程
            return f"  loop guard: analysis unavailable ({exc})"

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
        max_depth: Optional[int] = None,
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
        evm_to_z3_paths_kwargs = {}
        if max_depth is not None:
            evm_to_z3_paths_kwargs["max_depth"] = max_depth
        evm_paths = evm_program.to_z3_paths(
            initial_state,
            merge_state=stack_check is not None,
            **evm_to_z3_paths_kwargs,
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
        x86_to_z3_paths_kwargs = {}
        if max_depth is not None:
            x86_to_z3_paths_kwargs["max_depth"] = max_depth
        x86_paths = x86_program.to_z3_paths(
            initial_state,
            call_site_mapping=call_site_mapping,
            merge_state=stack_check is not None,
            enable_merge=enable_merge,
            summary_config=summary_config,
            reachability_timeout_ms=x86_reachability_timeout_ms,
            **x86_to_z3_paths_kwargs,
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
                "has_return_data, storage, transient_storage, status_code"
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
            # §6 prove-or-honestly-degrade：coverage 失败通常意味着符号
            # bound 循环——附上循环守卫报告，让降级结论可行动（哪些
            # natural loop、是否可配对、归纳引擎是否适用）。
            if message and "do not cover" in message:
                loop_note = self._loop_guard_note(evm_program, x86_program)
                if loop_note:
                    message = f"{message}\n{loop_note}"
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
    
