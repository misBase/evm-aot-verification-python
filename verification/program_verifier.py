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


# 循环上界系数：cfg_executor 的 max_iteration 硬上界（超过即被特殊处理），
# 故任一 block 最多被经过这么多次。用作 gas 恒足 bound 的保守乘子。
_GAS_BOUND_MAX_ITERATION = 500


# gas 验证的指令分层（全覆盖路径 A，见 memory: gas_full_coverage_codegen_layers）。
#
# 已**真证明**的动态 gas（x86 codegen 可见，EVM 侧建真实公式）：
#   阶段 1：MSTORE/RETURN/MLOAD/MSTORE8（内存扩展）、SHA3（内存扩展+word gas）、
#           CALLDATACOPY/CODECOPY/RETURNDATACOPY/MCOPY/REVERT（内存扩展+copy word gas）
#   A 类：LOG0..LOG4（memoryLogGas = 内存扩展 + LogGas + n*TopicGas + size*DataGas，
#         x86 memoryLogGas codegen 全程可见，EVM 侧 _charge_log_gas 建真实公式）。
#
# 已**UF 兜底**（host/builtin gas 不可见，两侧扣同名 host_gas_uf 相消，验证「两侧
# 扣同一 gas + 栈参数一致」，host 公式本身是 assume 非 prove）：
#   SLOAD/SSTORE/BALANCE/EXTCODESIZE/EXTCODEHASH/SELFDESTRUCT（host）、EXP（builtin）、
#   CALL/CALLCODE/DELEGATECALL/STATICCALL（host）。
#   EVM 侧 charge_host_gas_uf + x86 侧 _deduct_host_gas_uf（go_function_semantics），
#   两侧读同一组栈值（功能等价已证相等）扣同名 UF。已移出本拒绝集。
#   CALL 系列额外:x86 的 dealWithAddGas/SubGas returnGas 链是**可见机器码**（反汇编
#   已建模、加减净 0），且 checkMemoryAndCalcDynamicGasCall=nil（无可见内存扩展），
#   故 host UF 即全部 host gas → 可验。
#
# 下面是仍 **fail-closed** 拒绝的指令。它们除 host UF 外，x86 还有**可见**的内存
# 扩展 gas（memoryCreateGasN / ExtCodeCopy）尚未在 EVM 侧对齐建模；只挂 UF 不够，
# 会漏掉可见部分的差异。在可见部分对齐前显式拒绝（fail-closed，不会假绿）。
_DYNAMIC_GAS_UNSUPPORTED_KINDS = frozenset({
    # EXTCODECOPY:x86 有可见内存扩展 + copy word gas（checkMemoryAndCalcDynamicGas
    # ExtCodeCopy），EVM 侧尚未建该可见部分（host UF 已挂）。待对齐可见部分。
    "EXTCODECOPY",
    # CREATE/CREATE2:x86 有可见的内存扩展 + InitCodeWordGas（memoryCreateGasN，
    # checkMemoryAndCalcDynamicGasCreate≠nil），EVM 侧尚未建该可见部分（host UF
    # 已挂、returnGas 链已自动建模）。待对齐可见部分。
    "CREATE",
    "CREATE2",
})


def _find_unsupported_dynamic_gas_ops(evm_program: EVMProgram,
                                      oog_mode: bool = False) -> list[str]:
    """Return dynamic-gas operators that gas checking must still reject.

    全覆盖路径 A 下，gas 验证分两档:**真证明**（x86 可见，已建真实公式）与
    **UF 兜底**（B 类，host 黑盒，两侧同名 host_gas_uf 相消）。本函数返回仍需
    fail-closed 拒绝的指令 = CREATE/CREATE2/EXTCODECOPY:这些指令**两侧的 host
    UF 都已挂好**，但 x86 codegen 还有**可见的内存扩展 gas**（memoryCreateGasN /
    InitCodeWordGas / ExtCodeCopy）尚未在 EVM 侧建模——只靠 UF 相消会漏掉这段
    可见差异，故 fail-closed 拒绝直到 EVM 侧补齐可见部分。返回非空列表是防假绿守卫。

    其余 B 类（SLOAD/SSTORE/BALANCE/EXTCODESIZE/EXTCODEHASH/SELFDESTRUCT/EXP +
    CALL/CALLCODE/DELEGATECALL/STATICCALL）在 **check_gas（阶段 0，gas 恒足）** 下
    已转正、不在拒绝集:它们无可见内存扩展（CALL 系列的 returnGas 链是可见机器码但
    加减净 0、已对齐），host UF 即全部 host gas。LOG（A 类）也不在拒绝集:其 gas 在
    x86 memoryLogGas codegen 全程可见，EVM 侧 _charge_log_gas 镜像真实公式建模。

    **oog_mode（check_oog）额外拒绝 host 动态 gas 指令（HOST_GAS_UF_KINDS）**:
    host UF 只让两侧在 host 调用点**钳零并继续执行**（相消），并**不分叉 host
    动态 gas 耗尽的 OOG 终止路径**。而 EVM 侧目前只对 block 静态 gas 分叉 OOG
    （cfg_executor）。于是 SLOAD/EXP/CALL 等的 host 动态 gas 是否会触发 OOG、
    两侧 OOG 行为是否一致，**根本没有被验证**——OOG 模式放行它们 = 假绿。在补齐
    host 动态 OOG 分叉建模前，check_oog 必须 fail-closed 拒绝这些指令。
    （check_gas 不受影响:gas 恒足前提已剪掉所有 OOG，host UF 相消即足够。）
    """
    from state.host_gas import HOST_GAS_UF_KINDS

    reject = _DYNAMIC_GAS_UNSUPPORTED_KINDS
    if oog_mode:
        reject = reject | HOST_GAS_UF_KINDS

    unsupported: list[str] = []
    for block in getattr(evm_program, "blocks", None) or []:
        for op in getattr(block, "operations", None) or []:
            kind = (getattr(op, "kind", "") or "").upper()
            if kind in reject:
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
                 check_gas: bool = False, check_oog: bool = False):
        """初始化程序等价性检查器。

        Args:
            timeout_ms: SMT求解器超时（毫秒）
            verbose: 启用详细输出
            check_gas: 是否启用 gas 终值一致性检查（阶段 0/1，gas 充足路径终值）。
            check_oog: 是否启用 OOG 路径一致性检查（阶段 3B）。True 时不注入 gas
                恒足假设、放开 EVM 侧 OOG 分叉，验 out-of-gas 路径的 status code
                两侧一致。隐含需要 status 检查（故一并开启 check_gas 的检查通道）。
        """
        self.refinement_checker = RefinementChecker(
            timeout_ms=timeout_ms, verbose=verbose,
            check_gas=check_gas or check_oog,
        )
        self.check_oog = check_oog
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

        # 遇到未建模动态 gas opcode 必须 fail-closed，避免 EVM/x86 两侧都尚未
        # 建模动态扣减/OOG 时出现假绿。check_oog 同样要走此 guard：底层已开启
        # gas/status 检查（RefinementChecker(check_gas=check_gas or check_oog)）。
        # 两类未覆盖情况要区分:
        #   - B 类（EXP/SSTORE/CALL 等）:动态 gas **完全未在 EVM 侧建模**（仅挂
        #     host-gas UF，x86 侧 UF 未接入），由本 guard fail-closed 拒绝。
        #   - LOG（A 类）:动态 gas **已建模**（_charge_log_gas），故不在拒绝集；
        #     但 EVM 侧仅对 block.static_gas 分叉 OOG（cfg_executor），未对 LOG 动态
        #     gas 耗尽分叉 OOG 终止路径。当 gas 足以过 static 检查但不足以覆盖 LOG
        #     动态 gas 时，x86 产生一条 OOG 终止路径而 EVM 不产生 → 该 x86 路径无
        #     对应 EVM 路径，触发 **terminal-path 覆盖检查失败**（"EVM terminal paths
        #     do not cover all inputs"），fail-closed、不假绿（注意:失败现象是覆盖
        #     检查报错，不是 pair 级 gas SAT）。LOG + check_oog 暂不被 guard 拦截，
        #     待 LOG 动态 gas OOG 分叉建模后再完善。
        if self.check_gas or self.check_oog:
            # check_oog 额外拒绝 host 动态 gas 指令:它们的 host 动态 OOG 分叉未
            # 建模（host UF 只两侧钳零续跑、不分叉），放行 = 假绿（见 Fix #2）。
            unsupported_dynamic_gas = _find_unsupported_dynamic_gas_ops(
                evm_program, oog_mode=self.check_oog
            )
            if unsupported_dynamic_gas:
                sample = ", ".join(unsupported_dynamic_gas[:8])
                if len(unsupported_dynamic_gas) > 8:
                    sample += f", ... (+{len(unsupported_dynamic_gas) - 8} more)"
                return (
                    False,
                    "✗ GAS CHECK UNSUPPORTED: dynamic gas operators are not "
                    f"modeled yet for stage 0: {sample}",
                )

        # 阶段 3B（OOG 路径一致性）:放开 EVM 侧 OOG 分叉，**不**注入恒足假设
        # （否则 OOG 恒假被剪）。EVM/x86 各自产生 OOG 终止路径，由 terminal-path
        # pair 检查验 status code（含 out_of_gas=12）两侧一致。
        if self.check_oog:
            # Fix #4:OOG 分叉条件是 ULT(gas, static_gas)。若初始 gas 是具体大常量
            # （默认 create_initial_state() 给 1e9），ULT(1e9, static) 恒假 → 所有
            # OOG 分支被剪 → OOG 一致性根本没验却返回 VERIFIED（假绿）。check_oog
            # 必须 fail-closed 要求 symbolic gas（initial_state 经
            # create_initial_state(symbolic_gas=True) 构造）。
            from z3 import is_bv_value
            gas_sym = initial_state.evm_gas.Gas
            if is_bv_value(gas_sym):
                return (
                    False,
                    "✗ OOG CHECK UNSUPPORTED: check_oog requires symbolic gas "
                    "(use create_initial_state(symbolic_gas=True)); got a concrete "
                    f"gas constant {gas_sym}, which prunes all OOG branches "
                    "(fail-closed to avoid false green)",
                )
            initial_state.gas_modeling_enabled = True
            initial_state.oog_modeling_enabled = True
        # gas 一致性（阶段 0/1）:仅在 gas 检查且非 OOG 模式时注入「gas 恒足」前提
        # （UGE(G, bound)），让两侧 out-of-gas 分支恒假被剪，验 gas 充足路径终值。
        elif self.check_gas:
            _inject_gas_sufficiency_assumption(evm_program, initial_state)

        # gas/OOG 检查强制走 path_observations 模式（修复 scope assumption 全局
        # 泄漏）:动态 gas 的 success-path scope assumption（如 ULE(requested,
        # 0x1FFFFFFFE0)）是 **path-local** 的——merged-result 模式会把所有路径的
        # assumption 无条件 And 成全局 extra_condition，越界约束 sibling 路径
        # （failure_path_assumption_global_leak 病理 → 假绿）。path_observations
        # 模式下 _path_observation 把 assumption And 进**各路径自己的** condition，
        # 不泄漏。多内存操作 + 多路径的真实程序需要这个隔离。
        if (self.check_gas or self.check_oog) and not path_observations:
            path_observations = True
            if self.verbose:
                print("    ├─ gas/OOG check: forcing path_observations=True "
                      "(avoid scope-assumption global leak)")

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
    
