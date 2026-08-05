"""
程序等价性验证器。

本模块提供程序级验证功能，
操作整个程序而不是单个块。
"""

import time
from enum import Enum
from typing import Tuple, Optional
from evm_ir.program import EVMProgram
from x86_64.program import X86Program
from x86_64.summaries import X86SummaryConfig
from .refinement_checker import RefinementChecker
from .call_site_mapping import build_call_site_mapping
from state.host_gas import HOST_GAS_UF_KINDS
from state.smt_state import SMTState


class GasCheck(str, Enum):
    """gas 检查模式。每个取值绑定一种初始 gas 配置，verify_program_pair fail-closed 校验。

    - OFF：不比较 gas（功能等价），但**仍要求具体预算**。OFF 下 host gas UF 是关的，
      两侧都不扣 host cost H，于是模型里的 gas 比真实值偏高一个 H —— 凡是依赖 gas 的
      行为（OOG 阈值、`GAS` opcode 的取值、以及由它派生的分支）探索到的都是错误的路径
      集。具体预算**并不能**消除这个缺口，只是关掉了符号 gas 那类最明显的反例；
      `G=1e9, H=999999998, S=3` 就是具体预算下的反例。详见 verify_program_pair 内的说明。
    - FIXED_BUDGET：比较 gas，**要求具体预算**。结论是「从这一个预算出发」的**单点**
      结论，不是 ∀initial_gas。具体值让 `ULT(budget, cost)` 在 simplify 阶段折成 False，
      省掉每个 block 一次可达性查询。
    - FULL：比较 gas，**要求符号 gas**，对所有初始 gas 量化。具体值会把要验的 OOG 分支
      折死，故拒绝。

    两者的差别是「固定一个 gas 点」vs「量化所有 gas」，**不是**「无 OOG 路径」vs「有」：
    FIXED_BUDGET 下依赖符号 offset 的动态 fee 仍能超预算，那类 OOG 分支照样保留。

    结论范围（三个模式共同适用）见 ProgramEquivalenceChecker.__init__。
    """

    OFF = "off"
    FIXED_BUDGET = "fixed_budget"
    FULL = "full"


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


# --- gas 验证准入检查：没建模的动态 gas 指令一律拒验 ---
#
# 跑 gas 检查前先扫一遍程序：碰到"gas 数额随运行时数据变化、而我们没建模"的指令就
# 直接拒绝受理，不出 VERIFIED。判据 = 下面的全表 − 已建模表。
# 用"已建模"这张表做判据（而不是维护一张"不支持"清单），是因为清单漏登记时指令默认
# 放行，两侧都漏扣 gas 反而报 VERIFIED——假绿；这张表漏登记只会多拒。

# 全表：go-hpc-evm `evm/jump_table.go` 里带动态 gas 的全部指令（LOG0..LOG4 记作 "LOG"，
# topic 数在 op.immediate）。
#
# 这张表**手工同步**，最后核对于 commit `b3ddbdb`（与 tests/data/README.md
# 记的 fixture 版本一致）。升级 go-hpc-evm 时必须按下面两条重抽一遍——漏登记的指令不
# 进差集，守卫就不会拦它：
#
#   ① struct literal 里的 `dynamicGas:` 字段（25 处）。
#   ② 赋值形式 `instructionSet[common.X].dynamicGas = f`
#      （:142-155 enable2929 的 SLOAD/BALANCE/EXTCODESIZE/EXTCODEHASH）。
#      grep `"dynamicGas:"` 抓不到这一种，实际漏抽过一次。
_DYNAMIC_GAS_KINDS = frozenset({
    # 内存扩展 / word gas（x86 codegen 可见）
    "MLOAD", "MSTORE", "MSTORE8", "RETURN", "REVERT", "MCOPY",
    "SHA3", "CALLDATACOPY", "CODECOPY", "RETURNDATACOPY", "EXTCODECOPY",
    "LOG",
    "CREATE", "CREATE2",
    # gas 在 Go host/builtin runtime 内（x86 不可见）
    "SLOAD", "SSTORE", "BALANCE", "EXTCODESIZE", "EXTCODEHASH", "SELFDESTRUCT",
    "CALL", "CALLCODE", "DELEGATECALL", "STATICCALL", "EXP",
})

# 已建模分两层（依据见 memory: gas_full_coverage_codegen_layers）。
# 第 1 层，真证明：gas 算式在 x86 codegen 里可见，EVM 侧建了真实公式逐位比较——内存扩展
# 与 word/copy/LOG data gas，走 semantics_gas.charge_memory_and_word_gas / charge_log_gas
# （含 CREATE/CREATE2 的 memoryCreate{,2}GasN、EXTCODECOPY 的 memoryCopierGas(3)）。
_PROVEN_DYNAMIC_GAS_KINDS = frozenset({
    "MLOAD", "MSTORE", "MSTORE8", "RETURN", "REVERT", "MCOPY",
    "SHA3", "CALLDATACOPY", "CODECOPY", "RETURNDATACOPY", "EXTCODECOPY",
    "LOG",
    "CREATE", "CREATE2",
})
# 第 2 层，UF 兜底：gas 在 Go host/builtin runtime 内部算、x86 侧看不见，两侧扣同名
# host_gas_uf 相消。复用 state/host_gas.py 的 HOST_GAS_UF_KINDS，不抄第二份以免两处漂移。
_MODELED_DYNAMIC_GAS_KINDS = _PROVEN_DYNAMIC_GAS_KINDS | HOST_GAS_UF_KINDS

# 人工拒绝钩子：把某个"已建模"的 kind 临时挡回门外（建模有疑点、还没修时用）。
# **当前为空**——EXTCODECOPY/CREATE/CREATE2 曾长期在此，解禁论证见
# docs/Gas一致性验证设计.md §8「EXTCODECOPY / CREATE / CREATE2 的解禁」。
_MANUAL_REJECT_KINDS: frozenset[str] = frozenset()


def _find_unsupported_dynamic_gas_ops(evm_program: EVMProgram) -> list[str]:
    """扫出程序里必须拒验的动态 gas 指令（返回非空 ⇒ 拒绝受理 gas 检查）。

    拒绝集 = (_DYNAMIC_GAS_KINDS - _MODELED_DYNAMIC_GAS_KINDS) | _MANUAL_REJECT_KINDS，
    与 gas_check 模式无关。当前差集为空，但机制不是摆设：新指令只要登记进
    _DYNAMIC_GAS_KINDS 而没接建模，就自动被拦下。

    HOST_GAS_UF_KINDS 在任何模式下都算已建模：gas 数额靠两侧同名 UF 相消，而 host gas
    耗尽后的终止没有对应的生成代码、不算缺口——论证见 state/host_gas.py 模块 docstring。
    结论范围由 _annotate_gas_scope 写进成功消息。
    """
    reject = (_DYNAMIC_GAS_KINDS - _MODELED_DYNAMIC_GAS_KINDS) | _MANUAL_REJECT_KINDS

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


# 曾有 _inject_gas_sufficiency_assumption（注入 UGE(G, Σstatic_gas × 500) 剪 OOG 分支），
# 已删除：它从来不是健全性要求（钳零删掉后，不注入也照样 VERIFIED，只是路径 1→3、
# 全配对 pair 1→9），而 GasCheck.FIXED_BUDGET 的具体预算把同一件事做得更彻底——
# `ULT(budget, cost)` 在 simplify 阶段就折死，不必每个 block 一次可达性查询。


class ProgramEquivalenceChecker:
    """验证EVM和x86程序之间的等价性。"""

    def __init__(self, timeout_ms: int = 60000, verbose: bool = False,
                 gas_check: 'GasCheck | str' = GasCheck.OFF):
        """初始化程序等价性检查器。

        gas 检查的结论范围（所有模式适用，按这个口径读 VERIFIED）：

        - 验 **x86 可见 gas 计算**：makeStaticUseGas、checkMemoryAndCalcDynamicGas* 的
          内存扩展/word/log fee、CALL 系 returnGas 链。
        - host/builtin gas **数额**靠两侧同名 host_gas_uf 相消：证的是「两侧扣同一个数、
          栈参数一致」（能抓参数传错），host 公式本身是 assume。
        - host gas **耗尽后的终止**不在范围内，也不是缺口——那一处没有生成代码。
          理由见 state/host_gas.py 模块 docstring。

        Args:
            timeout_ms: SMT求解器超时（毫秒）
            verbose: 启用详细输出
            gas_check: GasCheck 之一（也接受其字符串值）。各模式语义见 GasCheck。

        Raises:
            ValueError: gas_check 不是合法的 GasCheck 取值。
        """
        # 运行时归一化：类型标注拦不住字符串，而 `self.gas_check is GasCheck.OFF`
        # 这类 identity 判断会把裸字符串 "off" 误当成"已启用 gas 检查"。
        self.gas_check = GasCheck(gas_check)
        self.refinement_checker = RefinementChecker(
            timeout_ms=timeout_ms, verbose=verbose,
            check_gas=self.gas_check is not GasCheck.OFF,
        )
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

        # IR 不变量：有 static_gas 的 block 必须带 TAG。静态 gas 的 OOG 守卫挂在 TAG
        # 序言上，而扣减无条件执行且是纯减法（consume_static 不钳零）——无 TAG 时 gas
        # 不足会回绕成 ~2^64 静默继续，后续 OOG 判断全部失效。
        #
        # 放在 verifier 入口而非 cfg_executor：这是**编译器产出 IR** 的不变量。仓库里大量
        # 合成 EVMBlock（static_gas 非零、无 TAG）直接驱动执行器测裸 CFG，不该被打断。
        bad_blocks = [
            b for b in (getattr(evm_program, "blocks", None) or [])
            if getattr(b, "static_gas", 0)
            and not any((getattr(op, "kind", "") or "").upper() == "TAG"
                        for op in (getattr(b, "operations", None) or []))
        ]
        if bad_blocks:
            sample = ", ".join(f"pc=0x{getattr(b, 'pc', 0):x}" for b in bad_blocks[:8])
            if len(bad_blocks) > 8:
                sample += f", ... (+{len(bad_blocks) - 8} more)"
            return (
                False,
                "✗ IR INVARIANT VIOLATED: block(s) carry static_gas but have no TAG "
                f"operation: {sample}. The static-gas OOG guard lives in the TAG "
                "prologue, so such a block would deduct gas without ever branching "
                "to OUT_OF_GAS — insufficient gas would wrap around instead "
                "(fail-closed)",
            )

        # 未建模动态 gas 的 opcode 必须 fail-closed，避免两侧都漏扣时假绿。
        # （LOG 曾是已知缺口，现已随 charge_log_gas 走 charge_dynamic_gas 补齐。）
        if self.gas_check is not GasCheck.OFF:
            unsupported_dynamic_gas = _find_unsupported_dynamic_gas_ops(evm_program)
            if unsupported_dynamic_gas:
                sample = ", ".join(unsupported_dynamic_gas[:8])
                if len(unsupported_dynamic_gas) > 8:
                    sample += f", ... (+{len(unsupported_dynamic_gas) - 8} more)"
                return (
                    False,
                    "✗ GAS CHECK UNSUPPORTED: these operators are outside the "
                    f"currently provable gas scope: {sample}",
                )

        # --- 初始 gas 配置校验 ---
        from z3 import is_bv_value, simplify

        # 两侧初始 gas 必须同源 —— **所有模式**都查。gas 现在无条件参与控制流（OOG 分叉），
        # 起点不同就不是在比同一个输入程序，`OFF` 也不例外。create_initial_state 用同一个
        # 对象喂 evm_gas 与 callengine_gas_remaining，但调用方拿到 state 后可以改任意字段。
        evm_gas = simplify(initial_state.evm_gas.Gas)
        aot_gas = simplify(initial_state.callengine_gas_remaining)
        if not evm_gas.eq(aot_gas):
            return (
                False,
                "✗ GAS CONFIG REJECTED: initial gas differs between the two sides — "
                f"IR evm_gas={evm_gas}, AOT callengine_gas_remaining={aot_gas}. "
                "Both must start from the same value (fail-closed)",
            )

        # 必须先 simplify 再判 concrete：is_bv_value 只看语法形式，
        # `BitVecVal(1,64) + BitVecVal(2,64)` 语义上就是 3 却返回 False —— 不化简的话
        # FULL 会把这种"语义具体"的 gas 当成符号量接受，实际只验了单点却声称量化全部。
        concrete = is_bv_value(evm_gas)

        # OFF 要求具体预算，但**这不是对下面这个缺口的修复**，只是关掉了其中最明显的
        # 一类反例。缺口本身仍在，如实记在这里：
        #
        # OFF 下 host_gas_uf_enabled 关着，两侧都不扣 host cost H，于是后续可见 gas 检查
        # 判的是 `S > G` 而非真实的 `S > G-H`，`S ≤ G < H+S` 这片真实可达的 OOG 区域被
        # 漏掉——这是 under-approximation，方向上会假绿。具体预算**并不能**消除它：H 是
        # UF，`G=1e9, H=999999998, S=3` 就是一个具体预算下的反例（host 调用成功，扣完剩
        # 2，下一步真实 OOG，而模型仍拿 1e9 去判）。所以 OFF 的结论是**条件性**的：前提
        # 是「预算足够，且不存在受 host 扣费影响的后续 OOG」。该前提由 _annotate_gas_scope
        # 写进每一条 VERIFIED 消息，不靠文档口头声明。
        #
        # **这是刻意保留的取舍，不是待办。** OFF 的定位是最便宜的功能等价筛查：它根本
        # 不比较 gas，开 host UF 对它零收益，却让每条路径都背上 UF 项、OOG 分支重新存活。
        # HOST_GAS_UPPER_BOUNDS 那笔钱花在真正比较 gas 的 FIXED_BUDGET / FULL 两档上
        # （见 state/host_gas.py 与 docs/Gas一致性验证设计.md §7.2）；需要把这个缺口关上
        # 的调用方改用那两档即可。
        if self.gas_check is GasCheck.OFF and not concrete:
            return (
                False,
                "✗ GAS CONFIG REJECTED: GasCheck.OFF requires a concrete initial gas "
                f"budget; got symbolic {evm_gas}. OFF leaves host gas unmodeled, so "
                "with symbolic gas the downstream OOG threshold is short by the host "
                "cost — use GasCheck.FULL to reason over all initial gas values",
            )

        # 比较 gas 的两个模式：形态与模式必须匹配，否则结论含义或求解规模不再是该模式
        # 承诺的那个。这里也由 verifier **自己**打开 host gas UF —— 它默认关，而
        # SLOAD/SSTORE/CALL/EXP 的 host gas 只有这一条路，关着就是 vacuous 通过。
        gas_budget = evm_gas.as_long() if concrete else None
        if self.gas_check is not GasCheck.OFF:
            if self.gas_check is GasCheck.FULL and concrete:
                return (
                    False,
                    "✗ GAS CHECK UNSUPPORTED: GasCheck.FULL requires symbolic gas "
                    "(use create_initial_state(symbolic_gas=True)); got gas that "
                    f"simplifies to the constant {evm_gas}, which folds away the very "
                    "OOG branches FULL is meant to verify (fail-closed)",
                )
            if self.gas_check is GasCheck.FIXED_BUDGET and not concrete:
                return (
                    False,
                    "✗ GAS CHECK UNSUPPORTED: GasCheck.FIXED_BUDGET requires a "
                    "concrete initial gas budget (use create_initial_state() or "
                    f"create_initial_state(gas_budget=...)); got symbolic {evm_gas}. "
                    "Symbolic gas leaves every block's OOG branch feasible, so the "
                    "mode's path-scale promise no longer holds — use GasCheck.FULL "
                    "to verify over all initial gas values",
                )
            initial_state.host_gas_uf_enabled = True

        # gas 检查必须走 path_observations 模式。动态 gas 的 scope assumption
        # （如 ULE(requested, 0x1FFFFFFFE0)）是 path-local 的，而 merged-result 模式
        # 会把所有路径的 assumption 无条件 And 成全局条件，越界约束 sibling 路径 →
        # 假绿（failure_path_assumption_global_leak）。path_observations 模式把
        # assumption And 进各路径自己的 condition，不泄漏。
        if self.gas_check is not GasCheck.OFF and not path_observations:
            path_observations = True
            if self.verbose:
                print("    ├─ gas/OOG check: forcing path_observations=True "
                      "(avoid scope-assumption global leak)")

        if self.verbose:
            print(f"\n=== Program-Level Verification (Alive2-style) ===")
            print(f"┌─ EVM Program: {evm_program}")
            print(f"└─ x86 Program: {x86_program}")

        if path_observations:
            verified, message = self._verify_program_pair_path_observations(
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
            return verified, self._annotate_gas_scope(verified, message, gas_budget)

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
            return verified, self._annotate_gas_scope(verified, message, gas_budget)

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

        return verified, self._annotate_gas_scope(verified, message, gas_budget)

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

    def _annotate_gas_scope(self, verified: bool, message: Optional[str],
                            gas_budget: Optional[int]) -> Optional[str]:
        """把 gas 结论的适用范围写进成功消息。

        库调用方拿不到 CLI 的那行输出，只有这个 message。不写范围的话，
        「FIXED_BUDGET 单点预算下通过」会被读成「所有 gas 下通过」。
        """
        if not verified or not message:
            return message
        if self.gas_check is GasCheck.OFF:
            # 这个缺口为什么是刻意保留的，见 verify_program_pair 内的论证。
            return (
                f"{message} [functional equivalence at the fixed initial gas budget "
                f"{gas_budget}; host gas is NOT modeled in this mode, so the modelled "
                "gas runs high by the host cost and any gas-dependent behaviour "
                "(out-of-gas thresholds, the GAS opcode's value, and branches derived "
                "from either) is explored over the wrong path set — use "
                "GasCheck.FIXED_BUDGET or FULL to close that gap]"
            )
        if self.gas_check is GasCheck.FIXED_BUDGET:
            scope = f"gas equivalent for the fixed initial budget {gas_budget}"
        else:
            scope = "gas and OOG paths equivalent over all initial gas values"
        # 措辞止于"受审计所得上界约束"：上界是 assume，本验证器证不了 host gas 公式，
        # 改强成"按协议扣数"即过度声明（test_gas_modes_do_not_overclaim_bounds 盯着）。
        return (
            f"{message} [{scope}; host gas amounts are shared uninterpreted functions "
            "constrained by externally audited upper bounds — the host gas formulas "
            "themselves are NOT proven here, and host-exhaustion termination is out "
            "of scope]"
        )

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
    
