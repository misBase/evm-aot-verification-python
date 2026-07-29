"""单指令 EVM/x86 微精化测试辅助工具。"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Literal

from z3 import (
    And,
    BitVecVal,
    BoolVal,
    Concat,
    Extract,
    If,
    IntVal,
    Not,
    Or,
    Select,
    Solver,
    SolverFor,
    Store,
    Then,
    Z3_BV_SORT,
    Z3_OP_AND,
    Z3_OP_CONCAT,
    Z3_OP_EXTRACT,
    Z3_OP_ITE,
    Z3_OP_NOT,
    eq as z3_eq,
    is_bv_value,
    simplify,
    unsat,
)

from common.div_bridge import verified_div_bridges
from common.uint256 import Uint256
from evm_ir.models import EvmOperator
from evm_ir.semantics import EVMOperationSemantics, evm_operator_to_z3
from state.evm_memory_state import EVMMemoryState
from state.evm_stack_state import EVMStackState
from state.smt_state import MemoryDomain, PointerTag, SMTState
from x86_64.disassembler import disassemble_hex
from x86_64.models import Register
from x86_64.program import X86Program
from x86_64.summaries.registry import X86SummaryConfig


_LIMB_STRIDE_BYTES = 8
_UINT256_SLOT_BYTES = 4 * _LIMB_STRIDE_BYTES
_MAX_SUPPORTED_ARITY = 17
# ITE 裁剪 oracle 的单次判断预算。ADDMOD 的 `sum==mod` 早退路径里，证明 EVM 顶层
# ITE 条件 `Or(mod.iszero, sum.eq(mod))` 在该 path 下恒真，需要 Z3 桥接 x86 借位链
# 与 4-limb 相等，实测刚好 ~1.06s（略超 1s）。给到 5s 后该分支可裁成常量，path 求解
# 从 ~7s 降到亚秒级（对齐独立 MOD）。oracle 仍 fail-closed：unknown/超时一律保留原 AST，
# 提高预算只是更努力地尝试裁剪，soundness 中性。sat/unsat 都立即返回，不会空等。
_PATH_ITE_ORACLE_TIMEOUT_MS = 5_000
_PATH_ITE_MIN_BV_BITS = 64
# 这些 opcode 的 EVM 参照语义是深 ITE 树（SDIV/SMOD 的 abs/sign/MOD 分段；ADDMOD 的
# mod==0 + carry 分支 + 内联 holiman Mod 分段）。逐 x86 终止路径比较时，大部分 ITE 分支
# 在该路径下不可达，但裸比较会让 Z3 同时处理整棵树而 unknown。对这些 kind 启用
# _rewrite_stack_outputs_under_path：在 path 条件下用 fail-closed oracle 裁掉可证不可达的
# 大位宽 ITE 分支，只留该路径对应分支与 x86 对齐（soundness 中性，证不动就保留原 AST）。
_PATH_AWARE_ITE_EVM_KINDS = {"SDIV", "SMOD", "ADDMOD"}
_CALLENGINE_LIMB_ATTRS = {
    0x18: "callengine_memory_size_bytes",
    0x68: "callengine_callvalue",
    0x70: "callengine_gas_remaining",
    0x78: "callengine_self_address_pointer",
    0x80: "callengine_origin_address_pointer",
    0x88: "callengine_caller_address_pointer",
    0x98: "callengine_input_size_bytes",
    0xA8: "callengine_code_size_bytes",
    0xB8: "callengine_return_data_size_bytes",
}


@dataclass(frozen=True)
class InstructionRefinementCase:
    """一条 EVM opcode 及其 x86 核心实现。

    默认把 case 视为纯栈运算：输入是 256-bit 栈值，输出写回第一个操作数槽。
    设置 ``expected_stack_height`` 时改为比较完整的最终栈窗口，用来覆盖
    PUSH/DUP/SWAP/POP 这类会改变栈形状的指令。
    """

    name: str
    evm_kind: str
    arity: int
    x86_core_hex: str
    base_addr: int
    evm_pc: int = 0
    evm_param: int | None = None
    evm_immediate: int | None = None
    evm_is_static: bool = False
    operand_values: tuple[int | None, ...] | None = None
    evm_operand_indices: tuple[int, ...] | None = None
    expected_stack_height: int | None = None
    expected_status_code: int | None = None
    compare_return_metadata: bool = False
    initial_memory_word_offsets: tuple[int, ...] = ()
    initial_calldata_word_offsets: tuple[int, ...] = ()
    initial_code_word_offsets: tuple[int, ...] = ()
    initial_return_data_word_offsets: tuple[int, ...] = ()
    calldata_size_bytes: int | None = None
    code_size_bytes: int | None = None
    return_data_size_bytes: int | None = None
    evm_context_values: tuple[tuple[str, int], ...] = ()
    # 合法跳转目标（JUMPDEST 的 PC）全集，供 JUMP/JUMPI 目标校验使用。
    # 全程序验证时由 SymbolicExecutor 预填充；单指令 case 没有块上下文，需在此显式给出。
    evm_valid_jump_targets: tuple[int, ...] | None = None
    x86_callengine_limb_values: tuple[tuple[int, int], ...] = ()
    x86_stack_byte_values: tuple[tuple[int, int], ...] = ()
    memory_check_offsets: tuple[int, ...] = ()
    storage_check_keys: tuple[int, ...] = ()
    transient_storage_check_keys: tuple[int, ...] = ()
    x86_execution_mode: Literal["linear", "cfg"] = "linear"
    x86_compare_terminal_paths: bool = False
    x86_enable_go_bridge: bool = False
    x86_summary_config: X86SummaryConfig | None = None
    x86_max_depth: int = 50
    solver_timeout_ms: int = 10_000


def assert_instruction_refines(case: InstructionRefinementCase) -> None:
    """证明一条 EVM 操作和对应 x86 核心产生相同的可观测效果。

    纯结果模式用于 AOT 纯栈计算：操作数是 256-bit 栈值，x86 片段把一个
    256-bit 结果原地写回底部/结果操作数槽。栈窗口模式会比较最终栈的每个槽位，
    覆盖 PUSH/DUP/SWAP/POP。两种模式都支持直线片段和不含 host call 的小 CFG。
    """
    operands = _operands(case)
    memory_words = _symbolic_memory_words(case)
    readonly_words = _symbolic_readonly_words(case)
    # 只要需要观察栈形状以外的状态，就切到完整状态比较路径。
    requires_state_comparison = (
        case.expected_stack_height is not None
        or bool(case.memory_check_offsets)
        or bool(case.storage_check_keys)
        or bool(case.transient_storage_check_keys)
        or case.expected_status_code is not None
        or case.compare_return_metadata
    )
    # 收集语义建模在**单条全局路径**上累积的 assumptions（如 EVM 侧 MOD/DIV 的相等
    # 借位链桥接、CALLDATALOAD 的 hi-192==0），与合约验证主路径
    # （verification.program_verifier._collect_assumptions）保持单一来源。
    # 注意：x86 terminal-paths 模式下，各路径的 assumptions 是 path-local 的，必须由
    # _path_observation_mismatches 逐路径 guard，**不**在这里无条件全局添加，否则某条
    # 路径（限制输入空间的）assumption 会越界约束 sibling 路径、藏住其真实 mismatch。
    assumption_states = []
    if not requires_state_comparison:
        evm_result = _normalize_refinement_bv(_build_evm_result(case, operands))
        x86_result = _normalize_refinement_bv(
            _build_x86_result(case, operands, memory_words, readonly_words)
        )
        mismatches = [evm_result != x86_result]
    else:
        evm_state = _build_evm_final_state(case, operands, memory_words, readonly_words)
        assumption_states.append(evm_state)
        if case.x86_execution_mode == "cfg" and case.x86_compare_terminal_paths:
            x86_global_states = _build_x86_final_global_states(
                case,
                operands,
                memory_words,
                readonly_words,
            )
            # x86 path-local assumptions 由 _path_observation_mismatches 逐路径 guard，
            # 不并入 assumption_states（避免无条件全局添加导致 sibling 路径假绿）。
            mismatches = _path_observation_mismatches(case, evm_state, x86_global_states)
        else:
            x86_state = _build_x86_final_state(case, operands, memory_words, readonly_words)
            assumption_states.append(x86_state)
            mismatches = _state_observation_mismatches(case, evm_state, x86_state)

    if not mismatches:
        raise AssertionError(f"{case.name} micro-refinement has no observable checks")

    assumptions = list(_collect_state_assumptions(assumption_states))

    # terminal-paths 模式逐项（逐路径）独立求解，而非一个大 Or(*mismatches) 一次 check。
    # 二者对「整体 unsat」判定等价（Or 的 unsat ⟺ 每个 disjunct unsat），但合成大公式
    # 会让 Z3 在 SDIV/SMOD 这类含多条慢 div 路径的 case 上选择困难而 unknown（实测大 Or
    # 155s unknown，逐路径各自秒级~十几秒 unsat）。非 terminal-paths 模式只有少量 mismatch
    # 项，逐项与单 Or 行为一致。
    for mismatch in mismatches:
        solver = _make_refinement_solver(case)
        solver.set(timeout=case.solver_timeout_ms)
        for assumption in assumptions:
            solver.add(assumption)
        solver.add(mismatch)
        result = solver.check()
        assert result == unsat, (
            f"{case.name} micro-refinement failed: "
            f"opcode={case.evm_kind}, base_addr=0x{case.base_addr:x}, "
            f"execution_mode={case.x86_execution_mode}, "
            f"compare_terminal_paths={case.x86_compare_terminal_paths}, "
            f"x86_core_hex={case.x86_core_hex}, solver_result={result}"
        )


def _make_refinement_solver(case: InstructionRefinementCase):
    """构造求解器。terminal-paths 模式用显式 tactic 链，否则用默认 Solver。

    SDIV/SMOD 的取负+借位链+holiman 分段 ITE 公式，让 Z3 默认 (smt) 策略在纯
    bit-vector 上选择不佳而 unknown（实测单路径 25s+ timeout）。显式
    `simplify → propagate-values → simplify → bit-blast → sat` 先用常量传播/化简把
    路径条件已固定的符号（如取负分支、IsZero/lt 判断）折掉，再 bit-blast 求解，
    同一路径 0.x~数秒 unsat。该 tactic 只改求解策略、不改语义，unsat 结论可信；
    与 verified_div_bridges 桥接协同（缺一不可：桥接消 div 实参 AST 差，tactic 消
    取负/分段 ITE 的求解开销）。

    NOTE 与生产路径的差异：这里比较的是**裸栈值** `evm_stack[i] != x86_val`，QF_AUFBV
    单独搞不定 SMOD 的取负/ITE（实测 281s 仍有 fail），故需此 bit-blast tactic。生产
    refinement（verification/）比较的是经 Store/Select 包裹的 memory/storage array 值，
    QF_AUFBV 的数组理论会先把 Select(Store(...)) 化简，配合 _RefinementContext.add_div_bridges
    注入同一桥接即可秒解（实测 SMOD 早退路径 1.3s），无需此 tactic。两侧差异源于比较表达式
    形态不同，不是重复造轮子。
    """
    if case.x86_execution_mode == "cfg" and case.x86_compare_terminal_paths:
        return Then(
            "simplify",
            "propagate-values",
            "simplify",
            "bit-blast",
            "sat",
        ).solver()
    return Solver()


def _normalize_refinement_bv(expr):
    """把按 byte 存取绕回来的表达式折叠回 word 级表达式。"""
    # x86 侧的 256-bit 值经 byte-array memory store/load 后，常会变成
    # Concat(If(c, 0, Extract(byte, x)), ...)。这里仅把这种严格连续、
    # 同条件、同来源的形状折回 If(c, 0, Extract(word, x))，避免让 Z3
    # 为纯粹的 byte 重组噪音做昂贵 bit-blast。
    return _fold_bytewise_ite_concat(simplify(expr))


def _fold_bytewise_ite_concat(expr):
    parts = _flatten_concat(expr)
    if len(parts) <= 1:
        return expr

    folded = _try_fold_bytewise_zero_ite_concat(parts)
    if folded is not None:
        return folded

    return expr


def _flatten_concat(expr):
    if expr.decl().kind() != Z3_OP_CONCAT:
        return [expr]

    parts = []
    for index in range(expr.num_args()):
        parts.extend(_flatten_concat(expr.arg(index)))
    return parts


def _try_fold_bytewise_zero_ite_concat(parts):
    # 只接受 If(cond, 0, Extract(..., source)) 且 Extract 范围从高到低连续
    # 的 concat；任何条件、来源、顺序或分支形状不一致都会放弃折叠。
    condition = None
    source = None
    high = None
    next_low = None
    total_size = 0

    for part in parts:
        if part.decl().kind() != Z3_OP_ITE or part.num_args() != 3:
            return None

        part_condition = part.arg(0)
        zero_branch = part.arg(1)
        value_branch = part.arg(2)
        if not is_bv_value(zero_branch) or zero_branch.as_long() != 0:
            return None
        if value_branch.decl().kind() != Z3_OP_EXTRACT:
            return None

        extract_high, extract_low = value_branch.decl().params()
        if extract_high - extract_low + 1 != zero_branch.size():
            return None

        value_source = value_branch.arg(0)
        if condition is None:
            condition = part_condition
            source = value_source
            high = extract_high
        elif not condition.eq(part_condition) or not source.eq(value_source):
            return None

        if next_low is not None and extract_high != next_low - 1:
            return None

        next_low = extract_low
        total_size += zero_branch.size()

    if condition is None or source is None or high is None or next_low is None:
        return None

    return If(condition, BitVecVal(0, total_size), Extract(high, next_low, source))


def _operands(case: InstructionRefinementCase) -> list[Uint256]:
    if not 0 <= case.arity <= _MAX_SUPPORTED_ARITY:
        raise ValueError(
            f"{case.name}: arity must be between 0 and "
            f"{_MAX_SUPPORTED_ARITY}, got {case.arity}"
        )
    values = case.operand_values or (None,) * case.arity
    if len(values) != case.arity:
        raise ValueError(
            f"{case.name}: operand_values length must match arity, "
            f"got {len(values)} for arity {case.arity}"
        )
    return [
        Uint256.symbolic(f"{case.name.lower()}_arg{i}") if value is None else Uint256.from_int(value)
        for i, value in enumerate(values)
    ]


def _symbolic_memory_words(case: InstructionRefinementCase) -> list[Uint256]:
    return [
        Uint256.symbolic(f"{case.name.lower()}_mem{i}")
        for i, _ in enumerate(case.initial_memory_word_offsets)
    ]


def _symbolic_readonly_words(case: InstructionRefinementCase) -> dict[str, list[Uint256]]:
    return {
        "calldata": [
            Uint256.symbolic(f"{case.name.lower()}_calldata{i}")
            for i, _ in enumerate(case.initial_calldata_word_offsets)
        ],
        "code": [
            Uint256.symbolic(f"{case.name.lower()}_code{i}")
            for i, _ in enumerate(case.initial_code_word_offsets)
        ],
        "return_data": [
            Uint256.symbolic(f"{case.name.lower()}_returndata{i}")
            for i, _ in enumerate(case.initial_return_data_word_offsets)
        ],
    }


def _collect_state_assumptions(states):
    """从一组 SMTState 收集去重后的 .assumptions（跳过 None）。

    与合约验证主路径 verification.program_verifier._collect_assumptions 同款逻辑，
    保证测试侧与主路径用单一来源（state.assumptions）注入 solver。语义建模函数
    （如 MOD/DIV 的相等借位链桥接、CALLDATALOAD 的 hi-192==0）通过
    SMTState.add_assumption 把恒真/无损先验挂到 state，这里统一取出。
    """
    seen = set()
    out = []
    for state in states:
        if state is None:
            continue
        for assumption in getattr(state, "assumptions", None) or []:
            key = assumption.hash()
            if key in seen:
                continue
            seen.add(key)
            out.append(assumption)
    return out


class _PathIteOracle:
    """用于判断 path condition 是否蕴含 ITE 选支的小型 fail-closed oracle。"""

    def __init__(self, path_conjuncts):
        self._solver = SolverFor("QF_AUFBV")
        self._solver.set(timeout=_PATH_ITE_ORACLE_TIMEOUT_MS)
        for conjunct in path_conjuncts:
            self._solver.add(conjunct)
        self._cache = {}

    def proves_unsat(self, extra_constraint) -> bool:
        key = extra_constraint.hash()
        for cached_expr, cached_result in self._cache.get(key, ()):
            if z3_eq(cached_expr, extra_constraint):
                return cached_result

        self._solver.push()
        self._solver.add(extra_constraint)
        result = self._solver.check() == unsat
        self._solver.pop()

        self._cache.setdefault(key, []).append((extra_constraint, result))
        return result


def _rewrite_stack_outputs_under_path(
    evm_stack,
    x86_stack,
    condition,
    path_assumptions,
    base_assumptions,
):
    """在当前路径下裁掉不可达的大位宽 BV ITE 分支。

    terminal-path 微测试比较的是裸栈表达式。SDIV/SMOD 的这些表达式里会保留
    abs/sign/MOD 的深层 ITE，而生产路径的 array-shaped 检查通常会更早被
    Store/Select 化简掉。这里的改写是 soundness 中性的：只有在当前路径条件
    与已注入 assumptions 能证明另一支不可达时才选支；证明不了（unknown）就
    保留原 AST。
    """
    path_conjuncts = _flatten_bool_conjuncts(
        And(condition, *path_assumptions, *base_assumptions)
    )
    oracle = _PathIteOracle(path_conjuncts)
    cache = {}
    return (
        tuple(
            _rewrite_large_bv_ites_under_path(expr, path_conjuncts, oracle, cache)
            for expr in evm_stack
        ),
        tuple(
            _rewrite_large_bv_ites_under_path(expr, path_conjuncts, oracle, cache)
            for expr in x86_stack
        ),
    )


def _flatten_bool_conjuncts(expr):
    if hasattr(expr, "decl") and expr.decl().kind() == Z3_OP_AND:
        out = []
        for child in expr.children():
            out.extend(_flatten_bool_conjuncts(child))
        return out
    return [expr]


def _negate_syntactic(expr):
    try:
        if expr.decl().kind() == Z3_OP_NOT and len(expr.children()) == 1:
            return expr.children()[0]
    except Exception:
        pass
    try:
        return Not(expr)
    except Exception:
        return None


def _bool_in_conjuncts(path_conjuncts, expr) -> bool:
    return any(z3_eq(conjunct, expr) for conjunct in path_conjuncts)


def _is_large_bv_expr(expr) -> bool:
    try:
        return (
            expr.sort().kind() == Z3_BV_SORT
            and expr.size() >= _PATH_ITE_MIN_BV_BITS
        )
    except Exception:
        return False


def _rewrite_large_bv_ites_under_path(expr, path_conjuncts, oracle, cache):
    cache_key = expr.get_id()
    if cache_key in cache:
        return cache[cache_key]

    try:
        kind = expr.decl().kind()
    except Exception:
        cache[cache_key] = expr
        return expr

    if kind == Z3_OP_ITE and len(expr.children()) == 3:
        cond, then_branch, else_branch = expr.children()
        neg_cond = _negate_syntactic(cond)

        if _bool_in_conjuncts(path_conjuncts, cond):
            out = _rewrite_large_bv_ites_under_path(
                then_branch, path_conjuncts, oracle, cache
            )
            cache[cache_key] = out
            return out
        if neg_cond is not None and _bool_in_conjuncts(path_conjuncts, neg_cond):
            out = _rewrite_large_bv_ites_under_path(
                else_branch, path_conjuncts, oracle, cache
            )
            cache[cache_key] = out
            return out

        if _is_large_bv_expr(expr):
            if neg_cond is not None and oracle.proves_unsat(neg_cond):
                out = _rewrite_large_bv_ites_under_path(
                    then_branch, path_conjuncts, oracle, cache
                )
                cache[cache_key] = out
                return out
            if oracle.proves_unsat(cond):
                out = _rewrite_large_bv_ites_under_path(
                    else_branch, path_conjuncts, oracle, cache
                )
                cache[cache_key] = out
                return out

    children = expr.children()
    if children:
        rewritten_children = [
            _rewrite_large_bv_ites_under_path(child, path_conjuncts, oracle, cache)
            for child in children
        ]
        if any(
            not z3_eq(old, new)
            for old, new in zip(children, rewritten_children, strict=True)
        ):
            try:
                out = expr.decl()(*rewritten_children)
                cache[cache_key] = out
                return out
            except Exception:
                pass

    cache[cache_key] = expr
    return expr


def _build_evm_result(case: InstructionRefinementCase, operands: list[Uint256]):
    op = _evm_operator(case)
    indices = case.evm_operand_indices or tuple(range(case.arity))
    if len(indices) != case.arity:
        raise ValueError(
            f"{case.name}: evm_operand_indices length must match arity, "
            f"got {len(indices)} for arity {case.arity}"
        )
    if any(index < 0 or index >= case.arity for index in indices):
        raise ValueError(
            f"{case.name}: evm_operand_indices must refer to operands "
            f"0..{case.arity - 1}, got {indices}"
        )
    inputs = [operands[index].to_bv256() for index in indices]
    return EVMOperationSemantics().operation_semantics(op, inputs)


def _consume_pending_errors(state: SMTState) -> SMTState:
    """把 opcode 产生的错误分支合并回单个 state（单指令桩专用）。

    单指令桩没有 CFG executor 来分裂终止状态，但也不能直接丢弃 pending_errors
    ——那样错误路径会静默消失。这里按错误条件做 ITE 合并，语义与
    ``EVMProgram._merge_global_states`` 一致：错误分支用错误瞬间的快照，
    正常分支用 post-state；条件恒真/恒假时自动退化成单分支。
    """
    pending = list(state.pending_errors)
    state.pending_errors = []
    if not pending:
        return state

    from state.smt_state import EVMStorageState, EVMTransientStorageState
    from evm_ir.status_code import set_terminal_status

    merged = state
    negations = []
    for branch in pending:
        cond = branch.condition
        if negations:
            cond = simplify(And(cond, *negations))
        negations.append(Not(branch.condition))

        error_state = branch.terminal_state
        set_terminal_status(error_state, branch.status_code)
        error_state.return_offset = BitVecVal(0, 64)
        error_state.return_length = BitVecVal(0, 64)

        combined = SMTState._create_empty()
        combined.__dict__.update(merged.__dict__)
        combined.pending_errors = []
        combined.error_code = If(cond, error_state.error_code, merged.error_code)
        combined.return_offset = If(cond, error_state.return_offset, merged.return_offset)
        combined.return_length = If(cond, error_state.return_length, merged.return_length)
        combined.evm_memory = EVMMemoryState(
            memory_array=If(cond, error_state.evm_memory.Memory, merged.evm_memory.Memory),
            msize=If(cond, error_state.evm_memory.MSize, merged.evm_memory.MSize),
        )
        combined.evm_stack = EVMStackState(
            stack_array=If(cond, error_state.evm_stack.Stack, merged.evm_stack.Stack),
            sp=If(cond, error_state.evm_stack.SP, merged.evm_stack.SP),
        )
        combined.evm_storage = EVMStorageState(
            storage_array=If(cond, error_state.evm_storage.Storage, merged.evm_storage.Storage),
        )
        combined.evm_transient_storage = EVMTransientStorageState(
            storage_array=If(
                cond,
                error_state.evm_transient_storage.TransientStorage,
                merged.evm_transient_storage.TransientStorage,
            ),
        )
        merged = combined

    return merged


def _build_evm_initial_state(
    case: InstructionRefinementCase,
    operands: list[Uint256],
    memory_words: list[Uint256],
    readonly_words: dict[str, list[Uint256]],
) -> SMTState:
    """构造 EVM 侧的初始状态（操作数已压栈，环境已就位）。

    单独暴露，便于测试用同一批符号操作数跑整个 EVMProgram——例如需要
    ``<op>; STOP`` 才能与含 STOP 的 x86 core 对齐时。
    """
    state = SMTState()
    state.evm_stack = EVMStackState(sp=IntVal(0))
    # EVM 侧直接把操作数压入符号栈，再交给 opcode 语义执行。
    for operand in operands:
        state.evm_stack = state.evm_stack.push(operand.to_bv256())
    for offset, word in zip(case.initial_memory_word_offsets, memory_words, strict=True):
        state.evm_memory = state.evm_memory.store_256bit(
            BitVecVal(offset, 64),
            word.to_bv256(),
        )
    _initialize_evm_readonly_sources(state, case, readonly_words)
    _initialize_evm_context_values(state, case)
    if case.evm_valid_jump_targets is not None:
        state.valid_jump_targets = set(case.evm_valid_jump_targets)
    return state


def _build_evm_final_state(
    case: InstructionRefinementCase,
    operands: list[Uint256],
    memory_words: list[Uint256],
    readonly_words: dict[str, list[Uint256]],
) -> SMTState:
    state = _build_evm_initial_state(case, operands, memory_words, readonly_words)
    return _consume_pending_errors(evm_operator_to_z3(_evm_operator(case), state))


def _extract_evm_stack_outputs(final_state: SMTState, expected_stack_height: int):
    return tuple(
        Select(final_state.evm_stack.Stack, IntVal(slot_index))
        for slot_index in range(expected_stack_height)
    )


def _build_x86_result(
    case: InstructionRefinementCase,
    operands: list[Uint256],
    memory_words: list[Uint256],
    readonly_words: dict[str, list[Uint256]],
):
    state = _build_x86_final_state(case, operands, memory_words, readonly_words)
    return _load_stack_slot(state, case.arity, 0)


def _build_x86_final_state(
    case: InstructionRefinementCase,
    operands: list[Uint256],
    memory_words: list[Uint256],
    readonly_words: dict[str, list[Uint256]],
) -> SMTState:
    initial_memory = _build_aot_stack_memory(operands)
    initial_evm_memory = _build_aot_evm_memory(case, memory_words)
    return _execute_x86_core(case, initial_memory, initial_evm_memory, readonly_words)


def _build_x86_final_global_states(
    case: InstructionRefinementCase,
    operands: list[Uint256],
    memory_words: list[Uint256],
    readonly_words: dict[str, list[Uint256]],
):
    initial_memory = _build_aot_stack_memory(operands)
    initial_evm_memory = _build_aot_evm_memory(case, memory_words)
    state = _build_x86_initial_state(case, initial_memory, initial_evm_memory, readonly_words)
    return _execute_x86_core_cfg_global_states(case, state)


def _extract_x86_stack_outputs(state: SMTState, arity: int, expected_stack_height: int):
    return tuple(
        _load_stack_slot(state, arity, slot_index)
        for slot_index in range(expected_stack_height)
    )


def _build_aot_stack_memory(operands: list[Uint256]):
    memory = {}
    # AOT 栈槽按 4 个 64-bit limb 存放一个 256-bit 操作数。
    for operand, offsets in zip(operands, _operand_limb_offsets(len(operands)), strict=True):
        for offset, limb in zip(
            offsets,
            (operand.z0, operand.z1, operand.z2, operand.z3),
            strict=True,
        ):
            memory[offset] = limb
    return memory


def _build_aot_evm_memory(case: InstructionRefinementCase, memory_words: list[Uint256]):
    memory = {}
    for offset, word in zip(case.initial_memory_word_offsets, memory_words, strict=True):
        value = word.to_bv256()
        # EVM memory 是 byte-addressed，需要把 256-bit word 拆成 32 个 byte。
        for byte_index in range(32):
            memory[offset + byte_index] = Extract(
                255 - 8 * byte_index,
                248 - 8 * byte_index,
                value,
            )
    return memory


def _execute_x86_core(
    case: InstructionRefinementCase,
    initial_memory,
    initial_evm_memory,
    readonly_words: dict[str, list[Uint256]],
):
    state = _build_x86_initial_state(case, initial_memory, initial_evm_memory, readonly_words)

    if case.x86_execution_mode == "cfg":
        return _execute_x86_core_cfg(case, state)
    if case.x86_execution_mode != "linear":
        raise ValueError(
            f"{case.name}: x86_execution_mode must be 'linear' or 'cfg', "
            f"got {case.x86_execution_mode!r}"
        )
    return _execute_x86_core_linear(case, state)


def _build_x86_initial_state(
    case: InstructionRefinementCase,
    initial_memory,
    initial_evm_memory,
    readonly_words: dict[str, list[Uint256]],
):
    state = SMTState()
    # AOT 约定：R15 指向 callEngine/EVM 上下文，未标注内存默认按栈域解释。
    state.x86_registers.set_register(Register.R13, BitVecVal(0, 64))
    state.x86_registers.set_register(Register.R14, BitVecVal(0, 64))
    state.x86_registers.set_register(Register.R15, BitVecVal(0, 64))
    state.x86_registers.set_pointer_tag(Register.R15, PointerTag.EVM_PTR)
    state.unrouted_memory_domain = MemoryDomain.STACK
    _initialize_evm_context_values(state, case)

    for offset, value in initial_memory.items():
        state.x86_memory = state.x86_memory.store_limb(
            BitVecVal(offset, 64),
            value,
            domain=MemoryDomain.STACK,
        )
    for offset, value in initial_evm_memory.items():
        state.x86_memory = state.x86_memory.store_byte(
            BitVecVal(offset, 64),
            value,
            domain=MemoryDomain.EVM,
        )
    _initialize_x86_readonly_sources(state, case, readonly_words)
    _initialize_x86_callengine_limb_values(state, case)
    _initialize_x86_stack_byte_values(state, case)

    return state


def _initialize_evm_readonly_sources(
    state: SMTState,
    case: InstructionRefinementCase,
    readonly_words: dict[str, list[Uint256]],
) -> None:
    state.calldata = _store_words_in_byte_array(
        state.calldata,
        case.initial_calldata_word_offsets,
        readonly_words["calldata"],
    )
    state.code = _store_words_in_byte_array(
        state.code,
        case.initial_code_word_offsets,
        readonly_words["code"],
    )
    state.return_data = _store_words_in_byte_array(
        state.return_data,
        case.initial_return_data_word_offsets,
        readonly_words["return_data"],
    )
    calldata_size = _initialize_calldata_size(state, case)
    state.callengine_input_size_bytes = calldata_size
    if case.code_size_bytes is not None:
        state.callengine_code_size_bytes = BitVecVal(case.code_size_bytes, 64)
    if case.return_data_size_bytes is not None:
        state.callengine_return_data_size_bytes = BitVecVal(case.return_data_size_bytes, 64)


def _initialize_evm_context_values(state: SMTState, case: InstructionRefinementCase) -> None:
    for field_name, value in case.evm_context_values:
        if field_name == "gas":
            state.evm_gas.Gas = BitVecVal(value, 64)
        elif field_name in {"block_timestamp", "block_number", "gaslimit", "blobbasefee", "blobhash_count"}:
            setattr(state, field_name, BitVecVal(value, 64))
        else:
            setattr(state, field_name, BitVecVal(value, 256))


def _initialize_x86_readonly_sources(
    state: SMTState,
    case: InstructionRefinementCase,
    readonly_words: dict[str, list[Uint256]],
) -> None:
    state.calldata = _store_words_in_byte_array(
        state.calldata,
        case.initial_calldata_word_offsets,
        readonly_words["calldata"],
    )
    state.code = _store_words_in_byte_array(
        state.code,
        case.initial_code_word_offsets,
        readonly_words["code"],
    )
    state.return_data = _store_words_in_byte_array(
        state.return_data,
        case.initial_return_data_word_offsets,
        readonly_words["return_data"],
    )

    _store_callengine_limb(state, 0x90, BitVecVal(0, 64))
    _store_callengine_limb(state, 0xA0, BitVecVal(0, 64))
    _store_callengine_limb(state, 0xB0, BitVecVal(0, 64))
    calldata_size = _initialize_calldata_size(state, case)
    state.callengine_input_size_bytes = calldata_size
    _store_callengine_limb(state, 0x98, calldata_size)
    if case.code_size_bytes is not None:
        size = BitVecVal(case.code_size_bytes, 64)
        state.callengine_code_size_bytes = size
        _store_callengine_limb(state, 0xA8, size)
    if case.return_data_size_bytes is not None:
        size = BitVecVal(case.return_data_size_bytes, 64)
        state.callengine_return_data_size_bytes = size
        _store_callengine_limb(state, 0xB8, size)


def _initialize_x86_callengine_limb_values(
    state: SMTState,
    case: InstructionRefinementCase,
) -> None:
    for offset, value in case.x86_callengine_limb_values:
        value_bv = BitVecVal(value, 64)
        _store_callengine_limb(state, offset, value_bv)
        attr = _CALLENGINE_LIMB_ATTRS.get(offset)
        if attr is not None:
            setattr(state, attr, value_bv)


def _initialize_x86_stack_byte_values(
    state: SMTState,
    case: InstructionRefinementCase,
) -> None:
    for offset, value in case.x86_stack_byte_values:
        state.x86_memory = state.x86_memory.store_byte(
            BitVecVal(offset, 64),
            BitVecVal(value, 8),
            domain=MemoryDomain.STACK,
        )


def _initialize_calldata_size(state: SMTState, case: InstructionRefinementCase):
    """返回 EVM 视图和 x86 callEngine 视图共用的 calldata size。"""
    if case.calldata_size_bytes is None:
        return state.calldatasize

    size = BitVecVal(case.calldata_size_bytes, 64)
    state.calldatasize = size
    return size


def _store_words_in_byte_array(array, offsets: tuple[int, ...], words: list[Uint256]):
    for offset, word in zip(offsets, words, strict=True):
        value = word.to_bv256()
        for byte_index in range(32):
            array = Store(
                array,
                BitVecVal(offset + byte_index, 64),
                Extract(255 - 8 * byte_index, 248 - 8 * byte_index, value),
            )
    return array


def _store_callengine_limb(state: SMTState, offset: int, value) -> None:
    state.x86_memory = state.x86_memory.store_limb(
        BitVecVal(offset, 64),
        value,
        domain=MemoryDomain.CALLENGINE,
    )


def _execute_x86_core_linear(case: InstructionRefinementCase, state: SMTState) -> SMTState:
    for instruction in disassemble_hex(case.x86_core_hex, base_addr=case.base_addr):
        state = instruction.to_z3(state)

    return state


def _execute_x86_core_cfg(case: InstructionRefinementCase, state: SMTState) -> SMTState:
    program = X86Program.from_hex(case.x86_core_hex, base_addr=case.base_addr)
    # 走 to_z3_paths 而非 to_z3，是为了拿到 coverage 证书：to_z3 在所有终止路径都被
    # depth 剪枝时会静默退化成 _empty_result（初始 state，EVM memory 全 0），让逐项检查
    # 把「x86 根本没执行完」误判成真 mismatch（假 SAT）。这正是 CALLDATACOPY copy-loop
    # 在 depth=120 下踩到的坑。这里 fail-closed：终止路径为空且 coverage 显示 depth-pruned
    # 时直接报错（提示调大 x86_max_depth），绝不静默用退化 state 比较。
    paths = program.to_z3_paths(
        state,
        max_depth=case.x86_max_depth,
        enable_go_bridge=case.x86_enable_go_bridge,
        enable_merge=False,
        merge_state=True,
        summary_config=case.x86_summary_config,
    )
    if not paths.global_states:
        _raise_no_terminal_paths(case, paths.coverage)
    return paths.merged_state


def _execute_x86_core_cfg_global_states(case: InstructionRefinementCase, state: SMTState):
    program = X86Program.from_hex(case.x86_core_hex, base_addr=case.base_addr)
    paths = program.to_z3_paths(
        state,
        max_depth=case.x86_max_depth,
        enable_go_bridge=case.x86_enable_go_bridge,
        enable_merge=False,
        merge_state=False,
        summary_config=case.x86_summary_config,
    )
    if not paths.global_states:
        _raise_no_terminal_paths(case, paths.coverage)
    return paths.global_states


def _raise_no_terminal_paths(case: InstructionRefinementCase, coverage) -> None:
    """终止路径为空时 fail-closed 报错，并区分 depth 剪枝与真不可达。

    coverage 不完整且含 depth-pruned，说明唯一的终止路径在走到 ret 前就被
    cfg_executor 的 depth 剪枝丢弃了（典型如 copy-loop 复制 N 字节需要 ~N 圈迭代，
    x86_max_depth 给小了）。这种情况下若让上游静默退化成空 state 再比较，会产生
    误导性的假 SAT/假 PASS，所以这里显式报错并提示调大 depth。
    """
    detail = ""
    if coverage is not None:
        coverage_details = dict(getattr(coverage, "details", ()) or ())
        depth_pruned = coverage_details.get("depth_pruned_states", 0)
        if not getattr(coverage, "complete", True) and depth_pruned:
            detail = (
                f" coverage incomplete (depth_pruned_states={depth_pruned}); "
                f"x86_max_depth={case.x86_max_depth} likely too small for this "
                f"copy/loop body — increase it"
            )
        elif getattr(coverage, "reason", None):
            detail = f" coverage reason: {coverage.reason}"
    raise ValueError(
        f"{case.name}: cfg execution produced no terminal paths.{detail}"
    )


def _state_observation_mismatches(
    case: InstructionRefinementCase,
    evm_state: SMTState,
    x86_state: SMTState,
):
    mismatches = []
    if case.expected_stack_height is not None:
        mismatches.append(evm_state.evm_stack.SP != IntVal(case.expected_stack_height))
        evm_stack = _extract_evm_stack_outputs(evm_state, case.expected_stack_height)
        x86_stack = _extract_x86_stack_outputs(x86_state, case.arity, case.expected_stack_height)
        mismatches.extend(evm != x86 for evm, x86 in zip(evm_stack, x86_stack, strict=True))
    if case.expected_status_code is not None:
        mismatches.append(
            x86_state.callengine_status_code != BitVecVal(case.expected_status_code, 8)
        )
    if case.compare_return_metadata:
        mismatches.extend(
            (
                evm_state.return_offset != x86_state.return_offset,
                evm_state.return_length != x86_state.return_length,
            )
        )
    mismatches.extend(_memory_mismatches(case, evm_state, x86_state))
    mismatches.extend(_storage_mismatches(case, evm_state, x86_state))
    mismatches.extend(_transient_storage_mismatches(case, evm_state, x86_state))
    return mismatches


def _path_observation_mismatches(
    case: InstructionRefinementCase,
    evm_state: SMTState,
    x86_global_states,
):
    if not x86_global_states:
        return [BoolVal(True)]

    mismatches = []
    if case.expected_stack_height is not None:
        mismatches.append(evm_state.evm_stack.SP != IntVal(case.expected_stack_height))
        evm_stack = _extract_evm_stack_outputs(evm_state, case.expected_stack_height)
    else:
        evm_stack = ()

    path_conditions = [gstate.get_constraints().as_bool() for gstate in x86_global_states]
    # x86 至少要有一条终止路径可行；随后逐路径比较该路径下的观测值。
    mismatches.append(Not(Or(*path_conditions)))

    for condition, gstate in zip(path_conditions, x86_global_states, strict=True):
        path_mismatches = []
        path_assumptions = getattr(gstate.mstate, "assumptions", None) or []
        base_assumptions = getattr(evm_state, "assumptions", None) or []
        evm_stack_for_bridge = ()
        x86_stack_for_bridge = ()
        if case.expected_stack_height is not None:
            x86_stack = _extract_x86_stack_outputs(
                gstate.mstate,
                case.arity,
                case.expected_stack_height,
            )
            if case.evm_kind in _PATH_AWARE_ITE_EVM_KINDS:
                evm_stack_for_bridge, x86_stack_for_bridge = (
                    _rewrite_stack_outputs_under_path(
                        evm_stack,
                        x86_stack,
                        condition,
                        path_assumptions,
                        base_assumptions,
                    )
                )
            else:
                evm_stack_for_bridge = evm_stack
                x86_stack_for_bridge = x86_stack
            path_mismatches.extend(
                evm != x86
                for evm, x86 in zip(
                    evm_stack_for_bridge,
                    x86_stack_for_bridge,
                    strict=True,
                )
            )
        if case.expected_status_code is not None:
            path_mismatches.append(
                gstate.mstate.callengine_status_code != BitVecVal(case.expected_status_code, 8)
            )
        if case.compare_return_metadata:
            path_mismatches.extend(
                (
                    evm_state.return_offset != gstate.mstate.return_offset,
                    evm_state.return_length != gstate.mstate.return_length,
                )
            )
        path_mismatches.extend(_memory_mismatches(case, evm_state, gstate.mstate))
        path_mismatches.extend(_storage_mismatches(case, evm_state, gstate.mstate))
        path_mismatches.extend(_transient_storage_mismatches(case, evm_state, gstate.mstate))

        if path_mismatches:
            # 把该路径自身的 assumptions（如 CALLDATALOAD 的 hi-192==0）作为 guard
            # 合进本路径 mismatch 的前置条件，等价 `condition ∧ assumptions ⇒ 检查`。
            # 否则某条路径的（限制输入空间的）assumption 若被无条件全局添加，会越界
            # 约束 sibling 路径、把其真实 mismatch 藏成假绿。对齐生产代码
            # x86_64/program.py:_path_observation 把 path assumptions And 进 condition。
            # SDIV/SMOD 等取负后再除的路径：EVM 与 x86 的除法子表达式数学相等但 AST 形式
            # 不同（取负 limb 链微差），Z3 证两个 256-bit bvudiv 相等需 bit-blast 而 unknown。
            # 在该路径下逐对生成 `evm_div == x86_div` 桥接（恒真、纯提速），让 solver 跳过
            # bit-blast。每对桥接都先 fail-closed 验证「实参在 path 下可证恒等」才加入，
            # 配对错误绝不假绿。
            div_bridges = verified_div_bridges(
                evm_stack_for_bridge,
                x86_stack_for_bridge,
                And(condition, *path_assumptions),
                assumptions=base_assumptions,
            )
            mismatches.append(
                And(condition, *path_assumptions, *div_bridges, Or(*path_mismatches))
            )

    return mismatches


def _memory_mismatches(case: InstructionRefinementCase, evm_state: SMTState, x86_state: SMTState):
    return [
        Select(evm_state.evm_memory.Memory, BitVecVal(offset, 64))
        != x86_state.x86_memory.load_byte(BitVecVal(offset, 64), domain=MemoryDomain.EVM)
        for offset in case.memory_check_offsets
    ]


def _storage_mismatches(case: InstructionRefinementCase, evm_state: SMTState, x86_state: SMTState):
    return [
        evm_state.evm_storage.sload(BitVecVal(key, 256))
        != x86_state.evm_storage.sload(BitVecVal(key, 256))
        for key in case.storage_check_keys
    ]


def _transient_storage_mismatches(
    case: InstructionRefinementCase,
    evm_state: SMTState,
    x86_state: SMTState,
):
    return [
        evm_state.evm_transient_storage.tload(BitVecVal(key, 256))
        != x86_state.evm_transient_storage.tload(BitVecVal(key, 256))
        for key in case.transient_storage_check_keys
    ]


def _evm_operator(case: InstructionRefinementCase) -> EvmOperator:
    return EvmOperator(
        kind=case.evm_kind,
        pc=case.evm_pc,
        immediate=case.evm_immediate,
        param=case.evm_param,
        is_static=case.evm_is_static,
    )


def _load_stack_slot(state: SMTState, arity: int, slot_index: int):
    offsets = _stack_limb_offsets(arity, slot_index)
    z0, z1, z2, z3 = (
        state.x86_memory.load_limb(BitVecVal(offset, 64), domain=MemoryDomain.STACK)
        for offset in offsets
    )
    return Concat(z3, z2, z1, z0)


def _operand_limb_offsets(arity: int) -> tuple[tuple[int, int, int, int], ...]:
    return tuple(
        _stack_limb_offsets(arity, slot_index)
        for slot_index in range(arity)
    )


def _stack_limb_offsets(arity: int, slot_index: int) -> tuple[int, int, int, int]:
    base_offset = -_UINT256_SLOT_BYTES * arity
    return tuple(
        base_offset + slot_index * _UINT256_SLOT_BYTES + limb_index * _LIMB_STRIDE_BYTES
        for limb_index in range(4)
    )
