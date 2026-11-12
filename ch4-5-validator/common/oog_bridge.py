"""块入口 OOG 谓词的「先证后桥接」（docs/循环处理增强方案.md §4.8）。

取消 no-OOG envelope 之后，cutpoint havoc 让 gas 变成符号量，每个块入口 TAG
守卫的 OOG 分支不再被 `simplify` 折死，全部存活 —— 归纳步的 (EVM 路径 × x86
路径) 矩阵因此膨胀。§4.8 给出的对策不是"少枚举几条"，而是**先证等价、再拿
等价结论当分区键**：

```text
1. 分别生成 oog_evm 与 oog_x86（各自侧的真实谓词）
2. 证明 R ∧ path_precondition ⇒ (oog_evm ↔ oog_x86)
3. 仅当该查询 UNSAT，才把等价结论作为桥接，用单个分区变量减少后续枚举
4. SAT / unknown / 超时 ⇒ 一律失败或降级
```

**严禁把它写成"两侧共享一个 OOG Boolean"。** 直接让两侧引用同一个 Boolean
就把待证命题假设掉了：x86 静态 gas 常量编错导致 `oog_evm = gas < 10` 而
`oog_x86 = gas < 11` 时，这类 codegen bug 会被完全掩盖 —— 而它恰恰是本机制
唯一能捕获的东西。所以这里的两个谓词来自**两个互不相干的信息源**：

- `oog_evm`：EVM IR 块的 `static_gas` 字段 + EVM 侧 gas 状态 `evm_gas.Gas`
- `oog_x86`：反汇编出的 TAG 序言 `cmp <reg>, IMM` 立即数 + x86 侧
  `callengine_gas_remaining`

纪律与 `common/div_bridge.py` 同构（先证实参恒等，再注入恒真等式），差别只在
桥接的是**控制流谓词**而不是数据等式：

- 桥接注入的 `oog_evm == oog_x86` 是在 `assumptions` 下**已证恒真**的等式，
  因此把它加进同一批 `assumptions` 是逻辑恒等变换（soundness 中性的求解提示）；
- 任何解析失败 / SAT / unknown / 超时都**不桥接**，调用方原路走 —— 这是纯
  性能优化，不允许成为新的正确性风险点。

分区剪枝的健全性论证（`cross_polarity_excluded`）：若已证
`base ⇒ (p_evm ↔ p_x86)`，且某条 EVM 路径满足 `base ∧ c_evm ⇒ p_evm`、某条
x86 路径满足 `base ∧ c_x86 ⇒ ¬p_x86`，则 `base ∧ c_evm ∧ c_x86` 蕴含
`p_evm ∧ ¬p_x86 ∧ (p_evm ↔ p_x86)`，恒假。于是这一对**被证明**不可共现，
无需再向求解器提问 —— 这是把一次求解替换成一次已证蕴含，不是跳过义务。
"""

import re
from dataclasses import dataclass, field
from typing import Callable, List, Optional, Sequence, Tuple

from z3 import (
    BitVecVal,
    Not,
    SolverFor,
    ULT,
    is_and,
    is_false,
    is_not,
    is_or,
    is_true,
    simplify,
    unsat,
)

# 桥接验证（证两侧谓词等价）的默认预算。单个 query 只含一条 64-bit ULT 的
# 异或再叠上 cutpoint 假设，通常 ≤1s；留余量避免满负载抖动（对齐 div_bridge）。
DEFAULT_BRIDGE_TIMEOUT_MS = 8_000

# AOT 编译器 的 callEngine 里 gas 余额字段偏移（`x86_64/aot_profile.py` 的
# `offsets["gas_remaining"]`）。这里保留一个默认值只是为了让本模块可以脱离
# profile 独立单测；生产调用点必须把活动 profile 的偏移传进来，否则合约级
# 重映射会让解析静默看错字段。
DEFAULT_GAS_FIELD_OFFSET = 0x70


# ---------------------------------------------------------------------------
# 各侧谓词的**独立**来源
# ---------------------------------------------------------------------------

def evm_oog_threshold(block) -> Optional[int]:
    """EVM 侧 OOG 阈值：带 TAG 守卫的块的 `static_gas`。

    必须与 `evm_ir/cfg_executor.py` 的 TAG 守卫逐字对齐 —— 那里的条件是
    `ULT(gas, BitVecVal(block.static_gas, 64))`，且只在「块含 TAG」且
    `static_gas` 非 0 时才建分支。两个条件缺一个，这里给出的谓词就会与执行器
    实际分叉的谓词不是一回事，桥接随即变成对**不存在的分支**做的断言。

    Returns:
        阈值；块没有 OOG 分叉时返回 None（不是 0 —— 0 会被误当成有效阈值）。
    """
    operations = getattr(block, "operations", None) or ()
    if not any(getattr(op, "kind", "").upper() == "TAG" for op in operations):
        return None
    static_gas = getattr(block, "static_gas", 0) or 0
    if static_gas <= 0:
        return None
    return int(static_gas)


# TAG 序言的 gas 检查三件套（`impl_amd64.go` 的 `makeStaticUseGas` +
# `jmpIfGasNotEnough`），实测形状（CErc20 0x107a2）：
#
#     mov rax, qword ptr [r13 + 0x70]
#     cmp rax, 0x32
#     jb  0x107d1                      ; → out_of_gas stub
#
# 解析**严格**要求这三条恰好是块的前三条指令且用同一个寄存器：codegen 换形状
# 时必须解析失败（fail-closed 退化成不桥接），而不是模糊匹配到别的 cmp/jb 上
# 去 —— 那会把一个与 gas 无关的分支冒充成 OOG 分区键。
_GAS_LOAD_RE = re.compile(
    r"^(?P<reg>[a-z0-9]+),\s*qword ptr \[r13 \+ (?P<offset>0x[0-9a-f]+)\]$"
)
_CMP_IMM_RE = re.compile(r"^(?P<reg>[a-z0-9]+),\s*(?P<imm>0x[0-9a-f]+|[0-9]+)$")
_TARGET_RE = re.compile(r"^(?P<target>0x[0-9a-f]+)$")


@dataclass(frozen=True)
class X86TagGasGuard:
    """从机器码解析出的 x86 TAG gas 守卫。"""

    threshold: int      # cmp 的立即数（该块的静态 gas）
    oog_target: int     # jb 的目标地址（OOG stub）
    gas_offset: int     # 读 gas 的 callEngine 字段偏移


def x86_tag_gas_guard(
    block,
    gas_offset: int = DEFAULT_GAS_FIELD_OFFSET,
    oog_stub_ok: Optional[Callable[[int], bool]] = None,
) -> Optional[X86TagGasGuard]:
    """解析 x86 块入口 TAG 序言的 gas 守卫（严格匹配，失败即 None）。

    Args:
        block: `x86_64.models.X86Block`。
        gas_offset: 活动 profile 的 `offsets["gas_remaining"]`。
        oog_stub_ok: 可选回调，用来确认 `jb` 目标**确实**是 out-of-gas 终止
            stub。不传就只按形状匹配 —— 形状对但跳去别处时，"这是 OOG 分支"
            就成了未经核实的断言。生产调用点应当传（`loop_induction` 用
            `x86_error_stub_status` 实现）。
    """
    # **必须滤掉对齐 nop**:codegen 会在序言中间插 nop 对齐(实测 CErc20 的
    # 0x1e65b / 0xbe03b 就是 `mov ; nop ; cmp ; jb`)。直接取 instructions[0:3]
    # 会拿到 `mov/nop/cmp` 而判定失败——方向上是 fail-closed(解析不出就不
    # 桥接),但白白丢掉覆盖率:实测 CErc20 的 9 个配对循环头里有 2 个因此
    # 拿不到谓词。`x86_64/loop_analysis.is_evm_tag_header` 与
    # `verification/loop_folding` 的 TAG 指纹都做了同样的过滤。
    instructions = [
        insn
        for insn in (getattr(block, "instructions", None) or ())
        if insn.mnemonic != "nop"
    ]
    if len(instructions) < 3:
        return None
    load, cmp_insn, jcc = instructions[0], instructions[1], instructions[2]

    if load.mnemonic != "mov" or cmp_insn.mnemonic != "cmp" or jcc.mnemonic != "jb":
        return None

    load_match = _GAS_LOAD_RE.match(load.op_str.strip())
    if load_match is None or int(load_match.group("offset"), 16) != gas_offset:
        return None

    cmp_match = _CMP_IMM_RE.match(cmp_insn.op_str.strip())
    if cmp_match is None or cmp_match.group("reg") != load_match.group("reg"):
        # 比较的不是刚读出来的 gas ⇒ 这不是 gas 守卫。
        return None

    target_match = _TARGET_RE.match(jcc.op_str.strip())
    if target_match is None:
        return None
    target = int(target_match.group("target"), 16)
    if oog_stub_ok is not None and not oog_stub_ok(target):
        return None

    return X86TagGasGuard(
        threshold=int(cmp_match.group("imm"), 0),
        oog_target=target,
        gas_offset=gas_offset,
    )


def evm_oog_predicate(block, evm_state):
    """EVM 侧真实 OOG 谓词（None 表示该块没有 OOG 分叉）。"""
    threshold = evm_oog_threshold(block)
    if threshold is None:
        return None
    # 与 `evm_ir/cfg_executor.py` 一致地 simplify：执行器把 simplify 后的形式
    # 塞进路径条件，语法极性识别（`conjunct_polarity`）要能对上同一个 AST。
    return simplify(ULT(evm_state.evm_gas.Gas, BitVecVal(threshold, 64)))


def x86_oog_predicate(
    block,
    x86_state,
    gas_offset: int = DEFAULT_GAS_FIELD_OFFSET,
    oog_stub_ok: Optional[Callable[[int], bool]] = None,
):
    """x86 侧真实 OOG 谓词（None 表示解析不出 gas 守卫 ⇒ 不桥接）。

    读的是 x86 侧自己的 gas（`callengine_gas_remaining`，即 `mov rax,
    [r13+0x70]` 的 side-channel 快路径结果）与**机器码里的**立即数。绝不能
    图省事复用 EVM 的 `static_gas` —— 那正是"共享判定"的变体，会把常量编错
    的 codegen bug 一并掩盖。
    """
    guard = x86_tag_gas_guard(block, gas_offset=gas_offset, oog_stub_ok=oog_stub_ok)
    if guard is None:
        return None
    return simplify(
        ULT(x86_state.callengine_gas_remaining, BitVecVal(guard.threshold, 64))
    )


# ---------------------------------------------------------------------------
# 桥接：先证等价
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class OogPartition:
    """一对**已证等价**的 OOG 谓词，充当路径分区键（§4.8 的"单个分区变量"）。

    两侧谓词各自保留，**不合并成一个 Boolean**：极性判定必须在各自侧用各自的
    谓词做，合并即假设待证命题。
    """

    name: str
    evm_predicate: object
    x86_predicate: object
    evm_threshold: int
    x86_threshold: int
    #: 已证恒真的桥接等式，可安全并入同一批 assumptions
    equality: object


@dataclass
class OogBridgeReport:
    """桥接尝试的结果（fail-closed：`partition is None` 即不桥接）。"""

    partition: Optional[OogPartition] = None
    status: str = "unavailable"  # 'bridged' | 'refuted' | 'unknown' | 'unavailable'
    reason: str = ""
    queries: List[Tuple[str, str]] = field(default_factory=list)

    @property
    def bridged(self) -> bool:
        return self.partition is not None


def verified_oog_bridge(
    evm_predicate,
    x86_predicate,
    assumptions: Sequence = (),
    name: str = "oog",
    evm_threshold: int = -1,
    x86_threshold: int = -1,
    ctx=None,
    verify_timeout_ms: int = DEFAULT_BRIDGE_TIMEOUT_MS,
) -> OogBridgeReport:
    """证明 `assumptions ⇒ (oog_evm ↔ oog_x86)`，成立才给出分区（§4.8 步骤 2–4）。

    反例查询是 `assumptions ∧ (oog_evm ≠ oog_x86)`：

    - **unsat** ⇒ 两侧谓词在该前提下必然同真同假，桥接成立；
    - **sat**   ⇒ 存在一个 gas 让两侧判定分叉（静态 gas 常量编错就长这样），
      拒绝桥接并如实标 `refuted`；
    - **unknown / 超时** ⇒ 同样拒绝（fail-closed）。

    注意 `refuted` **不是**"发现反例"结论：调用方拿到它只应放弃这项优化并
    照常走完整枚举，真正的等价义务由 ②(a)/②(d) 的主证明负责报告。
    """
    if evm_predicate is None or x86_predicate is None:
        return OogBridgeReport(
            status="unavailable",
            reason=(
                "no OOG predicate on "
                + ("EVM" if evm_predicate is None else "x86")
                + " side (no TAG gas guard, or the x86 prologue did not match "
                "the expected `mov/cmp/jb` shape)"
            ),
        )

    solver = SolverFor("QF_AUFBV", ctx=ctx) if ctx is not None else SolverFor("QF_AUFBV")
    solver.set("timeout", verify_timeout_ms)
    for assumption in assumptions:
        solver.add(assumption)
    solver.add(evm_predicate != x86_predicate)
    verdict = solver.check()
    queries = [(f"§4.8 oog-bridge {name}", str(verdict))]

    if verdict != unsat:
        return OogBridgeReport(
            status="refuted" if str(verdict) == "sat" else "unknown",
            reason=(
                f"OOG predicate equivalence not provable ({verdict}): "
                f"evm threshold={evm_threshold} vs x86 threshold={x86_threshold}"
                " — no bridge, falling back to the full path matrix"
            ),
            queries=queries,
        )

    return OogBridgeReport(
        partition=OogPartition(
            name=name,
            evm_predicate=evm_predicate,
            x86_predicate=x86_predicate,
            evm_threshold=evm_threshold,
            x86_threshold=x86_threshold,
            equality=(evm_predicate == x86_predicate),
        ),
        status="bridged",
        reason=(
            f"proved oog_evm(threshold={evm_threshold}) <-> "
            f"oog_x86(threshold={x86_threshold}) under the cutpoint assumptions"
        ),
        queries=queries,
    )


# ---------------------------------------------------------------------------
# 极性判定与剪枝
# ---------------------------------------------------------------------------

def conjunct_polarity(condition, predicate) -> Optional[bool]:
    """纯语法地判定 `condition` 是否蕴含 `predicate` 或其否定。

    只认**AST 恒等**的合取字面量，因此结论是语法蕴含（`A ∧ p ⇒ p`），不需要
    任何求解器、也不可能判错方向。找不到就返回 None，交给调用方用求解器兜底
    或干脆放弃剪枝 —— 绝不猜。

    走的是合取式的树：`And(...)` 展开；`Not(Or(...))` 按 De Morgan 展开成各
    析取项的否定（执行器 simplify 后常见这种形状）。析取项本身不展开：
    `Or(p, q)` 不蕴含 `p`。
    """
    if condition is None or predicate is None:
        return None
    negated = simplify(Not(predicate))
    stack = [condition]
    seen = set()
    while stack:
        node = stack.pop()
        try:
            node_id = node.get_id()
        except AttributeError:
            continue
        if node_id in seen:
            continue
        seen.add(node_id)

        if node.eq(predicate):
            return True
        if node.eq(negated):
            return False
        # 也接受未 simplify 的 `Not(predicate)` 写法
        if is_not(node) and node.arg(0).eq(predicate):
            return False
        if is_not(node) and node.arg(0).eq(negated):
            return True

        if is_and(node):
            stack.extend(node.children())
        elif is_not(node) and is_or(node.arg(0)):
            stack.extend(Not(child) for child in node.arg(0).children())
    return None


def cross_polarity_excluded(
    evm_polarity: Optional[bool], x86_polarity: Optional[bool]
) -> bool:
    """两侧极性都已判定且相反 ⇒ 该 (evm, x86) 组合在桥接下**可证**不可共现。

    未判定（None）一律返回 False：极性不明时不剪枝，保守方向。
    """
    return (
        evm_polarity is not None
        and x86_polarity is not None
        and evm_polarity != x86_polarity
    )


def constant_polarity(condition) -> Optional[bool]:
    """`BoolVal(True)/(False)` 这种常量条件的极性（辅助，供测试与调试用）。"""
    if condition is None:
        return None
    folded = simplify(condition)
    if is_true(folded):
        return True
    if is_false(folded):
        return False
    return None


__all__ = [
    "DEFAULT_BRIDGE_TIMEOUT_MS",
    "DEFAULT_GAS_FIELD_OFFSET",
    "OogBridgeReport",
    "OogPartition",
    "X86TagGasGuard",
    "conjunct_polarity",
    "constant_polarity",
    "cross_polarity_excluded",
    "evm_oog_predicate",
    "evm_oog_threshold",
    "verified_oog_bridge",
    "x86_oog_predicate",
    "x86_tag_gas_guard",
]
