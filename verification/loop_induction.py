"""P2：Tier 1 锁步关系式归纳引擎（docs/循环处理增强方案.md §4）。

对一对已配对的 (EVM natural loop, x86 natural loop)，在循环头 cutpoint 上
执行归纳步（§4.2 ②）：

- **havoc 构造**：cutpoint 状态用 ``SMTState.create_initial_state(num_inputs=k)``
  构造——两侧共享同一组新鲜栈符号（EVM 栈与 x86 STACK 窗口 by construction
  耦合）、共享 storage/transient/calldata Array、路径条件为空。这正是 §4.3
  的 havoc 纪律：除 R 钉住的状态外一切新鲜。
- **两侧各执行一轮循环体**（有界段执行，cutpoint 截断），按出口分类后：
  (a) 分支决策逐对一致（只覆盖正常回边/出口边）
  (b) 都走回边 ⇒ 回到循环头时 R 保持
  (c) 都走出口 ⇒ 出口处 R 保持
  (d) 体内终止路径 ⇒ 终止可观测量等价（含 status code；OOG / 栈下溢 /
      栈超限作为 terminal outcome 归入此项，**不**按地址与出口边配对）

关键语义（§6）：**归纳步 SAT ≠ 找到 bug**。R 太弱时归纳步给伪反例，本引擎
的失败输出只有 ``inconclusive``（→ 管线降级），绝不把 SAT 当反例报告。

范围（与文档一致）：
- R 的分量由 :class:`verification.cutpoint_relation.CutpointRelationSchema`
  单点定义，havoc 与证明义务强制对称。**不要在本模块手工拼 R 的合取**。
- gas 是 R 的内部控制流关系（三档 GasCheck 都要）；terminal gas 比较只在
  `FIXED_BUDGET`/`FULL`。no-OOG/no-stack-limit envelope 已取消。
- logs 仍不在可观测面（`common/path_observation.py` 的 OBSERVATION_KEYS 无该键）。
- 栈深按深度类逐一实例化（k 由调用方给出），byte offset 取 k*0x20。
- **§4.8 OOG 谓词桥接**（`enable_oog_bridge`，默认关闭）：envelope 取消后
  cutpoint 的 gas 是符号量，块入口 OOG 分支全部存活、路径矩阵膨胀。开启后先
  在 `common/oog_bridge.py` 里**分别**生成两侧谓词并证明其等价，只有 UNSAT
  才拿它当分区键剪掉极性相反的路径对。这是纯性能优化：关掉时逐字回到原行为，
  桥接不成立（SAT/unknown/解析失败）时也一样回到全量枚举。
"""

import time
from dataclasses import dataclass, field
from typing import Callable, Dict, List, Optional, Sequence, Set, Tuple

from z3 import (
    And,
    Array,
    BitVec,
    BitVecSort,
    BitVecVal,
    BoolVal,
    Concat,
    Lambda,
    Not,
    Select,
    SolverFor,
    is_and,
    sat,
    simplify,
    unsat,
)


def _make_solver(timeout_ms: int):
    """归纳查询统一用 QF_AUFBV（对齐 equivalence_context 与 div_bridge 先例：
    复杂 Store/Select 公式在默认 Solver 下容易 unknown）。"""
    solver = SolverFor("QF_AUFBV")
    solver.set("timeout", timeout_ms)
    return solver


def _conjuncts(expr) -> List:
    return list(expr.children()) if is_and(expr) else [expr]


# 后缀切片规模序列：路径条件的"决策项"位于合取尾部（执行器按块序累积
# 约束），小切片通常已含矛盾/所需前提。
_SLICE_SIZES = (1, 4, 16)


def _suffix_slices(evm_terms: List, x86_terms: List):
    """产出 (evm 子集, x86 子集, 标签) 序列，从小到大，最后是全量。

    健全性：约束子集是弱化——子集 unsat ⇒ 全集 unsat（失配证明）；
    弱前提证得目标 ⇒ 强前提下仍成立（R 证明）。因此任何切片上的
    unsat 结论都可直接采信；只有"全部切片失败"才落到全量查询。
    """
    for k in _SLICE_SIZES:
        if k >= len(evm_terms) and k >= len(x86_terms):
            break
        yield evm_terms[-k:], x86_terms[-k:], f"slice{k}"
    yield evm_terms, x86_terms, "full"


# --- 路径已判定的 ITE 极性（提速，soundness 中性）-------------------------
#
# EVM 侧 `state/evm_gas_state.memory_expansion_fee` 不分叉，它把"是否扩容"编码成
# `If(expands, …, …)`，于是 gas / MSize / lastGasCost 三处都挂着同一个 ITE。具体
# 一条路径上 `expands` 是定死的，但那件事**只能由几十条合取推出**（x86 侧才有对应
# 的真分支），QF_BV 前端 eager bit-blast 时用不上——两侧内存费因此没法相消，整条
# gas 义务从 0.3s 变成 120s unknown（CErc20 验收用例实测）。
#
# 对策与 `common/div_bridge.py` 同构：**先证后注入**。极性在完整前提下证出来才用，
# 判不出就不加。它是前提的逻辑后承，加进查询是恒等变换而不是新假设。
_ITE_POLARITY_LIMIT = 4
_ITE_POLARITY_TIMEOUT_MS = 5000
# 只对**被多个 ITE 结点共用**的条件花查询：单处出现的 ITE 解开也没有可相消的对象。
_ITE_POLARITY_MIN_SITES = 2


def _collect_shared_bv_ite_conditions(expressions, limit: int) -> List:
    """收集被多个 BV-ITE 结点共用的条件，按共用度降序（同频按发现序）。

    只看 **BV 分支**的 ITE：Bool 分支的 ITE 本来就在布尔层、SAT 求解器自己会
    分裂；Array/Lambda 分支给不出可相消的算术项，判它的极性纯属浪费预算。

    **必须用显式栈**：这里的表达式上千层嵌套，递归版会在 Python 默认递归上限处
    抛 RecursionError（同 `common.div_bridge.collect_div_subexprs` 的理由）。
    """
    from z3 import Z3_OP_ITE, is_app_of, is_bv, is_false, is_true

    # condition id -> [共用它的 ITE 结点数, 条件, 发现序]
    tally: Dict[int, List] = {}
    discovered = 0
    seen: Set[int] = set()
    stack = list(expressions)
    while stack:
        node = stack.pop()
        node_id = node.get_id()
        if node_id in seen:
            continue
        seen.add(node_id)
        if is_app_of(node, Z3_OP_ITE) and is_bv(node.arg(1)):
            condition = node.arg(0)
            if not (is_true(condition) or is_false(condition)):
                entry = tally.get(condition.get_id())
                if entry is None:
                    tally[condition.get_id()] = [1, condition, discovered]
                    discovered += 1
                else:
                    entry[0] += 1
        stack.extend(node.arg(index) for index in range(node.num_args()))

    ranked = sorted(
        (entry for entry in tally.values()
         if entry[0] >= _ITE_POLARITY_MIN_SITES),
        key=lambda entry: (-entry[0], entry[2]),
    )
    return [entry[1] for entry in ranked[:limit]]

from common.oog_bridge import (
    DEFAULT_BRIDGE_TIMEOUT_MS,
    OogPartition,
    conjunct_polarity,
    cross_polarity_excluded,
    evm_oog_predicate,
    evm_oog_threshold,
    verified_oog_bridge,
    x86_oog_predicate,
    x86_tag_gas_guard,
)
from common.store_forwarding import forward_selects, unshift_store_chain
from evm_ir.cfg_executor import SymbolicExecutor
from evm_ir.models import EVMBlock
from state.smt_state import SMTState
from state.x86_state import MemoryDomain
from x86_64.cfg_executor import X86SymbolicExecutor
from x86_64.models import Register, X86Block

LIMBS_PER_UINT256 = 4
LIMB_SIZE_BYTES = 8


# ---------------------------------------------------------------------------
# 结果类型
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class ExternalPremise:
    """终止论证依赖、但**不在本处证明**的一条前提。

    `discharged` 必须由真正兑现它的那一层来置位（段覆盖证书、结构守卫、
    主证明图……）。默认 False 是关键设计：**未兑现的前提不能算数**。把这些
    前提写成一串说明性字符串、再让 `proved` 忽略它们，等于把六项前提中的
    四项悄悄降格成注释——终止结论会在前提未落实时照样签发。
    """

    name: str
    detail: str
    responsible: str
    discharged: bool = False


@dataclass(frozen=True)
class ExternalPremiseDischarges:
    """由**调用方**兑现的两条终止外部前提（§4.2 ②(e)）。

    归纳步自己看不到这两条的证据：一条要的是全局结构守卫的结论（段内每条 x86
    回边都已配对或已有 Tier-2 引理），另一条要的是外层证明图的结论（骨架里每个
    SCC 要么被切在 cutpoint、要么自带终止证书）。两者都在本引擎之外。

    **默认全 False 是纪律，不是保守默认**：置位的唯一合法依据是调用方确实跑过
    那些检查并拿到了肯定结论。把它们默认成 True（或干脆不检查）等于把两条前提
    降格成注释——终止结论会在前提未落实时照样签发。

    注意：这些标志会被烘进缓存的 `TerminationEvidence`，因此必须进定理缓存键，
    否则"以 True 证过一次、之后以 False 请求"会取回那张宽松的定理（假绿）。
    """

    no_unidentified_inner_loop: bool = False
    all_sccs_cut_or_certified: bool = False

    def fingerprint(self) -> str:
        return (
            f"inner_loop={int(self.no_unidentified_inner_loop)},"
            f"sccs={int(self.all_sccs_cut_or_certified)}"
        )


@dataclass
class TerminationEvidence:
    """②(e) 的终止证据（§4.2）。

    单轮 latch 上证出 gas 严格递减**不足以**推出有限退出——完整结论还依赖
    段覆盖完整、无位向量回绕、段内无未识别循环、SCC 已切断、无无限
    stuttering、SAT/unknown/coverage 缺失 fail-closed 这六项前提。这里把
    "已在本处证的"与"依赖别处兑现的"分开记录，且后者带 `discharged` 标志，
    由证书的 `proved` 强制检查。
    """

    # 每条可行 latch arm 上 `gas_out <u gas_in` 的查询结果
    latch_arms_checked: int = 0
    latch_arms_decreasing: int = 0
    # 无位向量回绕的依据（OOG 分叉保证到达减法时 gas 已足够，Gas 设计 §5）
    no_wraparound_basis: Optional[str] = None
    # 依赖但由别处兑现的前提
    external_premises: List[ExternalPremise] = field(default_factory=list)

    @property
    def all_arms_decrease(self) -> bool:
        return (
            self.latch_arms_checked > 0
            and self.latch_arms_decreasing == self.latch_arms_checked
        )

    @property
    def pending_premises(self) -> Tuple[str, ...]:
        """尚未被兑现的外部前提名。非空 ⇒ 终止结论**不成立**。"""
        return tuple(
            premise.name
            for premise in self.external_premises
            if not premise.discharged
        )


@dataclass
class DepthClassEvidence:
    """深度类枚举完备性的两条义务（§4.1）。

    仅"遇到未登记的新 class 就 fail-closed"**不足以**证明枚举完整——那挡不住
    "永远遇不到、但确实存在"的 class。完备性必须拆成两条可证义务：

    (i) **首次到达覆盖**：任何到达该循环头的路径，其深度类都在已登记集合内。
        由 Base 段的 coverage 证书保证（枚举了全部到达路径），这里记录依据。
    (ii) **转移封闭**：每个已登记 class 的 latch 与再入只转移到已登记集合内。
        由归纳步逐条 latch 检查 SP 是否仍落在集合内。

    两条都成立时，深度类集合才是该循环头的归纳不变式。
    """

    registered_classes: Tuple[int, ...] = ()
    # (i)
    arrival_coverage_basis: Optional[str] = None
    # (ii)
    latch_transitions_checked: int = 0
    latch_transitions_closed: int = 0
    escaping_depths: Tuple[int, ...] = ()

    @property
    def transition_closed(self) -> bool:
        return (
            self.latch_transitions_checked > 0
            and self.latch_transitions_closed == self.latch_transitions_checked
            and not self.escaping_depths
        )

    @property
    def complete(self) -> bool:
        return self.arrival_coverage_basis is not None and self.transition_closed


@dataclass
class OogBridgeStats:
    """§4.8 OOG 谓词桥接这一次的完整台账（成立与否、剪掉多少对）。

    单独成结构而不是塞进 `reasons` 字符串：桥接是**性能优化**，它的收益必须
    可量化、可回归；而它的失败（SAT/unknown/解析不出）必须能一眼看出走的是
    降级路径而**不是**"证明成功"。两件事都不该靠读日志文本判断。

    `status` 的取值与 `common.oog_bridge.OogBridgeReport.status` 同义，另加
    `'disabled'`（调用方没开这项优化）。**`'refuted'` 不是反例报告**：它只
    表示两侧谓词在 cutpoint 前提下可能分叉，因而不能拿来当分区键；真正的
    等价义务照常由 ②(a)/②(d) 的主证明承担。
    """

    site: str = ""
    status: str = "disabled"
    reason: str = ""
    evm_threshold: int = -1
    x86_threshold: int = -1
    # 分区极性判定的开销与命中情况
    polarity_syntactic: int = 0
    polarity_solved: int = 0
    polarity_unknown: int = 0
    polarity_queries: int = 0
    # 收益：矩阵总对数与被已证蕴含剪掉的对数
    pairs_total: int = 0
    pairs_pruned: int = 0

    @property
    def bridged(self) -> bool:
        return self.status == "bridged"


@dataclass
class LoopInductionResult:
    """归纳/段查询结果。status ∈ {'proved', 'inconclusive'}——没有 'refuted'。"""

    status: str
    reasons: List[str] = field(default_factory=list)
    queries: List[Tuple[str, str]] = field(default_factory=list)
    # ① Base 查询产出：循环头到达时的绝对栈深类（供 ②③ 按类实例化）
    depth_classes: List[int] = field(default_factory=list)
    # ②(e) 终止证据；None 表示本次查询未涉及终止义务
    termination: Optional[TerminationEvidence] = None
    # 深度类完备性证据；None 表示本次查询未涉及
    depth_evidence: Optional[DepthClassEvidence] = None
    # 本次查询**实际核对过**的 cutpoint 结构前提覆盖点（§4.5.6）。
    # 记录而不是靠调用方推断：五处覆盖点的完整性由证书汇总检查，漏掉一处必须
    # 表现为"这处没记录"，而不是"大概跑过了"。
    structural_premise_sites: Tuple[str, ...] = ()
    # §4.8 OOG 桥接台账；None 表示这条查询根本不涉及路径矩阵（如结构预检直接
    # 拒绝）。默认关闭时 status 为 'disabled'。
    oog_bridge: Optional[OogBridgeStats] = None

    @property
    def proved(self) -> bool:
        return self.status == "proved"

    @classmethod
    def inconclusive(cls, reason: str, queries=None) -> "LoopInductionResult":
        return cls(status="inconclusive", reasons=[reason], queries=queries or [])


@dataclass
class SegmentPath:
    """段执行的一条出口路径。"""

    kind: str  # 'latch' | 'exit' | 'terminal'
    location: Optional[int]  # latch/exit：到达的 pc/addr；terminal：None
    condition: object  # 路径条件（BoolRef）
    state: SMTState
    # x86：执行器在这条路径上最后一次可达性检查的模型（可能已不满足
    # condition，使用方须先 eval 核对）；只用于提议，不参与任何证明。
    witness: object = field(default=None, compare=False, repr=False)


# ---------------------------------------------------------------------------
# 段执行
# ---------------------------------------------------------------------------

def run_evm_segment(
    blocks: Sequence[EVMBlock],
    cut_state: SMTState,
    entry_pc: int,
    stop_pcs: Set[int],
    max_depth: int = 200,
) -> Tuple[List[SegmentPath], List[str]]:
    """从 cutpoint 执行一轮 EVM 段，返回 (路径列表, coverage 缺陷)。"""
    executor = SymbolicExecutor(
        blocks=list(blocks),
        max_depth=max_depth,
        use_reachability_check=False,
        stop_pcs=stop_pcs,
    )
    final_states = executor.execute(cut_state, entry_pc=entry_pc)

    defects: List[str] = []
    certificate = executor.path_coverage_certificate()
    if not certificate.complete:
        defects.append(f"EVM segment coverage incomplete: {certificate.reason}")

    paths: List[SegmentPath] = []
    for gstate in executor.cut_states:
        pc = gstate.node.pc
        kind = "latch" if pc == entry_pc else "exit"
        paths.append(
            SegmentPath(
                kind=kind,
                location=pc,
                condition=gstate.get_constraints().as_bool(),
                state=gstate.mstate,
            )
        )
    for gstate in final_states:
        paths.append(
            SegmentPath(
                kind="terminal",
                location=gstate.node.pc if gstate.node else None,
                condition=gstate.get_constraints().as_bool(),
                state=gstate.mstate,
            )
        )
    return paths, defects


# x86 块入口 TAG 序言的三类错误终态（§4.2 ②(d)）。
#
# 这些**不是循环出口**：它们既不回循环头也不走正常出口，因此不按地址与 EVM
# 出口边配对，而是作为 terminal outcome 进 ②(d) 的可观测量证明（status code
# 是其中最核心的一项）。
#
# 上一版把它们整个**排除**掉，理由是 EVM 侧当时没有 gas/栈错误语义、配对必然
# 伪 SAT——那就是 no-OOG/no-stack-limit envelope。develop 现在两侧都有：
# `evm_ir/cfg_executor.py` 的 TAG 守卫已镜像三分支（OUT_OF_GAS →
# STACK_UNDERFLOW → STACK_REACHED_LIMIT），错误码见 `evm_ir/status_code.py`。
# 因此排除的理由已消失，envelope 取消，这些路径改为**配对证明**。
_TERMINAL_ERROR_STATUSES = frozenset({
    "out_of_gas",
    "gas_uint_overflow",
    "stack_underflow",
    "stack_reached_limit",
})

_STATUS_WRITE_MARKER = "[r13 + 0xe0]"


def _extract_imm_write(block: X86Block, marker: str) -> Optional[int]:
    """从块中提取 ``mov <marker>, IMM`` 的立即数（bridge 元数据解析）。"""
    for insn in block.instructions:
        if insn.mnemonic == "mov" and marker in insn.op_str:
            try:
                return int(insn.op_str.rsplit(",", 1)[1].strip(), 0)
            except (IndexError, ValueError):
                return None
    return None


def x86_error_stub_status(block: X86Block) -> Optional[int]:
    """静态识别错误终止 stub：写 [r13+0xe0] 状态码并以 ret 结束的块。

    Returns:
        状态码；不是错误 stub 时返回 None。
    """
    if not block.instructions or block.instructions[-1].mnemonic != "ret":
        return None
    # 错误 stub 无 lea rip 返回地址（有则是 go-bridge 站点）
    if any("rip" in insn.op_str for insn in block.instructions if insn.mnemonic == "lea"):
        return None
    for insn in block.instructions:
        if insn.mnemonic == "mov" and _STATUS_WRITE_MARKER in insn.op_str:
            try:
                return int(insn.op_str.rsplit(",", 1)[1].strip(), 0)
            except (IndexError, ValueError):
                return None
    return None


def run_x86_segment(
    blocks: Sequence[X86Block],
    cut_state: SMTState,
    entry_addr: int,
    stop_addrs: Set[int],
    max_depth: int = 400,
    aot_profile=None,
    use_reachability_check: bool = False,
    summary_config=None,
    summary_runtime=None,
    deadline=None,
    call_site_mapping=None,
    # Idle-machine reachability checks on CErc20: p99 35ms, max 47ms (2026-09-26);
    # 50ms left no margin, so load turned checks into unknown -> less pruning ->
    # depth-pruned segments. Unknown still means reachable (sound either way).
    # Symbolic-fmp/msize blocks (memory-expansion gas words*words) need up to
    # ~1s even with the mul-abstracted refutation (2026-09-27, Safe 6898:
    # 250ms kept 81 paths/107s, 1000ms 61 paths/68s; 3000ms no further gain).
    # Witness reuse means only non-model branches pay this budget.
    reachability_timeout_ms: int = 1000,
) -> Tuple[List[SegmentPath], List[str], List[str]]:
    """从 cutpoint 执行一轮 x86 段。

    Returns:
        (路径列表, coverage 缺陷, 段说明)。TAG 的 gas/栈错误终止路径**照常
        进入路径列表**并由 ②(d) 与 EVM 侧对应终态配对证明；段说明只记录
        它们的性质供报告标注。旧版在此处按 no-OOG/no-stack-limit envelope
        把这些路径整个丢弃，envelope 取消后该行为已移除。
    """
    if summary_runtime is not None and summary_config is not None:
        raise ValueError("supply summary_runtime or summary_config, not both")
    if summary_config is not None:
        # 段执行覆盖真实入口前缀/出口延续时，selector/calldata 的逐字节
        # 读代码需要 CALLDATALOAD summary 折叠（与整程序验证同一配置），
        # 否则命中 PointerTag 无法路由的字节访存直接 MemoryDomainError。
        from x86_64.summaries import build_x86_summary_runtime
        summary_runtime = build_x86_summary_runtime(
            list(blocks), summary_config=summary_config
        )
    executor = X86SymbolicExecutor(
        blocks=list(blocks),
        max_depth=max_depth,
        use_reachability_check=use_reachability_check,
        enable_go_bridge=True,
        enable_merge=False,
        stop_addrs=stop_addrs,
        aot_profile=aot_profile,
        summary_runtime=summary_runtime,
        deadline=deadline,
        call_site_mapping=call_site_mapping,
        reachability_timeout_ms=reachability_timeout_ms,
    )
    final_states = executor.execute(cut_state, entry_addr=entry_addr)

    defects: List[str] = []
    certificate = executor.path_coverage_certificate()
    if not certificate.complete:
        defects.append(f"x86 segment coverage incomplete: {certificate.reason}")

    error_codes = {
        code
        for name, code in executor.aot_profile.status_codes.items()
        if name in _TERMINAL_ERROR_STATUSES
    }

    paths: List[SegmentPath] = []
    notes: List[str] = []
    for gstate in executor.cut_states:
        addr = gstate.node.address
        kind = "latch" if addr == entry_addr else "exit"
        paths.append(
            SegmentPath(
                kind=kind,
                location=addr,
                condition=gstate.get_constraints().as_bool(),
                state=gstate.mstate,
                witness=gstate.get_constraints()._witness,
            )
        )
    for gstate in final_states:
        block = gstate.node.block if gstate.node else None
        status = executor._extract_status_code(block) if block is not None else None
        if status is not None and status in error_codes:
            # 不再排除：EVM 侧已有对应的 TAG 错误终态，交给 ②(d) 配对证明。
            # 只记录一条说明，供报告标注这条路径的性质。
            notes.append(
                f"x86 terminal error path at 0x{gstate.node.address:x} "
                f"(status={status}) proved as a paired terminal outcome"
            )
        paths.append(
            SegmentPath(
                kind="terminal",
                location=gstate.node.address if gstate.node else None,
                condition=gstate.get_constraints().as_bool(),
                state=gstate.mstate,
                witness=gstate.get_constraints()._witness,
            )
        )
    return paths, defects, notes


# ---------------------------------------------------------------------------
# R：耦合关系读取器
#
# 读取器与 schema 都在 verification/cutpoint_relation.py，这里只做再导出以保持
# 既有调用点（含测试）可用。**新代码请直接用 CutpointRelationSchema**：分散地
# 拼 R 的合取正是三处假绿缺口（host-gas 序号 / lastGasCost / return data）的
# 成因——havoc 改了、证明目标没改，而没有任何机制会发现。
# ---------------------------------------------------------------------------

from verification.cutpoint_relation import (  # noqa: E402  (置于 helper 定义前)
    CUTPOINT_STRUCTURAL_SITES,
    CutpointRelationSchema,
    RelationContext,
    StructuralPremiseReport,
    memory_coupling_condition,
    read_x86_stack_slot,
    x86_memory_as_evm_view,
)


_DEFAULT_RELATION_SCHEMA = CutpointRelationSchema()


# 三条查询各自**负责**的 cutpoint 结构前提覆盖点（§4.5.6）。剩下的第五处
# `certificate_application` 由 `verification.loop_certificate_prover` 负责。
#
# 记的是"负责哪几处"而不是"这次实际跑了哪几处"：某类路径为空时（例如出口段
# 全是终止路径、没有再入）义务本就是空真的，按实际调用记会把它误报成缺口，
# 反过来逼着调用方放宽完备性检查——那才是真缺口。义务是否真的接进了目标列表，
# 由测试用 tracing schema 直接盯 `structural_premises` 的调用来守。
BASE_STRUCTURAL_SITES: Tuple[str, ...] = ("base_arrival",)
STEP_STRUCTURAL_SITES: Tuple[str, ...] = ("latch_reentry", "exit_edge")
EXIT_STRUCTURAL_SITES: Tuple[str, ...] = ("exit_segment_cutpoint",)
# 由证书编排层（`prove_loop_certificate`）负责的那一处。
APPLICATION_STRUCTURAL_SITE: str = "certificate_application"

# 四方必须**恰好**分掉五处覆盖点：新增一处却没人认领时，证书的完备性检查会
# 因为永远凑不齐而全线降级（还算安全）；反过来若有人重复认领同一处，完备性
# 就会被一处冒充两处地凑齐——那是假绿。import 期直接钉死。
assert (
    tuple(
        sorted(
            (
                *BASE_STRUCTURAL_SITES,
                *STEP_STRUCTURAL_SITES,
                *EXIT_STRUCTURAL_SITES,
                APPLICATION_STRUCTURAL_SITE,
            )
        )
    )
    == tuple(sorted(CUTPOINT_STRUCTURAL_SITES))
), "cutpoint 结构前提覆盖点没有被三条查询 + 证书编排恰好分掉"


def coupling_conditions(
    evm_state: SMTState,
    x86_state: SMTState,
    stack_depth: int,
    cut_mem0=None,
    schema: Optional[CutpointRelationSchema] = None,
    context: Optional[RelationContext] = None,
) -> List:
    """R 的全部合取（§4.1），委托给 :class:`CutpointRelationSchema`。

    分量清单由 schema 单点定义并与 havoc 强制对称，故这里**不再**手工列举
    —— 手工列举正是 host-gas 序号 / lastGasCost / return data 三处漏掉的成因。

    传 `context`（归纳步，对 havoc 状态求义务）会触发分量对称性断言；Base 与
    certificate application 对**实际到达状态**重证 R，改传 `cut_mem0` 即可。
    """
    schema = schema or _DEFAULT_RELATION_SCHEMA
    if context is not None:
        return schema.goals(
            evm_state, x86_state, stack_depth, context=context
        )
    return schema.goals(
        evm_state, x86_state, stack_depth, memory_snapshot=cut_mem0
    )


def terminal_observable_conditions(
    evm_state: SMTState, x86_state: SMTState, cut_mem0=None,
    compare_gas: bool = False,
) -> List:
    """②(d) 终止可观测量等价。

    覆盖 return metadata、返回内容、storage/transient、**status code**，以及
    `compare_gas` 为真（`GasCheck.FIXED_BUDGET`/`FULL`）时的 **gas**。

    返回内容用整 memory 的 R15 平移相等表达（覆盖 [offset, offset+length)
    的返回区间，强于逐字节区间比较）：两侧从耦合的 mem₀ 出发执行对齐的
    EVM 内存操作，整体相等是自然的终止 R；过强的方向是安全的——只会
    多降级，不会假绿。offset/length 相等蕴含 has_return_data（两侧都由
    length != 0 派生）一致。

    **status 在这里而不在 cutpoint R 里**（§4.1）：cutpoint 处两侧都还在
    running，把 status 写进 R 需要先证"循环头处两侧均未终止"这条不变式，
    否则只是过强约束。终止路径上则相反——status 正是最核心的可观测量，
    OOG / 栈下溢 / 栈超限这些错误终态全靠它区分。

    **gas 的双重身份**（§4.1）：cutpoint 上的 gas 相等是控制流闭合所需的
    内部关系（三档都要，在 R 里）；这里的 gas 比较是 terminal observable，
    只在比较 gas 的两档做。混同两者会得到"OFF 档也在比较 gas"的错误结论。
    """
    conditions = [
        evm_state.return_offset == x86_state.return_offset,
        evm_state.return_length == x86_state.return_length,
        memory_coupling_condition(evm_state, x86_state, cut_mem0),
        evm_state.evm_storage.Storage == x86_state.evm_storage.Storage,
        evm_state.evm_transient_storage.TransientStorage
        == x86_state.evm_transient_storage.TransientStorage,
        evm_state.error_code == x86_state.callengine_status_code,
    ]
    if compare_gas:
        conditions.append(
            evm_state.evm_gas.Gas == x86_state.callengine_gas_remaining
        )
    return conditions


# ---------------------------------------------------------------------------
# 归纳步检查器
# ---------------------------------------------------------------------------

class Tier1LoopInduction:
    """对一对已配对循环执行 §4.2 的归纳步（②a–d）。

    Args:
        evm_blocks / x86_blocks: 两侧完整程序块表。
        evm_header / x86_header: 配对循环头。
        evm_exits / x86_exits: 循环出口目标（按序配对；数量不等 ⇒ inconclusive）。
        stack_depth: 该深度类下循环头的绝对栈深 k（EVM 栈槽数）。
        timeout_ms: 单条 Z3 查询预算。
        extra_invariant: 循环特定的 R 强化合取（如"栈顶 hi-192 为 0"）。
            会作为归纳前提加在 cutpoint 上，并作为证明义务加在 latch/exit
            的 R 目标里（前提与义务成对出现，保证强化是归纳的而非白嫖）。
        enable_oog_bridge: 是否启用 §4.8 的 OOG 谓词桥接（默认 **关闭**）。
            这是路径规模优化，不是健全性机制——关闭时逐字回到原枚举行为。
        oog_bridge_timeout_ms: 桥接等价性查询的预算（SAT/unknown/超时都不桥接）。
        oog_polarity_timeout_ms: 单条路径极性判定查询的预算上限。极性判不出来
            只是少剪一对，所以这里刻意给小预算，避免优化本身变成瓶颈。
    """

    def __init__(
        self,
        evm_blocks: Sequence[EVMBlock],
        x86_blocks: Sequence[X86Block],
        evm_header: int,
        x86_header: int,
        evm_exits: Sequence[int],
        x86_exits: Sequence[int],
        stack_depth: int,
        timeout_ms: int = 30000,
        max_depth: int = 400,
        extra_invariant: Optional[
            Callable[[SMTState, SMTState], List]
        ] = None,
        evm_body: Optional[Set[int]] = None,
        aot_profile=None,
        relation_schema: Optional[CutpointRelationSchema] = None,
        compare_terminal_gas: bool = False,
        host_gas_uf_enabled: bool = False,
        abstract_calldataload_words: bool = False,
        assume_calldata_offset_no_overflow: bool = True,
        enable_oog_bridge: bool = False,
        oog_bridge_timeout_ms: int = DEFAULT_BRIDGE_TIMEOUT_MS,
        oog_polarity_timeout_ms: int = 20000,
    ):
        # gas 的双重身份（§4.1）在这里落地成两个独立开关：
        # - `host_gas_uf_enabled` 决定 **havoc 状态**是否扣 host cost。它必须与
        #   调用方的 GasCheck 档位一致，否则归纳会在一个 host gas 全免的语义上
        #   证明——路径集与真实执行不同。
        # - `compare_terminal_gas` 决定 ②(d)/③ 的终止可观测量**是否含 gas**。
        #   只在 FIXED_BUDGET/FULL 打开；cutpoint 上的 gas 相等是 R 的分量，
        #   三档都要，与这个开关无关。
        self.compare_terminal_gas = compare_terminal_gas
        self.host_gas_uf_enabled = host_gas_uf_enabled
        # calldata 语义开关：与 gas 档位同理，必须与调用方一致并进缓存键。
        self.abstract_calldataload_words = abstract_calldataload_words
        self.assume_calldata_offset_no_overflow = (
            assume_calldata_offset_no_overflow
        )
        self.aot_profile = aot_profile
        # §4.8：默认关闭。开关本身也必须进调用方的定理缓存键——开与关证出的是
        # 同一条定理（剪掉的对是**已证**不可共现的），但查询轨迹不同，缓存混用
        # 会让"实测收益"这类台账串味。
        self.enable_oog_bridge = enable_oog_bridge
        self.oog_bridge_timeout_ms = oog_bridge_timeout_ms
        self.oog_polarity_timeout_ms = oog_polarity_timeout_ms
        # R 的单点定义：havoc 与证明义务由它成对生成并强制分量对称（§4.3）。
        self.relation_schema = relation_schema or CutpointRelationSchema()
        self._relation_context: Optional[RelationContext] = None
        self._cut_mem0 = None
        self.evm_blocks = list(evm_blocks)
        self.x86_blocks = list(x86_blocks)
        self.evm_header = evm_header
        self.x86_header = x86_header
        self.evm_exits = sorted(evm_exits)
        self.stack_depth = stack_depth
        self.timeout_ms = timeout_ms
        self.max_depth = max_depth
        self.extra_invariant = extra_invariant
        self.evm_body = set(evm_body) if evm_body is not None else None

        # TAG 错误 stub 不是可配对出口（§4.2 ②(d)）：它们既不回循环头也不走
        # 正常出口，不该按地址与 EVM 出口边配对。不进 stop 集，让段执行跑进去
        # 变成 terminal 路径，由 ②(d) 与 EVM 侧对应的错误终态一起证 status /
        # 可观测量等价。**注意与旧行为的区别**：旧版在 run_x86_segment 里把这
        # 些 terminal 路径整个丢弃（envelope 排除），现在它们照常参与证明。
        # 用**活动 profile** 的状态码表：调用方传了重映射状态码的 profile 时，
        # 硬编码 GO_HPC_EVM_PROFILE 会把真实错误 stub 当成普通出口（或反之），
        # 最终以出口数量不匹配的形式无谓降级。
        from x86_64.aot_profile import GO_HPC_EVM_PROFILE
        active_profile = self.aot_profile or GO_HPC_EVM_PROFILE
        error_codes = {
            code
            for name, code in active_profile.status_codes.items()
            if name in _TERMINAL_ERROR_STATUSES
        }
        blocks_by_addr = {b.start_addr: b for b in self.x86_blocks}
        pairable = []
        for addr in sorted(x86_exits):
            block = blocks_by_addr.get(addr)
            status = x86_error_stub_status(block) if block is not None else None
            if status is not None and status in error_codes:
                continue
            pairable.append(addr)
        self.x86_exits = pairable

    # -- cutpoint havoc 状态 ---------------------------------------------

    def build_cut_state(self, byte_offset_value: Optional[int] = None) -> SMTState:
        """构造 havoc 后的 cutpoint 状态（§4.3），委托给关系 schema。

        分量的 havoc 绑定与 R 的证明义务由
        :class:`verification.cutpoint_relation.CutpointRelationSchema` 成对生成，
        两者的具名分量集合被强制一致。**不要在这里手工补 havoc**：只改 havoc
        不改证明目标，会把该分量静默移出验证范围（假绿方向），而这里没有任何
        机制能发现——那正是 host-gas 序号 / lastGasCost / return data 三处
        缺口的成因。要加分量请改 schema 的 ``_COMPONENTS``。
        """
        context = self.relation_schema.build_havoc(
            self.stack_depth,
            byte_offset_value=byte_offset_value,
            host_gas_uf_enabled=self.host_gas_uf_enabled,
            abstract_calldataload_words=self.abstract_calldataload_words,
            assume_calldata_offset_no_overflow=(
                self.assume_calldata_offset_no_overflow
            ),
        )
        self._relation_context = context
        self._cut_mem0 = context.memory_snapshot
        return context.state

    # -- 结构预检 ---------------------------------------------------------

    def _invariant_premises(self, cut_state: SMTState) -> List:
        """cutpoint 上作为**归纳前提**的不变式（两侧共享同一状态视图）。

        含调用方的 `extra_invariant` 与 schema 的 `persistent_invariants`。
        后者若只出现在证明目标里而不在前提里，求解器就得从任意 havoc 状态凭空
        推出它——那不是不健全，但会让本可证明的循环无谓 inconclusive。
        """
        premises: List = []
        if self.extra_invariant is not None:
            premises.extend(self.extra_invariant(cut_state, cut_state))
        for invariant in getattr(
            self.relation_schema, "persistent_invariants", ()
        ) or ():
            premises.extend(invariant(cut_state, cut_state))
        return premises

    def _invariant_goals(self, evm_state: SMTState, x86_state: SMTState) -> List:
        """latch/exit/再入处**重建**不变式的证明义务（与前提成对出现）。

        前提与义务必须成对：只当前提是白嫖（定理凭空更强），只当义务是无谓降级。
        注意 `schema.goals()` 已经把 `persistent_invariants` 算进 R 的合取，
        所以这里只补 `extra_invariant`，避免重复。
        """
        if self.extra_invariant is None:
            return []
        return list(self.extra_invariant(evm_state, x86_state))

    def _domain_goals(self, evm_state: SMTState, x86_state: SMTState) -> List:
        """②的 havoc 域约束在给定状态上的重述（定理的适用域）。

        `build_havoc` 注入 `MSize ≤ max` 与 32 字节对齐两条假设，定理只在它们
        成立时有效。Base/application 必须在**实际到达状态**上证明它们——否则
        循环头可以在 `MSize > max` 处被到达，而证书照样签发（假绿）。

        两侧都要证：R 的 `memory_size` 分量保证两侧 MSize 相等，但那是 R 的
        结论、不是前提，这里不能靠它省掉一侧。**且必须按侧传 `side`**：两侧的
        内存大小落在不同字段上（EVM 是 `evm_memory.MSize`，x86 是
        `callengine_memory_size_bytes`），不传就会两侧读同一个镜像字段，EVM 侧
        那一半退化成恒真——名义上证了两侧、实际只证了一侧。
        """
        context = self._relation_context
        if context is None or context.domain_predicate is None:
            # 还没 havoc 过（如只跑 Base 的调用方）：借一次 schema 拿谓词。
            context = self.relation_schema.build_havoc(
                self.stack_depth,
                byte_offset_value=self.stack_depth * 0x20,
                host_gas_uf_enabled=self.host_gas_uf_enabled,
                abstract_calldataload_words=self.abstract_calldataload_words,
                assume_calldata_offset_no_overflow=(
                    self.assume_calldata_offset_no_overflow
                ),
            )
        predicate = context.domain_predicate
        if predicate is None:
            return []
        return (
            list(predicate(evm_state, side="evm"))
            + list(predicate(x86_state, side="x86"))
        )

    def _structural_goals(
        self, evm_state: SMTState, x86_state: SMTState, site: str
    ) -> Tuple[Optional[List], str]:
        """一处 cutpoint 结构前提在给定状态上的核对（§4.5.6）。

        status 刻意不进 R 的等式分量（那是过强约束，只制造无谓降级），但"两侧
        都还在 running"这件事必须自己成立——否则它就只剩 `create_initial_state`
        的初值在 by construction 撑着，一个已终止的状态可以冒充 cutpoint 到达
        状态。同类的还有"待消费队列为空"（cutpoint 在块边界）。

        Returns:
            ``(Z3 证明义务, "")``；Python 层当场违例时返回 ``(None, 原因)``，
            由调用方转成 inconclusive（fail-closed，不是反例）。
        """
        report: StructuralPremiseReport = (
            self.relation_schema.structural_premises(
                evm_state, x86_state, site=site
            )
        )
        if not report.ok:
            return None, (
                f"cutpoint structural premise violated at {site}: "
                + "; ".join(report.defects)
            )
        return list(report.conditions), ""

    def _structural_rejections(self) -> List[str]:
        reasons = []
        if len(self.evm_exits) != len(self.x86_exits):
            reasons.append(
                f"exit count mismatch: EVM {self.evm_exits} vs x86 "
                f"{[hex(a) for a in self.x86_exits]}"
            )
        header_block = next(
            (b for b in self.evm_blocks if b.pc == self.evm_header), None
        )
        if header_block is None:
            reasons.append(f"EVM header block pc={self.evm_header} not found")
            return reasons

        # 段结构校验：按"段入口到任一 stop"的**静态可达块**扫描，而不是只扫
        # 循环体。旧版只看 `evm_body`，会漏掉循环体经由未登记边到达、但仍在
        # 本次段执行范围内的块。
        #
        # MSIZE 现在**不再无条件拒绝**：R 的 `memory_size` 分量已钉住两侧
        # MSize（schema.supports_msize），读它是安全的。GAS 仍拒——放宽它需要
        # 先确认 `compileEVMGAS` 的取值在 havoc 的符号 gas 下与 EVM 侧逐字对齐。
        from verification.segment_validation import SegmentStructuralValidator

        validator = SegmentStructuralValidator()
        evm_stops = {self.evm_header, *self.evm_exits}
        evm_check = validator.validate_evm(
            self.evm_blocks,
            entry_pc=self.evm_header,
            stop_pcs=evm_stops,
            supports_msize=self.relation_schema.supports_msize,
        )
        reasons.extend(evm_check.reasons)

        x86_stops = {self.x86_header, *self.x86_exits}
        x86_check = validator.validate_x86(
            self.x86_blocks,
            entry_addr=self.x86_header,
            stop_addrs=x86_stops,
        )
        reasons.extend(x86_check.reasons)
        return reasons

    # -- 求解 --------------------------------------------------------------

    def _check_unsat(self, label, formula_terms, timeout_ms, queries) -> bool:
        solver = _make_solver(timeout_ms)
        solver.add(And(BoolVal(True), *formula_terms))
        started = time.time()
        result = solver.check()
        queries.append((label, f"{result} ({time.time() - started:.2f}s)"))
        return result == unsat

    def _proved_ite_polarities(
        self, solver_label: str, premises, goal_conditions, queries
    ) -> List:
        """把「这条路径已判定」的 ITE 极性作为**已证前提**返回（fail-closed）。

        判定方式：`premises ∧ c` 不可满足 ⇒ `premises ⊢ ¬c`（反之亦然）。因此
        返回的每条字面量都是完整前提的**逻辑后承**，把它加进后续查询是恒等
        变换（`A ⊨ e` ⟹ `A ≡ A ∧ e`），**不是**新假设——这一点与
        `common/div_bridge.py` 的"先证实参恒等再注入等式"是同一条纪律。

        判不出来（sat / unknown / 超预算）就不加：少一条提示只是慢一点，
        绝不猜极性——猜错方向会把一条本该证明的义务变成在错误分支上"证明"。

        为什么值得：见 `_collect_shared_bv_ite_conditions` 上方的说明。
        """
        candidates = _collect_shared_bv_ite_conditions(
            goal_conditions, _ITE_POLARITY_LIMIT
        )
        budget = min(self.timeout_ms, _ITE_POLARITY_TIMEOUT_MS)
        decided: List = []
        for index, condition in enumerate(candidates):
            label = f"{solver_label} ite-polarity#{index}"
            if self._check_unsat(
                f"{label} [assume]", premises + [condition], budget, queries
            ):
                decided.append(Not(condition))
                continue
            if self._check_unsat(
                f"{label} [assume not]",
                premises + [Not(condition)], budget, queries,
            ):
                decided.append(condition)
        return decided

    def _prove(self, solver_label: str, base_terms, evm_cond, x86_cond,
               goal_conditions, queries) -> bool:
        """证明 (base ∧ evm_cond ∧ x86_cond) ⇒ ∧goal，带后缀切片加速。

        弱化前提（条件子集）下 unsat ⇒ 完整前提下亦成立（健全）。
        """
        evm_terms = _conjuncts(evm_cond)
        x86_terms = _conjuncts(x86_cond)
        # store-forwarding：目标里的栈窗口读数嵌着逐字节 Store 链，Z3 对
        # 符号地址不转发；Python 层保守解析后再 simplify（融合
        # Concat-of-Extracts 等），对齐良好的目标常直接坍缩成 True。
        goal_conditions = [simplify(forward_selects(g)) for g in goal_conditions]
        negated_goal = Not(And(*goal_conditions))
        slice_budget = max(self.timeout_ms // 4, 10000)
        for e_slice, x_slice, tag in _suffix_slices(evm_terms, x86_terms):
            is_full = tag == "full"
            # 极性判定**只在切片全败之后**才做：绝大多数配对在 slice1/slice4 就
            # unsat 了，无条件判定会给 ②(d) 上百对终止路径各加若干条小查询——
            # 提速手段不该自己变成瓶颈。极性是在**完整前提**下证出的，所以只在
            # 完整查询里用它，前提强弱不匹配的问题也就不存在。
            hints = self._proved_ite_polarities(
                solver_label, base_terms + evm_terms + x86_terms,
                goal_conditions, queries,
            ) if is_full else []
            budget = self.timeout_ms if is_full else slice_budget
            if self._check_unsat(
                f"{solver_label} [{tag}]",
                base_terms + e_slice + x_slice + hints + [negated_goal],
                budget,
                queries,
            ):
                return True
        return False

    def _prove_disjoint(self, solver_label: str, base_terms, evm_cond, x86_cond,
                        queries) -> bool:
        """证明两路径条件不可同时满足（②(a) 决策对齐），带后缀切片加速。

        约束子集 unsat ⇒ 全集 unsat（健全）。
        """
        evm_terms = _conjuncts(evm_cond)
        x86_terms = _conjuncts(x86_cond)
        slice_budget = max(self.timeout_ms // 4, 10000)
        for e_slice, x_slice, tag in _suffix_slices(evm_terms, x86_terms):
            is_full = tag == "full"
            budget = self.timeout_ms if is_full else slice_budget
            if self._check_unsat(
                f"{solver_label} [{tag}]",
                base_terms + e_slice + x_slice,
                budget,
                queries,
            ):
                return True
        return False

    def _query_sat(self, solver_label: str, condition, queries, timeout_ms=None):
        solver = _make_solver(self.timeout_ms if timeout_ms is None else timeout_ms)
        solver.add(condition)
        started = time.time()
        result = solver.check()
        queries.append((solver_label, f"{result} ({time.time() - started:.2f}s)"))
        return result

    # -- §4.8 OOG 谓词桥接 --------------------------------------------------

    def _oog_stub_recognizer(self):
        """返回 `addr -> bool`，判断该地址是不是 out-of-gas 终止 stub。

        用**活动 profile** 的状态码：调用方传了重映射状态码的 profile 时，硬编码
        GO_HPC_EVM_PROFILE 会把别的 stub 当成 OOG（或反之），于是"这条 jb 通向
        OOG"这句话就成了未经核实的断言，桥接建立在错误的分支语义上。
        """
        from x86_64.aot_profile import GO_HPC_EVM_PROFILE

        profile = self.aot_profile or GO_HPC_EVM_PROFILE
        oog_code = profile.status_codes.get("out_of_gas")
        blocks_by_addr = {b.start_addr: b for b in self.x86_blocks}

        def _is_oog_stub(addr: int) -> bool:
            block = blocks_by_addr.get(addr)
            if block is None or oog_code is None:
                return False
            return x86_error_stub_status(block) == oog_code

        return _is_oog_stub

    def _build_oog_partition(
        self,
        cut_state: SMTState,
        evm_entry_pc: int,
        x86_entry_addr: int,
        assumptions: List,
        queries: List[Tuple[str, str]],
        site: str,
    ) -> Tuple[Optional[OogPartition], OogBridgeStats]:
        """§4.8 步骤 1–4：分别生成两侧 OOG 谓词 → 证等价 → 才给出分区。

        **两侧谓词各自独立生成**（EVM 取 IR 的 `static_gas`，x86 解析机器码里
        `cmp <reg>, IMM` 的立即数），绝不共用一个 Boolean —— 共用等于把待证命题
        假设掉，静态 gas 常量编错这类 codegen bug 会被完全掩盖。

        返回 `(None, stats)` 的每一种情形都是**降级**：调用方照常跑全量矩阵。
        """
        stats = OogBridgeStats(site=site)
        if not self.enable_oog_bridge:
            stats.reason = "oog bridge disabled (default); full matrix enumeration"
            return None, stats

        from x86_64.aot_profile import GO_HPC_EVM_PROFILE

        profile = self.aot_profile or GO_HPC_EVM_PROFILE
        gas_offset = profile.offsets.get("gas_remaining")

        evm_block = next(
            (b for b in self.evm_blocks if b.pc == evm_entry_pc), None
        )
        x86_block = next(
            (b for b in self.x86_blocks if b.start_addr == x86_entry_addr), None
        )
        if evm_block is None or x86_block is None or gas_offset is None:
            stats.status = "unavailable"
            stats.reason = (
                f"segment entry block not found (evm pc={evm_entry_pc}, "
                f"x86 addr={x86_entry_addr}) or profile has no gas offset"
            )
            return None, stats

        evm_threshold = evm_oog_threshold(evm_block)
        x86_guard = x86_tag_gas_guard(
            x86_block,
            gas_offset=gas_offset,
            oog_stub_ok=self._oog_stub_recognizer(),
        )
        stats.evm_threshold = -1 if evm_threshold is None else evm_threshold
        stats.x86_threshold = -1 if x86_guard is None else x86_guard.threshold

        evm_predicate = evm_oog_predicate(evm_block, cut_state)
        x86_predicate = x86_oog_predicate(
            x86_block,
            cut_state,
            gas_offset=gas_offset,
            oog_stub_ok=self._oog_stub_recognizer(),
        )
        report = verified_oog_bridge(
            evm_predicate,
            x86_predicate,
            assumptions,
            name=site,
            evm_threshold=stats.evm_threshold,
            x86_threshold=stats.x86_threshold,
            verify_timeout_ms=self.oog_bridge_timeout_ms,
        )
        queries.extend(report.queries)
        stats.status = report.status
        stats.reason = report.reason
        return report.partition, stats

    def _partition_polarities(
        self,
        partition: Optional[OogPartition],
        paths: List[SegmentPath],
        side: str,
        base,
        queries: List[Tuple[str, str]],
        stats: Optional[OogBridgeStats] = None,
    ) -> List[Optional[bool]]:
        """判定每条路径相对分区谓词的极性（True=必 OOG / False=必非 OOG）。

        两级：

        1. **语法**（0 次求解）：路径条件的合取字面量里直接含该谓词或其否定 ⇒
           `A ∧ p ⇒ p` 是语法蕴含。EVM 侧 100% 走这条——执行器把 `simplify` 后的
           `ULT(gas, static_gas)` 原样塞进路径条件。
        2. **求解器兜底**（≤2 次小预算查询）：x86 侧的分支条件是 `CF == 1` 这种
           标志位形式，语法上对不上，只能证 `base ∧ cond ⇒ ±p`。

        判不出来就返回 None ⇒ 该路径不参与剪枝（保守方向，只是少省一点）。
        **绝不猜极性**：猜错方向会把一对真正需要证明的组合当成"已排除"。
        """
        if partition is None:
            return [None] * len(paths)

        tally = stats if stats is not None else OogBridgeStats()
        predicate = (
            partition.evm_predicate if side == "evm" else partition.x86_predicate
        )
        budget = min(self.timeout_ms, self.oog_polarity_timeout_ms)
        polarities: List[Optional[bool]] = []
        for index, path in enumerate(paths):
            syntactic = conjunct_polarity(path.condition, predicate)
            if syntactic is not None:
                tally.polarity_syntactic += 1
                polarities.append(syntactic)
                continue
            label = f"{partition.name} polarity {side}#{index}({path.kind})"
            tally.polarity_queries += 1
            if self._query_sat(
                f"{label} [assume oog]",
                And(base, path.condition, predicate),
                queries,
                timeout_ms=budget,
            ) == unsat:
                # base ∧ cond ∧ p 不可满足 ⇒ base ∧ cond ⇒ ¬p
                tally.polarity_solved += 1
                polarities.append(False)
                continue
            tally.polarity_queries += 1
            if self._query_sat(
                f"{label} [assume not-oog]",
                And(base, path.condition, Not(predicate)),
                queries,
                timeout_ms=budget,
            ) == unsat:
                tally.polarity_solved += 1
                polarities.append(True)
                continue
            tally.polarity_unknown += 1
            polarities.append(None)
        return polarities

    # -- 配对矩阵验证（①②③ 共用） --------------------------------------

    def _verify_path_matrix(
        self,
        evm_paths: List[SegmentPath],
        x86_paths: List[SegmentPath],
        assumptions: List,
        compatible_fn,
        goals_fn,
        alignment_tag: str,
        queries: List[Tuple[str, str]],
        partition: Optional[OogPartition] = None,
        stats: Optional[OogBridgeStats] = None,
    ) -> Optional[LoopInductionResult]:
        """公共配对矩阵验证：可行性预过滤 → 决策对齐/joint-sat → 证明义务
        → 空洞守卫。全部通过返回 None，否则返回 inconclusive 结果。

        Args:
            compatible_fn(ep, xp) -> bool：两条路径是否是"应当共现"的组合。
            goals_fn(ep, xp, pair_label) -> (goal 条件列表, 查询标签)；
                返回 (None, reason) 表示该对无法构造证明义务 ⇒ inconclusive。
            alignment_tag：失配查询的标签前缀（②(a) / ①-align / ③-align）。
            partition：§4.8 已证等价的 OOG 谓词对；None（默认）⇒ 逐字保持
                原枚举行为，一次额外查询都不发。
            stats：桥接台账（收益计数写回处）。
        """
        base = And(BoolVal(True), *assumptions)

        # 可行性预过滤：base 下 UNSAT 的路径被证明不可达（等价于
        # reachability 剪枝）。unknown 保守保留（可能可行）。
        def _feasible(paths, side):
            kept = []
            verdicts = []
            for idx, path in enumerate(paths):
                verdict = self._query_sat(
                    f"feasibility {side}#{idx}({path.kind})",
                    And(base, path.condition),
                    queries,
                )
                if verdict != unsat:
                    kept.append(path)
                    verdicts.append(verdict)
            return kept, verdicts

        evm_paths, evm_feasibility = _feasible(evm_paths, "evm")
        x86_paths, x86_feasibility = _feasible(x86_paths, "x86")
        if not evm_paths or not x86_paths:
            return LoopInductionResult.inconclusive(
                "all paths on one side infeasible under cutpoint assumptions",
                queries,
            )

        # §4.8：极性只在**预过滤之后**判定——不可行路径已经出局，为它们花查询
        # 纯属浪费。partition 为 None 时这两行是零成本的 [None]*n。
        evm_polarity = self._partition_polarities(
            partition, evm_paths, "evm", base, queries, stats
        )
        x86_polarity = self._partition_polarities(
            partition, x86_paths, "x86", base, queries, stats
        )

        evm_partner_count = [0] * len(evm_paths)
        x86_partner_count = [0] * len(x86_paths)
        if stats is not None:
            stats.pairs_total += len(evm_paths) * len(x86_paths)

        for i, ep in enumerate(evm_paths):
            for j, xp in enumerate(x86_paths):
                pair_label = f"evm#{i}({ep.kind})/x86#{j}({xp.kind})"
                joint = And(base, ep.condition, xp.condition)

                if cross_polarity_excluded(evm_polarity[i], x86_polarity[j]):
                    # 桥接已证 `oog_evm ↔ oog_x86`，而这两条路径分别蕴含该谓词
                    # 的相反极性 ⇒ 三者合取恒假，这一对**被证明**不可共现。
                    #
                    # 这不是"跳过义务"：不兼容对本来就要证 disjoint（这里已证），
                    # 兼容对本来 joint-sat 会返回 unsat 并 `continue`（partner
                    # 计数同样不增）。两条原路径的结论都被完整复现，省下的只是
                    # 求解器往返。partner 计数保持不增是关键——空洞守卫必须继续
                    # 抓得住"某条路径根本没有可共现伙伴"。
                    if stats is not None:
                        stats.pairs_pruned += 1
                    queries.append((
                        f"{alignment_tag} partition {pair_label}",
                        f"pruned by proved {partition.name} bridge "
                        "(no solver query)",
                    ))
                    continue

                if not compatible_fn(ep, xp):
                    # 决策对齐：不兼容的组合必须不可行
                    if not self._prove_disjoint(
                        f"{alignment_tag} alignment {pair_label}",
                        assumptions, ep.condition, xp.condition, queries,
                    ):
                        return LoopInductionResult.inconclusive(
                            f"branch decisions may diverge: {pair_label}", queries
                        )
                    continue

                # 非空洞守卫的数据：joint 可满足的对才是真正的证明义务；
                # unsat 对不可共现（vacuous），unknown 保守履行义务但不计
                # partner。
                joint_feasibility = self._query_sat(
                    f"joint-sat {pair_label}", joint, queries
                )
                if joint_feasibility == unsat:
                    continue
                if joint_feasibility == sat:
                    evm_partner_count[i] += 1
                    x86_partner_count[j] += 1

                goals, label = goals_fn(ep, xp, pair_label)
                if goals is None:
                    return LoopInductionResult.inconclusive(label, queries)
                if not self._prove(
                    label, assumptions, ep.condition, xp.condition, goals, queries
                ):
                    return LoopInductionResult.inconclusive(
                        f"R/observables not preserved on {pair_label} "
                        "(SAT/unknown ⇒ inconclusive, NOT a counterexample)",
                        queries,
                    )

        # 空洞守卫：预过滤保留的路径全部 sat-or-unknown（可能可行），任何
        # 一条没有对侧可共现伙伴 ⇒ inconclusive。unknown 也设防（fail-closed）。
        for i, ep in enumerate(evm_paths):
            if evm_partner_count[i] == 0:
                return LoopInductionResult.inconclusive(
                    f"vacuous check: evm#{i}({ep.kind}) "
                    f"(standalone feasibility={evm_feasibility[i]}) has "
                    "no co-satisfiable x86 partner",
                    queries,
                )
        for j, xp in enumerate(x86_paths):
            if x86_partner_count[j] == 0:
                return LoopInductionResult.inconclusive(
                    f"vacuous check: x86#{j}({xp.kind}) "
                    f"(standalone feasibility={x86_feasibility[j]}) has "
                    "no co-satisfiable EVM partner",
                    queries,
                )
        return None

    # -- 归纳步 ------------------------------------------------------------

    def check_inductive_step(
        self,
        summary_config=None,
        *,
        premise_discharges: Optional[ExternalPremiseDischarges] = None,
    ) -> LoopInductionResult:
        """②：一轮循环体的锁步归纳（a–e）。

        `summary_config` 与 ①③ 用同一份：循环体内若含需要 CALLDATALOAD /
        MUL / copy-loop summary 才能越过的内生循环或访存切片，②裸执行会
        depth-prune、抛路由错误或直接 inconclusive（降级）。

        `premise_discharges` 让确实兑现了 §6 结构守卫 / 外层证明图那两条前提的
        调用方把它们置位；默认（None）等价于两条都未兑现。
        """
        queries: List[Tuple[str, str]] = []

        structural = self._structural_rejections()
        if structural:
            return LoopInductionResult.inconclusive("; ".join(structural))

        cut_state = self.build_cut_state()

        evm_stops = {self.evm_header, *self.evm_exits}
        x86_stops = {self.x86_header, *self.x86_exits}

        evm_paths, evm_defects = run_evm_segment(
            self.evm_blocks, cut_state.copy(), self.evm_header, evm_stops,
            max_depth=self.max_depth,
        )
        x86_paths, x86_defects, segment_notes = run_x86_segment(
            self.x86_blocks, cut_state.copy(), self.x86_header, x86_stops,
            max_depth=self.max_depth,
            aot_profile=self.aot_profile,
            summary_config=summary_config,
        )
        defects = evm_defects + x86_defects
        if defects:
            # 段执行本身有覆盖缺口 ⇒ 归纳前提不成立，fail-closed
            return LoopInductionResult.inconclusive("; ".join(defects), queries)
        if not evm_paths or not x86_paths:
            return LoopInductionResult.inconclusive(
                f"segment produced no paths (EVM {len(evm_paths)}, x86 {len(x86_paths)})",
                queries,
            )

        exit_pairing: Dict[int, int] = dict(zip(self.evm_exits, self.x86_exits))

        assumptions = list(getattr(cut_state, "assumptions", None) or [])
        assumptions.extend(self._invariant_premises(cut_state))

        # §4.8：桥接**必须在 assumptions 定稿之后、任何矩阵查询之前**建立，
        # 因为等价性正是在这一批 assumptions 下证的。之后再把已证等式并进
        # assumptions 是逻辑恒等变换（`A ⇒ e` ⟹ `A ≡ A ∧ e`），纯提示，
        # 不引入任何未证前提。
        partition, oog_stats = self._build_oog_partition(
            cut_state, self.evm_header, self.x86_header, assumptions, queries,
            site="header-oog",
        )
        if partition is not None:
            assumptions.append(partition.equality)

        def _compatible(ep, xp):
            return (
                (ep.kind == xp.kind == "latch")
                or (ep.kind == xp.kind == "terminal")
                or (
                    ep.kind == xp.kind == "exit"
                    and exit_pairing.get(ep.location) == xp.location
                )
            )

        def _goals(ep, xp, pair_label):
            if ep.kind == "terminal":
                # ②(d)：体内终止路径可观测量等价
                return (
                    terminal_observable_conditions(
                        ep.state, xp.state, cut_mem0=self._cut_mem0,
                        compare_gas=self.compare_terminal_gas,
                    ),
                    f"②(d) terminal {pair_label}",
                )
            # ②(b)/(c)：回边/出口处 R 保持。传 context ⇒ 顺带触发分量对称性断言。
            goals = coupling_conditions(
                ep.state, xp.state, self.stack_depth,
                schema=self.relation_schema,
                context=self._relation_context,
            )
            # **域约束必须在回边/出口处闭合**。havoc 注入了 `MSize ≤ 4MiB` 等
            # 约束、定理只在该域内成立；若一轮循环体扩容后跨出域外，下一轮就
            # 在域外复用了只在域内成立的定理，③也只从域内的 havoc 状态验证了
            # 一个并不覆盖实际出口的后缀（假绿）。把它做成归纳的一部分：域内
            # 进、域内出。
            goals = list(goals) + self._domain_goals(ep.state, xp.state)
            # **结构前提同样要闭合**（§4.5.6 的 ③④ 两处覆盖点）：havoc 假设了
            # 两侧都在 running，若一轮之后回边/出口处不再成立，下一轮就在前提
            # 不成立的状态上复用了定理。
            site = "latch_reentry" if ep.kind == "latch" else "exit_edge"
            structural, defect = self._structural_goals(
                ep.state, xp.state, site
            )
            if structural is None:
                return None, defect
            goals = goals + structural
            if self.extra_invariant is not None:
                # 证明义务：不变式在回边/出口处重新成立（归纳闭合）
                goals.extend(self.extra_invariant(ep.state, xp.state))
            label = (
                f"②(b) latch R {pair_label}"
                if ep.kind == "latch"
                else f"②(c) exit R {pair_label}"
            )
            return goals, label

        failure = self._verify_path_matrix(
            evm_paths, x86_paths, assumptions, _compatible, _goals,
            "②(a)", queries, partition=partition, stats=oog_stats,
        )
        if failure is not None:
            failure.oog_bridge = oog_stats
            return failure

        # ②(e)：在同一批 latch 路径上收集终止证据
        termination = self._collect_termination_evidence(
            cut_state, evm_paths, assumptions, queries,
            segment_defects=defects,
            premise_discharges=premise_discharges,
        )
        # §4.1 (ii)：latch 只转移到已登记深度类（转移封闭）
        depth_evidence = self._check_depth_transition_closure(evm_paths)

        return LoopInductionResult(
            status="proved", reasons=segment_notes, queries=queries,
            termination=termination, depth_evidence=depth_evidence,
            structural_premise_sites=STEP_STRUCTURAL_SITES,
            oog_bridge=oog_stats,
        )

    def _check_depth_transition_closure(
        self, evm_paths: List[SegmentPath]
    ) -> DepthClassEvidence:
        """§4.1 (ii)：每条 latch 回到循环头时的绝对栈深仍在已登记集合内。

        本次归纳步是按单个深度类 `self.stack_depth` 实例化的，因此"封闭"就是
        latch 处 SP 仍等于该值。落在集合外的深度会被记进 `escaping_depths`
        ——那意味着存在**未登记**的深度类，枚举不完整，调用方必须降级或补证
        该类，而不是当作已覆盖。
        """
        registered = (self.stack_depth,)
        evidence = DepthClassEvidence(registered_classes=registered)
        escaping: List[int] = []

        for path in evm_paths:
            if path.kind != "latch":
                continue
            evidence.latch_transitions_checked += 1
            sp = simplify(path.state.evm_stack.SP)
            try:
                depth = sp.as_long()
            except AttributeError:
                # 符号深度 ⇒ 无法判定封闭性，按逃逸处理（fail-closed 方向）
                escaping.append(-1)
                continue
            if depth in registered:
                evidence.latch_transitions_closed += 1
            else:
                escaping.append(depth)

        evidence.escaping_depths = tuple(escaping)
        return evidence

    # -- ②(e) 终止义务 ------------------------------------------------------

    def _collect_termination_evidence(
        self, cut_state: SMTState, evm_paths: List[SegmentPath],
        assumptions: List, queries: List[Tuple[str, str]],
        segment_defects: Sequence[str] = (),
        premise_discharges: Optional[ExternalPremiseDischarges] = None,
    ) -> TerminationEvidence:
        """证明每条可行 latch arm 严格降低无符号 gas（§4.2 ②(e)）。

        gas 是循环 latch 的 ranking function：cutpoint 上 gas 是 havoc 的任意
        符号（不是具体值），一轮回到循环头时若必然严格变小，则不存在无限
        latch 序列。

        **这只是六项前提中的一条**，不等于"证明了循环终止"——其余五项
        （段覆盖完整 / 无位向量回绕 / 段内无未识别循环 / SCC 已切断 /
        无无限 stuttering）由别处保证，逐条记进 `external_premises`，由证书
        汇总。把这条单独说成终止论证是过强的（见 §2.1）。

        Args:
            premise_discharges: 调用方兑现的外部前提。归纳步看不见 §6 结构守卫
                与外层证明图的结论，只有真正跑过它们的那一层才有资格置位；
                默认（None）两条都算未兑现。
        """
        from z3 import ULT

        discharges = premise_discharges or ExternalPremiseDischarges()
        evidence = TerminationEvidence()
        gas_in = cut_state.evm_gas.Gas
        latches = [p for p in evm_paths if p.kind == "latch"]

        for index, path in enumerate(latches):
            evidence.latch_arms_checked += 1
            label = f"②(e) gas decreases on latch#{index}"
            # 反例查询：路径可行 ∧ gas 未严格变小
            terms = list(assumptions) + [
                path.condition,
                Not(ULT(path.state.evm_gas.Gas, gas_in)),
            ]
            if self._check_unsat(label, terms, self.timeout_ms, queries):
                evidence.latch_arms_decreasing += 1

        # 无回绕依据：consume_static 是纯减法不钳零，而 OOG 分叉保证到达
        # 减法时 gas 已足够（Gas 设计 §5），因此不会下溢回绕。这条是结构
        # 性论证而非本处的 SMT 查询，如实标注来源。
        evidence.no_wraparound_basis = (
            "TAG guard forks on ULT(gas, static_gas) before the subtraction "
            "(state/evm_gas_state.consume_static is a plain non-clamping "
            "subtraction); see docs/Gas一致性验证设计.md §5"
        )
        # 外部前提：`discharged` 只在**真正兑现**它时才置 True。三条由本方法
        # 所在的这次段执行兑现（它们的证据就在手边）；另两条归本引擎之外的
        # 结构守卫与证明图，只能由跑过它们的调用方经 `premise_discharges` 置位
        # ——不传就是没兑现，绝不默认成 True。
        segment_coverage_ok = not segment_defects
        evidence.external_premises = [
            ExternalPremise(
                name="segment_coverage_completeness",
                detail=(
                    "both sides' path_coverage_certificate reported complete "
                    "for this segment"
                ),
                responsible="run_evm_segment / run_x86_segment",
                discharged=segment_coverage_ok,
            ),
            ExternalPremise(
                name="no_unidentified_inner_loop",
                detail=(
                    "every x86 back edge inside the segment is either Tier-1 "
                    "paired or matched by a proved Tier-2 lemma (§6 guard)"
                ),
                responsible="verification.loop_pairing / §6 structural guard",
                # 本查询看不到全局守卫的结论，由调用方在接入守卫后置位
                discharged=discharges.no_unidentified_inner_loop,
            ),
            ExternalPremise(
                name="all_sccs_cut_or_certified",
                detail=(
                    "every SCC in the proof skeleton is either cut at a "
                    "cutpoint or carries its own termination certificate"
                ),
                responsible="enclosing cutpoint proof graph",
                discharged=discharges.all_sccs_cut_or_certified,
            ),
            ExternalPremise(
                name="no_infinite_x86_stuttering",
                detail=(
                    "the segment executor is depth-bounded and reports "
                    "coverage defects fail-closed, so a non-terminating x86 "
                    "stutter shows up as an incomplete certificate"
                ),
                responsible="run_x86_segment coverage certificate",
                discharged=segment_coverage_ok,
            ),
            ExternalPremise(
                name="sat_unknown_coverage_fail_closed",
                detail=(
                    "_verify_path_matrix turns SAT/unknown/coverage gaps into "
                    "inconclusive rather than success"
                ),
                responsible="Tier1LoopInduction._verify_path_matrix",
                discharged=True,
            ),
        ]
        return evidence

    # -- ① Base 查询 --------------------------------------------------------

    def check_base_query(
        self,
        initial_state: SMTState,
        evm_entry_pc: Optional[int] = None,
        x86_entry_addr: Optional[int] = None,
        max_depth: int = 500,
        x86_reachability: bool = True,
        summary_config=None,
    ) -> LoopInductionResult:
        """① Base：从真实入口符号执行到两侧循环头，证明每条到达路径上
        R 成立，并提取绝对栈深类（供 ②③ 按类实例化）。

        入口状态是**真实**初始状态（非 havoc）——两侧共享同一 SMTState 的
        符号 calldata/storage，storage/calldata 耦合 by construction；栈从
        空开始，到达时窗口内容由两侧各自执行建立，R 是真正的证明义务。

        x86 侧默认开 reachability check：base 段跑的是真实入口的整程序
        前缀，具体死分支（selector 分派等）不剪会路径爆炸。

        **① 刻意不接 §4.8 的 OOG 分区**（不是漏了）：Base 只把「到达循环头」的
        路径送进矩阵（terminal 路径已被过滤掉），它们相对**入口块**的 OOG 谓词
        极性必然一致，分区分不出任何东西，却要为每条路径付极性判定的查询。
        路径规模问题出在 ②③ 的 havoc 段上，对策也就留在那两处。
        """
        queries: List[Tuple[str, str]] = []
        base_mem0 = initial_state.evm_memory.Memory

        if evm_entry_pc is None:
            evm_entry_pc = self.evm_blocks[0].pc
        if x86_entry_addr is None:
            x86_entry_addr = min(b.start_addr for b in self.x86_blocks)

        evm_paths, evm_defects = run_evm_segment(
            self.evm_blocks, initial_state.copy(), evm_entry_pc,
            {self.evm_header}, max_depth=max_depth,
        )
        x86_paths, x86_defects, segment_notes = run_x86_segment(
            self.x86_blocks, initial_state.copy(), x86_entry_addr,
            {self.x86_header}, max_depth=max_depth,
            aot_profile=self.aot_profile,
            use_reachability_check=x86_reachability,
            summary_config=summary_config,
        )
        # 缺陷门是**非对称**的：EVM 侧证书必须完整（漏掉一条会到达的
        # EVM 路径 ⇒ 该首次到达的 R 义务凭空消失 ⇒ 组合不健全）；x86 侧
        # 深度剪枝可容忍——base 只关心到达路径，若被剪的 x86 路径本会
        # 到达，其输入不被 Or(x86 到达) 覆盖，evm⇒x86 对齐义务必失败
        # （fail-closed）；被剪的非到达路径（合约其他函数区域，含 Tier-2
        # 拷贝循环）与 ① 无关。
        if evm_defects:
            return LoopInductionResult.inconclusive("; ".join(evm_defects), queries)
        segment_notes = list(segment_notes) + [
            f"x86 base segment note: {d}" for d in x86_defects
        ]

        evm_arrivals = [
            p for p in evm_paths
            if p.kind != "terminal" and p.location == self.evm_header
        ]
        x86_arrivals = [
            p for p in x86_paths
            if p.kind != "terminal" and p.location == self.x86_header
        ]
        if not evm_arrivals:
            return LoopInductionResult.inconclusive(
                "base query: no EVM arrival at loop header from entry "
                "(unreached from this entry condition)",
                queries,
            )

        # 深度类提取：到达时的 EVM 绝对栈深必须是具体值
        from z3 import IntVal
        depth_classes: Set[int] = set()
        arrival_depths: List[int] = []
        for p in evm_arrivals:
            sp = simplify(p.state.evm_stack.SP)
            try:
                depth = sp.as_long()
            except AttributeError:
                return LoopInductionResult.inconclusive(
                    f"base query: symbolic stack depth at arrival ({sp})",
                    queries,
                )
            depth_classes.add(depth)
            arrival_depths.append(depth)

        assumptions = list(getattr(initial_state, "assumptions", None) or [])

        # ①-对齐：EVM 到达 ⟺ x86 到达（一侧到循环头而另一侧不到 ⇒ 失配）
        from z3 import Or
        or_x86 = (
            Or(*[p.condition for p in x86_arrivals])
            if x86_arrivals else BoolVal(False)
        )
        or_evm = Or(*[p.condition for p in evm_arrivals])
        for i, ep in enumerate(evm_arrivals):
            if not self._prove_disjoint(
                f"①-align evm-arrival#{i} ⇒ x86-arrival",
                assumptions, ep.condition, Not(or_x86), queries,
            ):
                return LoopInductionResult.inconclusive(
                    f"base query: EVM arrival#{i} may occur without x86 arrival",
                    queries,
                )
        for j, xp in enumerate(x86_arrivals):
            if not self._prove_disjoint(
                f"①-align x86-arrival#{j} ⇒ evm-arrival",
                assumptions, xp.condition, Not(or_evm), queries,
            ):
                return LoopInductionResult.inconclusive(
                    f"base query: x86 arrival#{j} may occur without EVM arrival",
                    queries,
                )

        # ①-R：每对可共现的到达路径上 R 成立（栈深取该 EVM 路径的深度类）
        def _compatible(ep, xp):
            return True  # 到达对齐已单独证明，到达×到达全部是义务对

        def _goals(ep, xp, pair_label):
            depth = arrival_depths[evm_arrivals.index(ep)]
            goals = coupling_conditions(
                ep.state, xp.state, depth, cut_mem0=base_mem0,
                # **必须传 schema**：不传会回落到模块级默认关系，于是带
                # `persistent_invariants` 的自定义 schema 在 ② 下证出的定理，
                # 会被一个从未证明该关系的 Base 放行（假绿）。
                schema=self.relation_schema,
            )
            # ② 的 havoc 注入了域约束（`MSize ≤ 4MiB`、32 字节对齐），定理**只在
            # 这个域内成立**。Base 必须证明实际到达状态落在域内，否则就是把定理
            # 用到证明域之外（假绿）。域约束由 schema 给出并重述到到达状态上。
            goals = list(goals) + self._domain_goals(ep.state, xp.state)
            # §4.5.6 覆盖点 ①：到达循环头时两侧都还在 running。② 的 havoc 把它
            # 当前提，Base 就必须在**实际到达状态**上证出来。
            structural, defect = self._structural_goals(
                ep.state, xp.state, "base_arrival"
            )
            if structural is None:
                return None, defect
            goals = goals + structural
            if self.extra_invariant is not None:
                # ② 把 I 当归纳前提用（`R ∧ I ⇒ 一轮后 R ∧ I`），所以 Base
                # **必须**在实际到达状态上证出 I——否则定理只在 I 的子域成立，
                # 却被应用到可能违反 I 的到达状态上（假绿）。
                goals = list(goals) + list(
                    self.extra_invariant(ep.state, xp.state)
                )
            return (
                goals,
                f"①-R base {pair_label} (depth={depth})",
            )

        failure = self._verify_path_matrix(
            evm_arrivals, x86_arrivals, assumptions, _compatible, _goals,
            "①", queries,
        )
        if failure is not None:
            return failure

        # §4.1 (i)：首次到达覆盖。段执行的 coverage 证书已在上面 fail-closed
        # 检查过（`evm_defects` 非空即 inconclusive），因此这里枚举到的深度类
        # 就是**全部**可能的首次到达深度——如实记录依据，供证书汇总。
        # (ii) 转移封闭由归纳步的 `_check_depth_transition_closure` 负责。
        depth_evidence = DepthClassEvidence(
            registered_classes=tuple(sorted(depth_classes)),
            arrival_coverage_basis=(
                "EVM base segment coverage certificate is complete "
                "(evm_defects empty), so every path reaching the loop header "
                "was enumerated and its concrete depth registered"
            ),
        )

        return LoopInductionResult(
            status="proved",
            reasons=segment_notes,
            queries=queries,
            depth_classes=sorted(depth_classes),
            depth_evidence=depth_evidence,
            structural_premise_sites=BASE_STRUCTURAL_SITES,
        )

    # -- ③ 出口查询 ---------------------------------------------------------

    def check_exit_query(
        self,
        stack_depth: int,
        evm_exit_pc: Optional[int] = None,
        x86_exit_addr: Optional[int] = None,
        max_depth: Optional[int] = None,
        summary_config=None,
    ) -> LoopInductionResult:
        """③ 出口：从"出口处 R 成立"（havoc + 全深度类窗口）继续符号执行
        到终止或回到循环头，证明终止可观测量等价 / 再入时 R 保持。

        havoc 覆盖整栈（stack_depth = 该深度类的绝对栈深，字节偏移取具体
        k*0x20）——caller-frame 返回地址等被 havoc 成共享符号；EVM 侧
        resolved_multi 返回跳靠执行器的 immediate_set 分叉（每叉带
        value==target 约束），与 x86 的 CMPQ+JEQ 比较链自然对齐。
        """
        queries: List[Tuple[str, str]] = []
        if evm_exit_pc is None:
            evm_exit_pc = self.evm_exits[0]
        if x86_exit_addr is None:
            x86_exit_addr = self.x86_exits[0]
        if max_depth is None:
            max_depth = self.max_depth

        saved_depth = self.stack_depth
        self.stack_depth = stack_depth
        try:
            cut_state = self.build_cut_state(
                byte_offset_value=stack_depth * 0x20
            )
        finally:
            self.stack_depth = saved_depth

        from utils.exceptions import UnsupportedJumpError
        try:
            evm_paths, evm_defects = run_evm_segment(
                self.evm_blocks, cut_state.copy(), evm_exit_pc,
                {self.evm_header, evm_exit_pc}, max_depth=max_depth,
            )
        except UnsupportedJumpError as exc:
            return LoopInductionResult.inconclusive(
                f"exit continuation hits unsupported jump: {exc}", queries
            )
        x86_paths, x86_defects, segment_notes = run_x86_segment(
            self.x86_blocks, cut_state.copy(), x86_exit_addr,
            {self.x86_header, x86_exit_addr}, max_depth=max_depth,
            aot_profile=self.aot_profile,
            summary_config=summary_config,
        )
        defects = evm_defects + x86_defects
        if defects:
            return LoopInductionResult.inconclusive("; ".join(defects), queries)
        if not evm_paths or not x86_paths:
            return LoopInductionResult.inconclusive(
                f"exit segment produced no paths (EVM {len(evm_paths)}, "
                f"x86 {len(x86_paths)})",
                queries,
            )

        # ③ 的 havoc 同样从「出口处 R ∧ I 成立」出发：②(c) 已在出口处建立 I，
        # 不把它作为前提就等于丢掉了一段已证信息（无谓降级）。
        assumptions = list(getattr(cut_state, "assumptions", None) or [])
        assumptions.extend(self._invariant_premises(cut_state))

        # §4.8：③ 的段入口是**出口块**，它同样带 TAG 序言、同样在 havoc 的符号
        # gas 下分叉出 OOG 路径，所以桥接的建立方式与 ② 完全一样，只是站点不同。
        partition, oog_stats = self._build_oog_partition(
            cut_state, evm_exit_pc, x86_exit_addr, assumptions, queries,
            site="exit-oog",
        )
        if partition is not None:
            assumptions.append(partition.equality)

        def _compatible(ep, xp):
            if ep.kind == xp.kind == "terminal":
                return True
            # 再入循环头 / 回到出口 cutpoint：按位置配对
            if ep.kind != "terminal" and xp.kind != "terminal":
                pairing = {
                    self.evm_header: self.x86_header,
                    evm_exit_pc: x86_exit_addr,
                }
                return pairing.get(ep.location) == xp.location
            return False

        def _goals(ep, xp, pair_label):
            if ep.kind == "terminal":
                return (
                    terminal_observable_conditions(
                        ep.state, xp.state, cut_mem0=self._cut_mem0,
                        compare_gas=self.compare_terminal_gas,
                    ),
                    f"③-terminal {pair_label}",
                )
            sp = simplify(ep.state.evm_stack.SP)
            try:
                depth = sp.as_long()
            except AttributeError:
                return None, (
                    f"exit segment: symbolic stack depth at re-entry "
                    f"{pair_label}"
                )
            # §4.5.6 覆盖点 ⑤：出口段进入下一 cutpoint 时两侧仍在 running。
            # 与再入重建不变式同理——只保持普通 R 而丢掉结构前提，下一轮就在
            # 定理前提不成立的状态上复用定理。
            structural, defect = self._structural_goals(
                ep.state, xp.state, "exit_segment_cutpoint"
            )
            if structural is None:
                return None, defect
            return (
                coupling_conditions(ep.state, xp.state, depth,
                                    cut_mem0=self._cut_mem0,
                                    schema=self.relation_schema)
                + self._domain_goals(ep.state, xp.state)
                + structural
                # **再入必须重建不变式**：出口 suffix 回到循环头时若破坏了 I
                # 而仍保持普通 R，下一轮就会在缺少定理前提 I 的状态上复用定理。
                + self._invariant_goals(ep.state, xp.state),
                f"③-R {pair_label} (depth={depth})",
            )

        failure = self._verify_path_matrix(
            evm_paths, x86_paths, assumptions, _compatible, _goals,
            "③", queries, partition=partition, stats=oog_stats,
        )
        if failure is not None:
            failure.oog_bridge = oog_stats
            return failure

        return LoopInductionResult(
            status="proved", reasons=segment_notes, queries=queries,
            oog_bridge=oog_stats,
            structural_premise_sites=EXIT_STRUCTURAL_SITES,
        )

    # -- bridge site 显式配对校验 -------------------------------------------

    def check_bridge_sites(
        self, x86_body_addrs: Set[int]
    ) -> List[str]:
        """循环体内 host/bridge site 显式配对校验（§7 P2 评审要求）。

        静态扫描 x86 循环体内的 bridge-ret 块（lea rip + ret + 状态码写），
        解析每个站点的 (status, func_index) → 函数名；校验其必须是
        (a) EVM 循环体内出现的 host 操作，或 (b) codegen 内部 builtin
        （memory_grow/stack_grow/gas_cost，EVM 侧无对应操作）。
        任何解析失败或不在允许集内的站点 ⇒ 返回拒绝理由（fail-closed）。
        """
        from x86_64.aot_profile import GO_HPC_EVM_PROFILE

        profile = self.aot_profile or GO_HPC_EVM_PROFILE
        host_status = profile.status_codes["call_go_host_function"]
        builtin_status = profile.status_codes["call_builtin_function"]
        internal_builtins = {"memory_grow", "stack_grow", "gas_cost"}

        evm_body_kinds: Set[str] = set()
        body_pcs = self.evm_body if self.evm_body is not None else {self.evm_header}
        for block in self.evm_blocks:
            if block.pc in body_pcs:
                for op in block.operations:
                    evm_body_kinds.add(op.kind.upper())

        reasons: List[str] = []
        blocks_by_addr = {b.start_addr: b for b in self.x86_blocks}
        for addr in sorted(x86_body_addrs):
            block = blocks_by_addr.get(addr)
            if block is None or not block.instructions:
                continue
            if block.instructions[-1].mnemonic != "ret":
                continue
            if not any(
                insn.mnemonic == "lea" and "rip" in insn.op_str
                for insn in block.instructions
            ):
                continue  # 无返回地址的 ret 是错误 stub，非 bridge
            status = _extract_imm_write(block, "[r13 + 0xe0]")
            if status == host_status:
                func_index = _extract_imm_write(block, "[r13 + 0xe8]")
                name = profile.host_functions.get(func_index)
                if name is None:
                    reasons.append(
                        f"bridge at 0x{addr:x}: unknown host func_index "
                        f"{func_index}"
                    )
                elif name.upper() not in evm_body_kinds:
                    reasons.append(
                        f"bridge at 0x{addr:x}: host '{name}' has no matching "
                        "EVM op in loop body"
                    )
            elif status == builtin_status:
                func_index = _extract_imm_write(block, "[r13 + 0xe4]")
                name = profile.builtin_functions.get(func_index)
                if name is None:
                    reasons.append(
                        f"bridge at 0x{addr:x}: unknown builtin func_index "
                        f"{func_index}"
                    )
                elif (
                    name not in internal_builtins
                    and name.upper() not in evm_body_kinds
                ):
                    reasons.append(
                        f"bridge at 0x{addr:x}: builtin '{name}' has no "
                        "matching EVM op in loop body"
                    )
            else:
                reasons.append(
                    f"bridge at 0x{addr:x}: unexpected status code {status}"
                )
        return reasons
