"""循环折叠编排(docs/循环处理增强方案.md §4.7 折叠形态 / §6 管线第 2–3 步)。

把三件已有的部件串成一条链:

    §6 结构守卫(loop_pairing)
        → Tier-1 证书(loop_certificate_prover)
            → 主执行的 stop 集合 + 覆盖核对

**为什么折叠不需要"从出口继续执行"。** 直觉上折叠像是"跳过循环、从出口接着跑",
但证书的 ③ 出口查询是从 **havoc 状态**出发的:它证明的是「对任意满足 R 的出口状态,
后缀 observable 等价」。实际到达出口的状态是"任意满足 R 的状态"的一个特例,因此
后缀义务**已经**被 ③ 履行完了。主验证器要做的只是:

    1. 把配对的循环头设成 stop,让主执行在那里截断;
    2. 核对每个截断态确实落在某张有效证书的适用域内;
    3. 其余(不经过循环的)terminal path 照常做 observable 等价检查。

反过来说,如果让主执行**真的**从出口继续跑,那是在重复 ③ 已经做过的事,而且会
用一个具体状态去替代 ③ 量化过的任意状态——不健全性问题,但纯属浪费。

**为什么单独成模块。** 折叠的正确性依赖一串彼此独立的前置条件(守卫通过、配对成立、
每个深度类都有证书、截断态落在适用域内),这些条件的**组合逻辑**本身就该被单独测试;
塞进 program_verifier 会和 gas 配置校验、路径枚举、observable 检查搅在一起。
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from typing import Dict, FrozenSet, List, Optional, Sequence, Tuple

from evm_ir.models import EVMBlock
from state.smt_state import SMTState
from verification.cutpoint_relation import STACK_ELEMENT_SIZE
from verification.loop_certificate_prover import (
    LoopProofOutcome,
    prove_loop_certificate,
)
from verification.loop_pairing import LoopGuardReport, analyze_program_pair, build_evm_cfg
from x86_64.aot_profile import AOT_COMPILER_PROFILE
from x86_64.loop_analysis import NaturalLoop, build_x86_cfg
from x86_64.models import X86Block


def loop_exit_targets(
    loop: NaturalLoop, succs: Dict[int, Sequence[int]]
) -> Tuple[int, ...]:
    """循环体的出口目标集合:body 内节点指向 body 外的边。

    注意这里给的是**出口目标**(循环外的第一个节点),不是"出口边的源"。
    ②(c)/③ 都以目标为段起点,两者不能混——用源块会让 ③ 从循环体内部起跑,
    把最后一轮的尾巴重复计入后缀。
    """
    out = set()
    for node in loop.body:
        for target in succs.get(node, ()):
            if target not in loop.body:
                out.add(target)
    return tuple(sorted(out))


# ---------------------------------------------------------------------------
# Tier-1 配对的结构指纹(§4.7 证书的"EVM/x86 循环头与结构指纹"一项)
#
# **为什么需要它。** 配对本身是顺序的:`loop_pairing.pair_natural_loops` 把两侧
# natural loop 按 header 排序后逐位比对 latch 数,因此**同 latch 数的错误置换可以
# 直接进入 pairs**(§6)。文档给这条顺序假设的 fail-safe 论证是"错配的证书永远不
# 会被消费",但那只在消费端逐点核对时成立,而且置换后的两张证书仍会各花分钟级
# Z3 去证。指纹核对是这条顺序假设的**独立交叉验证**,在证明之前就把置换挡掉。
#
# **指纹来自哪里。** x86 循环头的 TAG 序言里刻着它所编译的那个 EVM 块的两个字段
# (`impl_amd64.go: compileEVMTag` → `gas_dynamic_amd64.go: makeStaticUseGas`):
#
#     mov tmp, [r13+gas_remaining]  ; cmp tmp, StaticGas     ; jb OOG        ← 循环头块
#     sub tmp, StaticGas            ; mov [r13+gas_remaining], tmp
#     mov tmp, [r13+stack_byte_off] ; cmp tmp, MinDepth*0x20 ; jb underflow  ← 落空块
#
# 两个立即数就是 `EVMBlock.static_gas` 与 `EVMBlock.min_depth` 的 codegen 面镜像。
# 实测三份真实合约的 19 对配对逐个吻合(CErc20 9 / Safe 4 / Permit2 6),且每份合约
# 内 (static_gas, min_depth, latch 数) 三元组两两不同 ⇒ 任何置换都会被抓住。
#
# **取不出指纹一律拒绝。** "认不出就放行"会让这条核对在 codegen 变形后静默失效,
# 而它是配对唯一的独立交叉验证——静默失效等于把顺序假设重新变成无人看守的前提。
# ---------------------------------------------------------------------------

_GAS_LOAD_RE = re.compile(
    r"^(\w+),\s*qword ptr \[r13 \+ 0x%x\]$"
    % AOT_COMPILER_PROFILE.offsets["gas_remaining"]
)
_STACK_BYTES_LOAD_RE = re.compile(
    r"^(\w+),\s*qword ptr \[r13 \+ 0x%x\]$"
    % AOT_COMPILER_PROFILE.offsets["stack_byte_offset"]
)
_REG_IMM_RE = re.compile(r"^(\w+),\s*(0x[0-9a-fA-F]+|\d+)$")
_TAG_OOG_JUMPS = frozenset({"jb", "jc"})


def _meaningful(block: Optional[X86Block]) -> List:
    """块内的有效指令:对齐填充的 nop 不算(codegen 会在序言中间插对齐 nop)。"""
    if block is None:
        return []
    return [insn for insn in block.instructions if insn.mnemonic != "nop"]


def _cmp_immediate_after_load(insns: Sequence, load_re: re.Pattern) -> Optional[int]:
    """找 ``mov REG, qword ptr [r13+off]`` 紧跟的 ``cmp REG, IMM``,取该立即数。

    要求"紧跟"而不是"后面某处":codegen 就是这么连着发的,放宽成模糊搜索会让
    别处一条无关的 ``cmp`` 冒充指纹。
    """
    for idx, insn in enumerate(insns):
        if insn.mnemonic != "mov":
            continue
        load = load_re.match(insn.op_str.strip())
        if load is None or idx + 1 >= len(insns):
            continue
        follow = insns[idx + 1]
        if follow.mnemonic != "cmp":
            continue
        matched = _REG_IMM_RE.match(follow.op_str.strip())
        if matched is not None and matched.group(1) == load.group(1):
            return int(matched.group(2), 0)
    return None


def x86_tag_prologue_fingerprint(
    header_block: Optional[X86Block],
    fallthrough_block: Optional[X86Block],
) -> Optional[Tuple[int, int]]:
    """从 TAG 序言取出 ``(static_gas, min_depth_bytes)``;形态不符返回 None。

    ``fallthrough_block`` 是循环头块**按地址紧邻的下一块**,即 TAG 序言里
    OOG 分支 ``jb`` 的落空目标——栈下溢检查在那里,``min_depth`` 也就刻在那里。
    """
    header = _meaningful(header_block)
    if len(header) < 3 or header[2].mnemonic not in _TAG_OOG_JUMPS:
        return None
    static_gas = _cmp_immediate_after_load(header[:2], _GAS_LOAD_RE)
    if static_gas is None:
        return None
    min_depth_bytes = _cmp_immediate_after_load(
        _meaningful(fallthrough_block), _STACK_BYTES_LOAD_RE
    )
    if min_depth_bytes is None:
        return None
    return static_gas, min_depth_bytes


def pair_fingerprint_defect(
    evm_block: Optional[EVMBlock],
    x86_header_block: Optional[X86Block],
    x86_fallthrough_block: Optional[X86Block],
) -> Optional[str]:
    """核对一对循环头的结构指纹;一致返回 None,否则返回拒绝理由。

    Returns:
        None 表示 x86 循环头的 TAG 序言确实是这个 EVM 块编译出来的;否则是
        一句可直接进 ``FoldingPlan.reasons`` 的理由。**取不出指纹也返回理由**
        (fail-closed)。
    """
    if evm_block is None:
        return "EVM loop header is not in the block table (cannot fingerprint the pair)"
    if x86_header_block is None:
        return "x86 loop header is not in the block table (cannot fingerprint the pair)"

    fingerprint = x86_tag_prologue_fingerprint(x86_header_block, x86_fallthrough_block)
    if fingerprint is None:
        return (
            f"x86 header 0x{x86_header_block.start_addr:x} has no readable TAG "
            "prologue (static-gas / min-depth immediates), so the pairing cannot "
            "be cross-checked"
        )

    static_gas, min_depth_bytes = fingerprint
    expected_depth_bytes = evm_block.min_depth * STACK_ELEMENT_SIZE
    if static_gas != evm_block.static_gas or min_depth_bytes != expected_depth_bytes:
        # 顺序配对允许同 latch 数置换,这里就是它的兜底(§6)。
        return (
            f"TAG prologue of x86 header 0x{x86_header_block.start_addr:x} "
            f"encodes static_gas={static_gas}, min_depth={min_depth_bytes // STACK_ELEMENT_SIZE} "
            f"but EVM header pc=0x{evm_block.pc:x} has static_gas="
            f"{evm_block.static_gas}, min_depth={evm_block.min_depth}: "
            "the two loop headers are not a compiled pair"
        )
    return None


@dataclass(frozen=True)
class FoldedLoop:
    """一个已被证书覆盖的配对循环头。"""

    evm_header: int
    x86_header: int
    evm_exits: Tuple[int, ...]
    x86_exits: Tuple[int, ...]
    outcome: LoopProofOutcome

    @property
    def proved(self) -> bool:
        return self.outcome.proved

    @property
    def depth_classes(self) -> Tuple[int, ...]:
        return tuple(self.outcome.depth_classes)

    def describe(self) -> str:
        return (
            f"loop evm=0x{self.evm_header:x} / x86=0x{self.x86_header:x} "
            f"depth_classes={list(self.depth_classes)}"
        )


@dataclass
class FoldingPlan:
    """折叠计划:哪些 cutpoint 已被证书覆盖、主执行该在哪里截断。

    `reasons` 非空即**整体不可折叠**——没有"折叠了一部分也算数"这回事:
    未折叠的循环头不会进 stop 集合,主执行会照常展开它,符号 bound 循环于是
    在 depth-pruning 处 fail-closed。调用方可以选择降级到不折叠的老路径,
    但不能把部分折叠当成完整折叠。
    """

    folded: Tuple[FoldedLoop, ...] = ()
    reasons: Tuple[str, ...] = ()
    guard_report: Optional[LoopGuardReport] = None
    notes: Tuple[str, ...] = ()

    @property
    def ok(self) -> bool:
        """没有失败原因。**无循环的程序也是 ok 的**(folded 为空但计划成立)。"""
        return not self.reasons

    @property
    def evm_stop_pcs(self) -> FrozenSet[int]:
        return frozenset(f.evm_header for f in self.folded)

    @property
    def x86_stop_addrs(self) -> FrozenSet[int]:
        return frozenset(f.x86_header for f in self.folded)

    def by_evm_header(self) -> Dict[int, FoldedLoop]:
        return {f.evm_header: f for f in self.folded}

    def by_x86_header(self) -> Dict[int, FoldedLoop]:
        return {f.x86_header: f for f in self.folded}

    def describe(self) -> List[str]:
        lines = [f"loop folding: {len(self.folded)} cutpoint(s) covered by certificates"]
        lines.extend(f"  folded: {f.describe()}" for f in self.folded)
        lines.extend(f"  note: {note}" for note in self.notes)
        lines.extend(f"  blocked: {reason}" for reason in self.reasons)
        return lines


def plan_loop_folding(
    evm_blocks: Sequence[EVMBlock],
    x86_blocks: Sequence[X86Block],
    initial_state: SMTState,
    *,
    evm_entry_pc: Optional[int] = None,
    x86_entry_addr: Optional[int] = None,
    tier2_matcher=None,
    guard_report: Optional[LoopGuardReport] = None,
    summary_config=None,
    aot_profile=None,
    relation_schema=None,
    cache=None,
    timeout_ms: int = 30000,
    max_depth: int = 400,
    require_termination: bool = True,
    compare_terminal_gas: bool = False,
    host_gas_uf_enabled: bool = False,
) -> FoldingPlan:
    """跑守卫 → 逐个配对循环生成证书 → 产出折叠计划(§6 管线第 0–2 步)。

    Args:
        guard_report: 调用方**已经跑过**的 §6 守卫报告。给了就不重跑——
            `program_verifier` 把 `tier2_matcher` 的传法收敛在单一入口
            (`_analyze_loop_guard`),这里再造一个构造点就会出现"附注说没问题、
            守卫说有问题"的错位。不给则本函数用 `tier2_matcher` 自行分析。
        require_termination: 透传给证书。**默认 True**:折叠意味着主证明不再
            展开该循环,若不要求终止证据,得到的是"两侧锁步同步"而非"循环会
            结束"——把前者当后者用,不终止的循环会被判等价。
        compare_terminal_gas / host_gas_uf_enabled: 必须与调用方的 `GasCheck`
            档位一致,否则定理在另一套 gas 语义下证出(§4.5.2)。

    Returns:
        :class:`FoldingPlan`。`ok` 为假时 `reasons` 说明卡在哪一步。
        **任何一步失败都不折叠**,而不是折叠成功的那部分。
    """
    reasons: List[str] = []
    notes: List[str] = []

    if not evm_blocks or not x86_blocks:
        return FoldingPlan(reasons=("empty program: nothing to fold",))

    # --- 第 0 步:结构守卫 ---------------------------------------------------
    # 必须在路径枚举之前:它的输出决定哪些循环头是 cutpoint。
    report = guard_report
    if report is None:
        report = analyze_program_pair(
            list(evm_blocks), list(x86_blocks), tier2_matcher=tier2_matcher
        )
    notes.extend(report.notes())
    if not report.ok:
        # fail-closed:守卫不过就不折叠。unpaired 循环意味着有回边既没有 Tier-1
        # 配对也没命中 Tier-2 引理,此时折叠等于对没验过的循环签发通行证。
        return FoldingPlan(
            reasons=tuple(f"guard: {r}" for r in report.reasons()),
            guard_report=report,
            notes=tuple(notes),
        )

    if not report.pairs:
        # 无 Tier-1 循环。这是**成功**的计划:没有需要折叠的东西,主执行照常跑。
        return FoldingPlan(guard_report=report, notes=tuple(notes))

    # --- 第 2 步:逐个配对循环生成证书 --------------------------------------
    evm_succs, _ = build_evm_cfg(list(evm_blocks))
    x86_succs, _ = build_x86_cfg(list(x86_blocks))

    if evm_entry_pc is None:
        evm_entry_pc = evm_blocks[0].pc
    if x86_entry_addr is None:
        x86_entry_addr = min(b.start_addr for b in x86_blocks)

    evm_by_pc = {block.pc: block for block in evm_blocks}
    x86_by_addr = {block.start_addr: block for block in x86_blocks}
    x86_addrs = sorted(x86_by_addr)

    def _fallthrough(addr: int) -> Optional[X86Block]:
        """TAG 序言 ``jb`` 的落空块 = 按地址紧邻的下一块(序言是直线发射的)。"""
        index = x86_addrs.index(addr) if addr in x86_by_addr else -1
        if index < 0 or index + 1 >= len(x86_addrs):
            return None
        return x86_by_addr[x86_addrs[index + 1]]

    folded: List[FoldedLoop] = []
    for evm_loop, x86_loop in report.pairs:
        # 先核对结构指纹:顺序配对允许同 latch 数置换,配错的一对不值得再花
        # 分钟级 Z3 去证(而且证出来的定理讲的是另一对程序点的事)。
        defect = pair_fingerprint_defect(
            evm_by_pc.get(evm_loop.header),
            x86_by_addr.get(x86_loop.header),
            _fallthrough(x86_loop.header),
        )
        if defect is not None:
            reasons.append(f"loop evm=0x{evm_loop.header:x}: {defect}")
            continue

        evm_exits = loop_exit_targets(evm_loop, evm_succs)
        x86_exits = loop_exit_targets(x86_loop, x86_succs)
        if not evm_exits or not x86_exits:
            # 无出口的循环:要么是无限循环,要么是 CFG 构建漏了边。两种都不该
            # 静默折叠——前者的"等价"没有意义,后者是分析缺陷。
            reasons.append(
                f"loop evm=0x{evm_loop.header:x}: no exit target on "
                f"{'EVM' if not evm_exits else 'x86'} side"
            )
            continue

        outcome = prove_loop_certificate(
            evm_blocks=list(evm_blocks),
            x86_blocks=list(x86_blocks),
            evm_header=evm_loop.header,
            x86_header=x86_loop.header,
            evm_exits=evm_exits,
            x86_exits=x86_exits,
            initial_state=initial_state,
            evm_entry_pc=evm_entry_pc,
            x86_entry_addr=x86_entry_addr,
            relation_schema=relation_schema,
            cache=cache,
            summary_config=summary_config,
            aot_profile=aot_profile,
            timeout_ms=timeout_ms,
            max_depth=max_depth,
            evm_body=frozenset(evm_loop.body),
            require_termination=require_termination,
            compare_terminal_gas=compare_terminal_gas,
            host_gas_uf_enabled=host_gas_uf_enabled,
        )
        entry = FoldedLoop(
            evm_header=evm_loop.header,
            x86_header=x86_loop.header,
            evm_exits=evm_exits,
            x86_exits=x86_exits,
            outcome=outcome,
        )
        if not outcome.proved:
            reasons.extend(
                f"loop evm=0x{evm_loop.header:x}: {r}"
                for r in (outcome.unmet_obligations or ("certificate inconclusive",))
            )
            continue
        folded.append(entry)

    if reasons:
        # 有循环没拿到证书 ⇒ 整体不折叠(见 FoldingPlan 的类注释)。
        return FoldingPlan(
            reasons=tuple(reasons), guard_report=report, notes=tuple(notes)
        )
    return FoldingPlan(
        folded=tuple(folded), guard_report=report, notes=tuple(notes)
    )


@dataclass
class CutCoverageResult:
    """主执行截断态的覆盖核对结果。"""

    covered: int = 0
    reasons: Tuple[str, ...] = ()

    @property
    def ok(self) -> bool:
        return not self.reasons


def verify_cut_coverage(
    plan: FoldingPlan,
    *,
    evm_cut_depths: Sequence[Tuple[int, Optional[int]]],
    x86_cut_headers: Sequence[int],
) -> CutCoverageResult:
    """核对主执行在 cutpoint 处的截断态确实落在证书适用域内(§4.7 消费四步)。

    这一步**不能**省成"到达了 cutpoint 就算被覆盖"。证书是按深度类实例化的
    (`build_havoc(stack_depth)` 收具体整数),落在未登记深度类上的到达状态
    根本不在任何定理的适用域内。

    程序点核对是**成对**的(§4.7 消费第 1 步:"EVM pc 与 x86 addr 必须同时匹配
    证书记录的那一对")。证书是关系式定理,它的前提是"两侧同时站在这一对程序点
    上";只核对"这个 pc 有证书"和"这个 addr 有证书"两件独立的事,等于把一对
    程序点拆成两个单侧断言——错配的计划正好能钻这个空子(见下面的到达对称性)。

    Args:
        evm_cut_depths: 主执行 EVM 侧的截断态,每项是 `(header_pc, 绝对栈深)`。
            栈深为 None 表示取不出具体值(符号栈深)——**必须拒绝**,而不是
            当作"某个已登记的类"放行。
        x86_cut_headers: 主执行 x86 侧截断态所在的地址。

    Returns:
        :class:`CutCoverageResult`;`reasons` 非空即覆盖不完整,调用方必须
        fail-closed,不得把未覆盖的截断态当成"已由证书处理"。

    **本函数依赖的前提**(调用方必须保证,否则核对是空的):主执行与证书 ①
    Base 用的是**同一个入口与同一套配置**(max_depth / summary_config /
    GasCheck 档位 / calldata 语义开关)。Base 对所有到达路径证明了 R,主执行
    的截断态才因此落在已证集合内;配置不同则路径集不同,Base 的结论不适用。
    这个一致性由证书指纹在 `plan_loop_folding` 处保证,不在这里重复检查。

    **本函数够不到的一格**:两侧截断态是各自的**集合**,没有"哪条 EVM 路径与
    哪条 x86 路径是同一次执行"的对应关系。因此若两个循环在两侧都被截断(并列
    分支各一个),把它们对调后集合完全不变,这里分辨不出。那一格由
    `plan_loop_folding` 的 TAG 序言指纹核对挡住;要在**这里**分辨,得让调用方
    把截断态按 path pair 传进来。
    """
    by_evm = plan.by_evm_header()
    by_x86 = plan.by_x86_header()
    reasons: List[str] = []
    covered = 0

    # 计划必须是循环头之间的**双射**。两条证书共用一个 header 时上面两张表会
    # 静默丢掉一条,后面的核对就只覆盖了一半却照样报 ok——fail-open 方向。
    if len(by_evm) != len(plan.folded) or len(by_x86) != len(plan.folded):
        reasons.append(
            "folding plan is not a one-to-one map between loop headers: "
            f"{len(plan.folded)} certificate(s) but {len(by_evm)} EVM / "
            f"{len(by_x86)} x86 distinct header(s)"
        )

    # §4.7 消费第 1 步:证书记的是**一对**程序点,主执行必须两侧同时到达它、
    # 或两侧都不到达。只有一侧到达,说明这一侧折叠掉的循环在另一侧没有对应的
    # 截断——证书"两侧都站在这对 cutpoint 上"的前提没有兑现,定理不适用。
    # 一侧没到达也不能当"这条证书没用上就算了":另一侧确实在这里停了,那条
    # 路径的后缀既没被展开也没被任何已消费的证书覆盖。
    reached_evm = {header for header, _ in evm_cut_depths}
    reached_x86 = set(x86_cut_headers)
    for entry in plan.folded:
        evm_hit = entry.evm_header in reached_evm
        x86_hit = entry.x86_header in reached_x86
        if evm_hit != x86_hit:
            stopped, missing = (
                ("EVM", "x86") if evm_hit else ("x86", "EVM")
            )
            reasons.append(
                f"certificate for the pair (EVM pc=0x{entry.evm_header:x}, "
                f"x86 0x{entry.x86_header:x}) was reached on the {stopped} side "
                f"only: the {missing} side never stopped at its half of the pair, "
                "so the two cut states are not the paired cutpoint the "
                "certificate is about"
            )

    for header, depth in evm_cut_depths:
        entry = by_evm.get(header)
        if entry is None:
            reasons.append(
                f"EVM execution stopped at pc=0x{header:x}, which has no "
                "certificate in this folding plan"
            )
            continue
        if depth is None:
            reasons.append(
                f"EVM cut state at pc=0x{header:x} has a symbolic stack depth; "
                "certificates are instantiated per concrete depth class"
            )
            continue
        if depth not in entry.depth_classes:
            reasons.append(
                f"EVM cut state at pc=0x{header:x} has depth {depth}, outside "
                f"the certified classes {list(entry.depth_classes)}"
            )
            continue
        covered += 1

    for addr in x86_cut_headers:
        if addr not in by_x86:
            reasons.append(
                f"x86 execution stopped at 0x{addr:x}, which has no certificate "
                "in this folding plan"
            )

    return CutCoverageResult(covered=covered, reasons=tuple(reasons))


__all__ = [
    "CutCoverageResult",
    "FoldedLoop",
    "FoldingPlan",
    "loop_exit_targets",
    "pair_fingerprint_defect",
    "plan_loop_folding",
    "verify_cut_coverage",
    "x86_tag_prologue_fingerprint",
]
