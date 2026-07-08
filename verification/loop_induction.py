"""P2：Tier 1 锁步关系式归纳引擎（docs/循环处理增强方案.md §4）。

对一对已配对的 (EVM natural loop, x86 natural loop)，在循环头 cutpoint 上
执行归纳步（§4.2 ②）：

- **havoc 构造**：cutpoint 状态用 ``SMTState.create_initial_state(num_inputs=k)``
  构造——两侧共享同一组新鲜栈符号（EVM 栈与 x86 STACK 窗口 by construction
  耦合）、共享 storage/transient/calldata Array、路径条件为空。这正是 §4.3
  的 havoc 纪律：除 R 钉住的状态外一切新鲜。
- **两侧各执行一轮循环体**（有界段执行，cutpoint 截断），按出口分类后：
  (a) 分支决策逐对一致（kind 不兼容的路径对必须不可同时满足）
  (b) 都走回边 ⇒ 回到循环头时 R 保持
  (c) 都走出口 ⇒ 出口处 R 保持
  (d) 体内终止路径 ⇒ 终止可观测量等价（v1：return metadata + storage）

关键语义（§6）：**归纳步 SAT ≠ 找到 bug**。R 太弱时归纳步给伪反例，本引擎
的失败输出只有 ``inconclusive``（→ 管线降级），绝不把 SAT 当反例报告。

v1 范围限定（与文档一致）：
- 可观测面 = 当前 checker 已建模的 8 项（无 status/gas/logs）。
- gas 保持现有全程序抽象（具体大常量 ⇒ TAG OOG 分支静态压死）；含 GAS
  opcode 的循环体直接 inconclusive（具体 gas 值在第 n 轮不成立）。
- 栈深按深度类逐一实例化（k 由调用方给出）。
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
    """归纳查询统一用 QF_AUFBV（对齐 refinement_context 与 div_bridge 先例：
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

@dataclass
class LoopInductionResult:
    """归纳/段查询结果。status ∈ {'proved', 'inconclusive'}——没有 'refuted'。"""

    status: str
    reasons: List[str] = field(default_factory=list)
    queries: List[Tuple[str, str]] = field(default_factory=list)
    # ① Base 查询产出：循环头到达时的绝对栈深类（供 ②③ 按类实例化）
    depth_classes: List[int] = field(default_factory=list)

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


# §4.3 no-OOG/no-stack-limit envelope：这些错误终止路径在 v1 中被显式排除
# （对应 develop 全程序模式用具体大 gas 静态压死的同一抽象，此处显式化）。
_ENVELOPE_EXCLUDED_STATUSES = frozenset({
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
) -> Tuple[List[SegmentPath], List[str], List[str]]:
    """从 cutpoint 执行一轮 x86 段。

    Returns:
        (路径列表, coverage 缺陷, envelope 排除记录)。gas/栈错误终止路径
        按 §4.3 的 no-OOG/no-stack-limit envelope 排除并显式记录——结论
        携带该 envelope 标注，不冒充无条件证明。
    """
    summary_runtime = None
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
    )
    final_states = executor.execute(cut_state, entry_addr=entry_addr)

    defects: List[str] = []
    certificate = executor.path_coverage_certificate()
    if not certificate.complete:
        defects.append(f"x86 segment coverage incomplete: {certificate.reason}")

    excluded_codes = {
        code
        for name, code in executor.aot_profile.status_codes.items()
        if name in _ENVELOPE_EXCLUDED_STATUSES
    }

    paths: List[SegmentPath] = []
    envelope_notes: List[str] = []
    for gstate in executor.cut_states:
        addr = gstate.node.address
        kind = "latch" if addr == entry_addr else "exit"
        paths.append(
            SegmentPath(
                kind=kind,
                location=addr,
                condition=gstate.get_constraints().as_bool(),
                state=gstate.mstate,
            )
        )
    for gstate in final_states:
        block = gstate.node.block if gstate.node else None
        status = executor._extract_status_code(block) if block is not None else None
        if status is not None and status in excluded_codes:
            envelope_notes.append(
                f"x86 terminal path at 0x{gstate.node.address:x} (status={status}) "
                "excluded by no-OOG/no-stack-limit envelope"
            )
            continue
        paths.append(
            SegmentPath(
                kind="terminal",
                location=gstate.node.address if gstate.node else None,
                condition=gstate.get_constraints().as_bool(),
                state=gstate.mstate,
            )
        )
    return paths, defects, envelope_notes


# ---------------------------------------------------------------------------
# R：耦合关系读取器
# ---------------------------------------------------------------------------

def read_x86_stack_slot(state: SMTState, slot_from_top: int):
    """按 §4.1 的映射读取 x86 STACK 窗口中自顶向下第 j 个 slot 的 256-bit 值。

    cutpoint 都在块入口，规范窗口基址 = side-channel 的
    ``stack_base + byte_offset``（[r13+0x38] + [r13+0x30]，executor 全程
    维护），栈顶 slot 在 base - 0x20（负偏移，见 go_function_semantics）。

    注意**不可**混入 ``callengine_stack_pointer_limbs``（[r13+0x28]）：
    那是 host bridge 的传参暂存（如 SLOAD 站点留下的 8），不是窗口状态；
    也不用 R14 寄存器（host 调用后可能是旧值，靠下一块 TAG 序言重算）。
    """
    base = state.callengine_stack_base + state.callengine_stack_byte_offset
    slot_base = base - BitVecVal(
        LIMBS_PER_UINT256 * LIMB_SIZE_BYTES * (slot_from_top + 1), 64
    )
    limbs = []
    for l in range(LIMBS_PER_UINT256):
        addr = slot_base + BitVecVal(l * LIMB_SIZE_BYTES, 64)
        limbs.append(state.x86_memory.load_64bit(addr, domain=MemoryDomain.STACK))
    # z0 是最低有效 limb（little-endian）
    return Concat(limbs[3], limbs[2], limbs[1], limbs[0])


def x86_memory_as_evm_view(x86_state: SMTState):
    """把 x86 evm_mem 转成以 EVM offset 为索引的视图：view[a] = evm_mem[R15+a]。"""
    r15 = x86_state.x86_registers.get_register(Register.R15)
    offset = BitVec("__mem_view_offset", 64)
    return Lambda([offset], Select(x86_state.x86_memory.evm_mem, r15 + offset))


def memory_coupling_condition(
    evm_state: SMTState,
    x86_state: SMTState,
    cut_mem0=None,
):
    """memory 的 R15 平移相等。

    优先把 x86 evm_mem 的 Store 链下推到 offset 空间（消 Lambda，变成
    QF 纯数组等式）；下推失败时回退 Lambda 视图（fail-closed，可能更难
    解但语义相同）。
    """
    if cut_mem0 is not None:
        r15 = x86_state.x86_registers.get_register(Register.R15)
        unshifted = unshift_store_chain(
            x86_state.x86_memory.evm_mem, r15, cut_mem0
        )
        if unshifted is not None:
            return evm_state.evm_memory.Memory == unshifted
    return evm_state.evm_memory.Memory == x86_memory_as_evm_view(x86_state)


def coupling_conditions(
    evm_state: SMTState,
    x86_state: SMTState,
    stack_depth: int,
    include_memory: bool = True,
    cut_mem0=None,
) -> List:
    """R 的可判定合取（v1）：栈窗口逐 slot 相等 + storage/transient 相等
    + memory 的 R15 平移相等。
    """
    conditions = []
    for j in range(stack_depth):
        conditions.append(
            evm_state.evm_stack.peek(j) == read_x86_stack_slot(x86_state, j)
        )
    conditions.append(
        evm_state.evm_storage.Storage == x86_state.evm_storage.Storage
    )
    conditions.append(
        evm_state.evm_transient_storage.TransientStorage
        == x86_state.evm_transient_storage.TransientStorage
    )
    if include_memory:
        conditions.append(
            memory_coupling_condition(evm_state, x86_state, cut_mem0)
        )
    return conditions


def terminal_observable_conditions(
    evm_state: SMTState, x86_state: SMTState, cut_mem0=None
) -> List:
    """②(d) v1 终止可观测量：return metadata + **返回内容** + storage/transient。

    返回内容用整 memory 的 R15 平移相等表达（覆盖 [offset, offset+length)
    的返回区间，强于逐字节区间比较）：两侧从耦合的 mem₀ 出发执行对齐的
    EVM 内存操作，整体相等是自然的终止 R；过强的方向是安全的——只会
    多降级，不会假绿。offset/length 相等蕴含 has_return_data（两侧都由
    length != 0 派生）一致。
    """
    return [
        evm_state.return_offset == x86_state.return_offset,
        evm_state.return_length == x86_state.return_length,
        memory_coupling_condition(evm_state, x86_state, cut_mem0),
        evm_state.evm_storage.Storage == x86_state.evm_storage.Storage,
        evm_state.evm_transient_storage.TransientStorage
        == x86_state.evm_transient_storage.TransientStorage,
    ]


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
    ):
        self.aot_profile = aot_profile
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

        # envelope 错误 stub 不是可配对出口：不进 stop 集，让段执行跑进去
        # 变成 terminal 错误路径，由 run_x86_segment 按 envelope 排除。
        from x86_64.aot_profile import GO_HPC_EVM_PROFILE
        excluded_codes = {
            code
            for name, code in GO_HPC_EVM_PROFILE.status_codes.items()
            if name in _ENVELOPE_EXCLUDED_STATUSES
        }
        blocks_by_addr = {b.start_addr: b for b in self.x86_blocks}
        pairable = []
        for addr in sorted(x86_exits):
            block = blocks_by_addr.get(addr)
            status = x86_error_stub_status(block) if block is not None else None
            if status is not None and status in excluded_codes:
                continue
            pairable.append(addr)
        self.x86_exits = pairable

    # -- cutpoint havoc 状态 ---------------------------------------------

    def build_cut_state(self, byte_offset_value: Optional[int] = None) -> SMTState:
        """构造 havoc 后的 cutpoint 状态（§4.3）。

        - k 个新鲜栈符号同时写入 EVM 栈与 x86 STACK 窗口（同一组符号 ⇒
          R 的栈耦合 by construction）；storage/calldata 等共享 Array 也是
          新鲜符号。
        - **栈基字节偏移 [r13+0x30] 必须符号化**：TAG 序言有栈下溢/超限
          检查（cmp offset, k*0x20 / maxStack），具体 0 会把全部可行路径
          送进 underflow stub、留下带假约束的空洞路径。这是 §4.3
          no-stack-limit envelope 的实现：off ∈ [k*0x20, 0x4000] 且 0x20
          对齐；x86 窗口基址 = stack_base + off（对应 AOT 的
          ``mov r14,[r13+0x38]; add r14,[r13+0x30]`` 重算）。
        - memory 显式 havoc：初始 K(0) 零数组是 entry-specific 的。用新鲜
          数组 mem₀ 作 EVM memory，x86 evm_mem 取其 R15 平移（同一数组 ⇒
          memory 耦合 by construction）。
        - gas 保持具体大常量（v1 观测面不含 gas；循环体含 GAS/MSIZE 已被
          结构预检拒绝）。
        """
        from common.uint256 import Uint256
        from state.x86_state import MemoryDomain as _MD
        from verification.memory_mapping import StackMemoryMapper
        from x86_64.aot_profile import GO_HPC_EVM_PROFILE
        from z3 import ULE

        state = SMTState.create_initial_state(num_inputs=0)
        r13 = state.x86_registers.get_register(Register.R13)
        offsets = GO_HPC_EVM_PROFILE.offsets

        # 栈基字节偏移：全深度类模式（byte_offset_value 给定，= k*0x20，
        # 由 ① Base 查询确定的具体深度类）用具体值——TAG 栈检查静态解析，
        # 公式显著变简单；窗口模式退回符号 off + no-stack-limit envelope。
        if byte_offset_value is not None:
            off = BitVecVal(byte_offset_value, 64)
        else:
            off = BitVec("cut_stack_byte_offset", 64)
            state.add_assumption(
                ULE(BitVecVal(0x20 * max(self.stack_depth, 1), 64), off)
            )
            state.add_assumption(ULE(off, BitVecVal(0x4000, 64)))
            state.add_assumption(off & BitVecVal(0x1F, 64) == BitVecVal(0, 64))
        state.callengine_stack_byte_offset = off
        state.x86_memory = state.x86_memory.store_limb(
            r13 + BitVecVal(offsets["stack_byte_offset"], 64),
            off,
            domain=_MD.CALLENGINE,
        )

        # memory size / memory gas havoc：具体 0 是 entry-specific 的
        # （第 n 轮到达时内存已增长）。两侧共用同一 size 符号（耦合 by
        # construction）；上界是 no-OOG envelope 的一部分（4MB 时扩展
        # gas 已远超 10^9，真实执行必 OOG——被 envelope 排除）。
        # mem_gas 独立 havoc 是过近似，方向安全（只多降级）。
        mem_size = BitVec("cut_mem_size_bytes", 64)
        state.add_assumption(ULE(mem_size, BitVecVal(0x400000, 64)))
        state.add_assumption(
            mem_size & BitVecVal(0x1F, 64) == BitVecVal(0, 64)
        )
        mem_gas = BitVec("cut_mem_gas_used", 64)
        state.add_assumption(ULE(mem_gas, BitVecVal(1 << 40, 64)))
        state.callengine_memory_size_bytes = mem_size
        state.callengine_memory_gas_used = mem_gas
        state.evm_memory.MSize = mem_size
        state.x86_memory = state.x86_memory.store_limb(
            r13 + BitVecVal(offsets["memory_size"], 64),
            mem_size,
            domain=_MD.CALLENGINE,
        )
        state.x86_memory = state.x86_memory.store_limb(
            r13 + BitVecVal(offsets["last_gas_cost"], 64),
            mem_gas,
            domain=_MD.CALLENGINE,
        )

        # 窗口基址 = stack_base + off；k 个共享栈符号写入两侧
        window_base = state.callengine_stack_base + off
        values = [
            Uint256.symbolic(f"cut_stack_{i}").to_bv256()
            for i in range(self.stack_depth)
        ]
        for value in values:
            state.evm_stack = state.evm_stack.push(value)
        state.x86_memory = StackMemoryMapper.initialize_x86_memory_from_stack(
            state.x86_memory, values, base=window_base
        )

        state.x86_registers.set_register(Register.R14, window_base)
        state.x86_registers.set_register(Register.R15, state.callengine_memory_base)

        # memory havoc + R15 平移耦合
        mem0 = Array("cut_evm_mem0", BitVecSort(64), BitVecSort(8))
        state.evm_memory.Memory = mem0
        r15 = state.callengine_memory_base
        addr = BitVec("__cut_mem_addr", 64)
        state.x86_memory.evm_mem = Lambda([addr], Select(mem0, addr - r15))
        # 供 R 目标构造做 unshift（Store 链下推消 Lambda）
        self._cut_mem0 = mem0
        return state

    # -- 结构预检 ---------------------------------------------------------

    def _structural_rejections(self) -> List[str]:
        reasons = []
        if len(self.evm_exits) != len(self.x86_exits):
            reasons.append(
                f"exit count mismatch: EVM {self.evm_exits} vs x86 "
                f"{[hex(a) for a in self.x86_exits]}"
            )
        # 含 GAS/MSIZE opcode 的**循环体**：具体 gas / havoc msize 抽象在
        # 第 n 轮不成立。只扫循环体块（body 未知时退化为只扫 header 块）。
        header_block = next(
            (b for b in self.evm_blocks if b.pc == self.evm_header), None
        )
        if header_block is None:
            reasons.append(f"EVM header block pc={self.evm_header} not found")
        body_pcs = self.evm_body if self.evm_body is not None else {self.evm_header}
        for block in self.evm_blocks:
            if block.pc not in body_pcs:
                continue
            for op in block.operations:
                if op.kind.upper() in ("GAS", "MSIZE"):
                    reasons.append(
                        f"loop body contains {op.kind.upper()} opcode at pc={op.pc}; "
                        "cutpoint abstraction unsound for induction"
                    )
                    break
        return reasons

    # -- 求解 --------------------------------------------------------------

    def _check_unsat(self, label, formula_terms, timeout_ms, queries) -> bool:
        solver = _make_solver(timeout_ms)
        solver.add(And(BoolVal(True), *formula_terms))
        started = time.time()
        result = solver.check()
        queries.append((label, f"{result} ({time.time() - started:.2f}s)"))
        return result == unsat

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
            budget = self.timeout_ms if is_full else slice_budget
            if self._check_unsat(
                f"{solver_label} [{tag}]",
                base_terms + e_slice + x_slice + [negated_goal],
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

    def _query_sat(self, solver_label: str, condition, queries):
        solver = _make_solver(self.timeout_ms)
        solver.add(condition)
        started = time.time()
        result = solver.check()
        queries.append((solver_label, f"{result} ({time.time() - started:.2f}s)"))
        return result

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
    ) -> Optional[LoopInductionResult]:
        """公共配对矩阵验证：可行性预过滤 → 决策对齐/joint-sat → 证明义务
        → 空洞守卫。全部通过返回 None，否则返回 inconclusive 结果。

        Args:
            compatible_fn(ep, xp) -> bool：两条路径是否是"应当共现"的组合。
            goals_fn(ep, xp, pair_label) -> (goal 条件列表, 查询标签)；
                返回 (None, reason) 表示该对无法构造证明义务 ⇒ inconclusive。
            alignment_tag：失配查询的标签前缀（②(a) / ①-align / ③-align）。
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

        evm_partner_count = [0] * len(evm_paths)
        x86_partner_count = [0] * len(x86_paths)

        for i, ep in enumerate(evm_paths):
            for j, xp in enumerate(x86_paths):
                pair_label = f"evm#{i}({ep.kind})/x86#{j}({xp.kind})"
                joint = And(base, ep.condition, xp.condition)

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

    def check_inductive_step(self) -> LoopInductionResult:
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
        x86_paths, x86_defects, envelope_notes = run_x86_segment(
            self.x86_blocks, cut_state.copy(), self.x86_header, x86_stops,
            max_depth=self.max_depth,
            aot_profile=self.aot_profile,
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
        if self.extra_invariant is not None:
            # 归纳前提：不变式在 cutpoint 上成立（两侧共享同一状态视图）
            assumptions.extend(self.extra_invariant(cut_state, cut_state))

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
                        ep.state, xp.state, cut_mem0=self._cut_mem0
                    ),
                    f"②(d) terminal {pair_label}",
                )
            # ②(b)/(c)：回边/出口处 R 保持
            goals = coupling_conditions(
                ep.state, xp.state, self.stack_depth, cut_mem0=self._cut_mem0
            )
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
            "②(a)", queries,
        )
        if failure is not None:
            return failure

        # envelope 排除必须随结论显式携带（§4.3：显式化的抽象，不是无条件证明）
        return LoopInductionResult(
            status="proved", reasons=envelope_notes, queries=queries
        )

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
        x86_paths, x86_defects, envelope_notes = run_x86_segment(
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
        envelope_notes = list(envelope_notes) + [
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
            return (
                coupling_conditions(ep.state, xp.state, depth, cut_mem0=base_mem0),
                f"①-R base {pair_label} (depth={depth})",
            )

        failure = self._verify_path_matrix(
            evm_arrivals, x86_arrivals, assumptions, _compatible, _goals,
            "①", queries,
        )
        if failure is not None:
            return failure

        return LoopInductionResult(
            status="proved",
            reasons=envelope_notes,
            queries=queries,
            depth_classes=sorted(depth_classes),
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
        x86_paths, x86_defects, envelope_notes = run_x86_segment(
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

        assumptions = list(getattr(cut_state, "assumptions", None) or [])

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
                        ep.state, xp.state, cut_mem0=self._cut_mem0
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
            return (
                coupling_conditions(ep.state, xp.state, depth,
                                    cut_mem0=self._cut_mem0),
                f"③-R {pair_label} (depth={depth})",
            )

        failure = self._verify_path_matrix(
            evm_paths, x86_paths, assumptions, _compatible, _goals,
            "③", queries,
        )
        if failure is not None:
            return failure

        return LoopInductionResult(
            status="proved", reasons=envelope_notes, queries=queries
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
