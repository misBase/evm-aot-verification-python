"""P3(ii)：Tier 2 codegen 拷贝循环的模板引理离线证明（docs/循环处理增强方案.md §5）。

`impl_amd64.go` 共 7 条 runtime 回边，坍缩为 6 种指令形态（byte-tail 在
FromLow/FromHigh 各出现一次，形态与寄存器分配完全相同）：

======================  =============================  =======================
模板名                   来源(impl_amd64.go)             真实实例（证明锚点）
======================  =============================  =======================
returndata-byte-copy    compileEVMRETURNDATACOPY loop   CErc20 0x1590f（34 处）
makedata-byte-copy      compileMakeDataCopy beginLoop   CALLDATACOPY core 0x41
mcopy-low-word          MCOPYFromLow loopStart          CErc20 0xad2ac
mcopy-high-word         MCOPYFromHigh loopStart         CErc20 0xad254
mcopy-byte-tail         FromLow/FromHigh loopStart2     CErc20 0xad2cf/0xad294
mcopy-shr-align         MCOPYFromHigh SHRStart          CErc20 0xad284
======================  =============================  =======================

证明方法（每条引理一次性离线证明，绑定编译器版本）：

- **快照相对 Inv**（§5.1）：cutpoint 内存 = ``Lambda(a, F(i)[a])`` by
  construction（同 loop_induction.build_cut_state 范式），F(i) 为已拷贝
  区间的闭式覆盖。
- **逐点 witness 目标**（§5.2 变体）：数组等式目标改为在新鲜符号地址 w
  上逐点证明 ``mem'[r15+w] == F(i+1)[w]``——w 任意即全称，全程 QF、无
  Lambda 等式、无量词。
- **生产语义**：一轮循环体经 ``X86SymbolicExecutor`` 在**真实 fixture
  字节**上符号执行（不是手工转写），信任链与全程序验证同源。
- ①(Base)：Inv(0) 平凡（F(0)=mem₀）；②(归纳步)：latch 路径上 Inv 保持；
  ③(出口)：exit 路径上出口关系成立。FromLow/FromHigh 的多段复合由
  glue 段实跑 + 纯 Z3 复合恒等式（tail 满覆盖 == MCOPY 闭式）完成，
  整体定理按 §5.3 的分段归纳组装（元级论证，各片段均为 Z3 引理）。

引理携带的显式前提（应用侧必须核对/由 envelope 承担）：
- 区间不回绕（dst/src/size 的 no-wrap，来自 memory-grow 边界检查）；
- size < 2^63（signed jl/jle 判定与 unsigned 语义一致的范围）；
- FromLow 要求 dst ≤ src、FromHigh 要求 src < dst（构造分派分支自身保证）。

失败语义：任何查询非 unsat ⇒ 该引理不进 PROVEN_TIER2_LEMMAS（fail-closed），
§6 守卫拒绝对应回边。
"""

import time
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Sequence, Tuple

from z3 import (
    And,
    Array,
    BitVec,
    BitVecSort,
    BitVecVal,
    BoolVal,
    Extract,
    If,
    Lambda,
    LShR,
    Not,
    Or,
    Select,
    SolverFor,
    ULE,
    ULT,
    simplify,
    unsat,
)

from common.store_forwarding import forward_selects
from state.smt_state import SMTState
from state.x86_state import PointerTag
from x86_64.models import Register, X86Block

BV64 = BitVecSort(64)
BV8 = BitVecSort(8)


# 模板规格与逐指令精确匹配器（与 §6 守卫共用）住在 x86_64/loop_templates.py；
# 引理证明在规格的真实实例字节上完成，匹配命中即引理适用。
from x86_64.loop_templates import (  # noqa: F401  (re-export 供测试使用)
    TEMPLATES,
    LoopTemplate,
    match_body_blocks_exact,
    match_template_exact,
)


# ---------------------------------------------------------------------------
# 引理证明引擎
# ---------------------------------------------------------------------------

@dataclass
class LemmaResult:
    name: str
    proved: bool
    reasons: List[str] = field(default_factory=list)
    queries: List[Tuple[str, str]] = field(default_factory=list)


def _make_solver(timeout_ms: int):
    solver = SolverFor("QF_AUFBV")
    solver.set("timeout", timeout_ms)
    return solver


class _ProofContext:
    """一条引理的证明上下文：premises 累积 + unsat 查询记录。"""

    def __init__(self, name: str, timeout_ms: int = 60000):
        self.name = name
        self.timeout_ms = timeout_ms
        self.queries: List[Tuple[str, str]] = []
        self.failures: List[str] = []

    def prove(self, label: str, premises: Sequence, goal) -> bool:
        """证明 premises ⇒ goal（unsat(premises ∧ ¬goal)）。"""
        goal = simplify(forward_selects(goal))
        solver = _make_solver(self.timeout_ms)
        solver.add(And(BoolVal(True), *premises))
        solver.add(Not(goal))
        started = time.time()
        result = solver.check()
        self.queries.append((f"{self.name}: {label}", f"{result} ({time.time() - started:.2f}s)"))
        if result != unsat:
            self.failures.append(f"{label}: {result}")
            return False
        return True

    def prove_pointwise_split(self, label: str, premises: Sequence, w,
                              window_base, window_len: int, goal) -> bool:
        """窗口 case-split 逐点证明：w ∈ {base+k} 各一条 + w ∉ 窗口一条。

        穷尽性（BV）：在窗口不回绕前提（base ≤u base+len）下，
        w ∈ [base, base+len) ⇔ ∃k<len. w = base+k，与窗口外互补覆盖全
        地址空间。qword store 链对符号地址的数组判定在固定 w 点上退化
        为线性等式，绕开 Z3 对 Store⁸-vs-Lambda 等式的 unknown。
        """
        ok = True
        for k in range(window_len):
            ok &= self.prove(
                f"{label} [w=win+{k}]",
                list(premises) + [w == window_base + k], goal,
            )
        ok &= self.prove(
            f"{label} [w∉win]",
            list(premises)
            + [Not(And(ULE(window_base, w),
                       ULT(w, window_base + window_len)))],
            goal,
        )
        return ok

    def result(self) -> LemmaResult:
        return LemmaResult(
            name=self.name,
            proved=not self.failures,
            reasons=list(self.failures),
            queries=list(self.queries),
        )


def _fresh_lemma_state() -> SMTState:
    """引理证明的基础状态：R15=EVM 内存基址（带 tag），内存快照 M0 以
    EVM offset 空间表述、evm_mem 取其 R15 平移（同 build_cut_state 范式）。
    """
    state = SMTState.create_initial_state(num_inputs=0)
    r15 = state.callengine_memory_base
    state.x86_registers.set_register(Register.R15, r15)
    state.x86_registers.set_pointer_tag(Register.R15, PointerTag.EVM_PTR)
    state.x86_registers.set_register(
        Register.R14,
        state.callengine_stack_base + state.callengine_stack_byte_offset,
    )
    state.x86_registers.set_pointer_tag(Register.R14, PointerTag.STACK_PTR)
    return state


def _install_mem(state: SMTState, mem0_offset_space) -> None:
    """evm_mem := Lambda(a, mem0[a - r15])。"""
    r15 = state.callengine_memory_base
    a = BitVec(f"__t2_mem_addr_{id(mem0_offset_space)}", 64)
    state.x86_memory.evm_mem = Lambda([a], Select(mem0_offset_space, a - r15))


def _read_mem_at(state: SMTState, r15, w):
    """读段执行后 evm_mem 在 EVM offset w 处的字节（绝对地址 r15+w）。"""
    return Select(state.x86_memory.evm_mem, r15 + w)


def _byte_of(qword, k):
    """qword（64bit，little-endian 内存序）第 k 字节（k 为 64bit 符号项）。"""
    return Extract(7, 0, LShR(qword, BitVecVal(8, 64) * k))


def _qword_le(mem_offset_space, off):
    """从 offset 空间数组读 little-endian qword（mov reg,[mem] 的值）。"""
    from z3 import Concat
    bytes_ = [Select(mem_offset_space, off + BitVecVal(k, 64)) for k in range(8)]
    return Concat(*reversed(bytes_))


def _reg(state: SMTState, name64: str):
    return state.x86_registers.get_register(Register(name64))


def _set_reg(state: SMTState, name64: str, value, tag: PointerTag = PointerTag.NONE):
    state.x86_registers.set_register(Register(name64), value)
    if tag != PointerTag.NONE:
        state.x86_registers.set_pointer_tag(Register(name64), tag)


def _run_segment(blocks, state, entry, stops, max_depth=200):
    """段执行（复用 loop_induction 的 run_x86_segment）。"""
    from verification.loop_induction import run_x86_segment
    paths, defects, _ = run_x86_segment(
        blocks, state, entry, stops, max_depth=max_depth
    )
    return paths, defects


def _single_path(paths, kind: str, location: int):
    hits = [p for p in paths if p.kind != "terminal" and p.location == location]
    if kind == "any":
        return hits
    return hits


# ---------------------------------------------------------------------------
# 各引理
# ---------------------------------------------------------------------------

def prove_shr_align(blocks: Sequence[X86Block], header: int, exit_addr: int,
                    binding: Dict[str, object], timeout_ms: int = 60000) -> LemmaResult:
    """mcopy-shr-align：Inv(i) ≜ TMP = TMP0 >> 8i ∧ C = C0 - i。

    ②：C ≠ 0 一轮后 Inv(i+1)；③：出口处 C = 0 ⇒ TMP = TMP0 >> 8·C0。
    纯寄存器循环（§5.1：不修改 memory，不套 mem=F(i) 模板）。
    """
    ctx = _ProofContext("mcopy-shr-align", timeout_ms)
    reg_c, reg_t = binding["C"], binding["T"]

    tmp0 = BitVec("t2_shr_tmp0", 64)
    c0 = BitVec("t2_shr_c0", 64)
    i = BitVec("t2_shr_i", 64)

    state = _fresh_lemma_state()
    m0 = Array("t2_shr_mem0", BV64, BV8)
    _install_mem(state, m0)
    _set_reg(state, reg_t, LShR(tmp0, BitVecVal(8, 64) * i))
    _set_reg(state, reg_c, c0 - i)

    premises = [ULE(i, c0), ULE(c0, BitVecVal(8, 64))]

    paths, defects = _run_segment(blocks, state.copy(), header, {header, exit_addr})
    if defects:
        ctx.failures.append("; ".join(defects))
        return ctx.result()

    latch = [p for p in paths if p.kind != "terminal" and p.location == header]
    exits = [p for p in paths if p.kind != "terminal" and p.location == exit_addr]
    if len(latch) != 1 or len(exits) != 1:
        ctx.failures.append(
            f"unexpected path shape: {[(p.kind, p.location) for p in paths]}"
        )
        return ctx.result()

    # ② 归纳步：i' = i+1
    lp = latch[0]
    pre = premises + [lp.condition, ULT(i, c0)]
    ctx.prove("② tmp' = tmp0 >> 8(i+1)", pre,
              _reg(lp.state, reg_t) == LShR(tmp0, BitVecVal(8, 64) * (i + 1)))
    ctx.prove("② c' = c0-(i+1)", pre, _reg(lp.state, reg_c) == c0 - (i + 1))
    # ②(a) 决策对齐的单侧退化：latch 路径蕴含 i < c0（继续条件与 Inv 一致）
    ctx.prove("② latch ⇒ i < c0", premises + [lp.condition], ULT(i, c0))

    # ③ 出口：C=0 ⇒ i=c0 ⇒ TMP = TMP0 >> 8·c0
    ep = exits[0]
    pre = premises + [ep.condition]
    ctx.prove("③ exit ⇒ i = c0", pre, i == c0)
    ctx.prove("③ tmp = tmp0 >> 8·c0", pre,
              _reg(ep.state, reg_t) == LShR(tmp0, BitVecVal(8, 64) * c0))
    ctx.prove("③ memory 不被修改", pre,
              _read_mem_at(ep.state, state.callengine_memory_base,
                           BitVec("t2_shr_w", 64))
              == Select(m0, BitVec("t2_shr_w", 64)))
    return ctx.result()


def _overlay_byte(tmp0, m1, dt0, count, w):
    """tail 覆盖的逐点值：[dt0, dt0+count) 内取 tmp0 的对应字节，否则 m1。"""
    return If(
        And(ULE(dt0, w), ULT(w, dt0 + count)),
        _byte_of(tmp0, w - dt0),
        Select(m1, w),
    )


def prove_byte_tail(blocks: Sequence[X86Block], header: int, exit_addr: int,
                    binding: Dict[str, object], timeout_ms: int = 60000) -> LemmaResult:
    """mcopy-byte-tail：Inv(j) ≜ mem = overlay(TMP0 前 j 字节 @ DT0, M1)
    ∧ TMP = TMP0 >> 8j ∧ DST = r15+DT0+j ∧ S = ST0-j。

    M1 是任意基内存（复合时实例化为 word 段出口的 F/G），TMP0 任意
    qword（复合时实例化为跨界 qword / 对齐移位结果）。
    """
    ctx = _ProofContext("mcopy-byte-tail", timeout_ms)
    reg_dst, reg_t, reg_s = binding["DST"], binding["T"], binding["S"]

    m1 = Array("t2_tail_m1", BV64, BV8)
    tmp0 = BitVec("t2_tail_tmp0", 64)
    dt0 = BitVec("t2_tail_dt0", 64)
    st0 = BitVec("t2_tail_st0", 64)
    j = BitVec("t2_tail_j", 64)
    w = BitVec("t2_tail_w", 64)

    state = _fresh_lemma_state()
    r15 = state.callengine_memory_base
    a = BitVec("t2_tail_lam", 64)
    inv_mem = Lambda([a], _overlay_byte(tmp0, m1, dt0, j, a))
    _install_mem(state, inv_mem)
    _set_reg(state, reg_dst, r15 + dt0 + j, PointerTag.EVM_PTR)
    _set_reg(state, reg_t, LShR(tmp0, BitVecVal(8, 64) * j))
    _set_reg(state, reg_s, st0 - j)

    premises = [
        ULE(j, st0),
        ULE(st0, BitVecVal(8, 64)),
        # 8 字节窗口不回绕（tail 覆盖区间 ≤ 8 字节）
        ULE(dt0, dt0 + BitVecVal(8, 64)),
    ]

    paths, defects = _run_segment(blocks, state.copy(), header, {header, exit_addr})
    if defects:
        ctx.failures.append("; ".join(defects))
        return ctx.result()
    latch = [p for p in paths if p.kind != "terminal" and p.location == header]
    exits = [p for p in paths if p.kind != "terminal" and p.location == exit_addr]
    if len(latch) != 1 or len(exits) != 1:
        ctx.failures.append(
            f"unexpected path shape: {[(p.kind, p.location) for p in paths]}"
        )
        return ctx.result()

    lp = latch[0]
    pre = premises + [lp.condition]
    ctx.prove("② latch ⇒ j < st0", pre, ULT(j, st0))
    ctx.prove("② mem' = overlay(j+1)", pre,
              _read_mem_at(lp.state, r15, w)
              == _overlay_byte(tmp0, m1, dt0, j + 1, w))
    ctx.prove("② tmp' = tmp0 >> 8(j+1)", pre,
              _reg(lp.state, reg_t) == LShR(tmp0, BitVecVal(8, 64) * (j + 1)))
    ctx.prove("② dst' = r15+dt0+j+1", pre,
              _reg(lp.state, reg_dst) == r15 + dt0 + (j + 1))
    ctx.prove("② s' = st0-(j+1)", pre, _reg(lp.state, reg_s) == st0 - (j + 1))

    ep = exits[0]
    pre = premises + [ep.condition]
    ctx.prove("③ exit ⇒ j = st0", pre, j == st0)
    ctx.prove("③ mem = overlay(st0)（满覆盖）", pre,
              _read_mem_at(ep.state, r15, w)
              == _overlay_byte(tmp0, m1, dt0, st0, w))
    return ctx.result()


def _copy_region_byte(m0, d0, s0, copied, w):
    """word 拷贝已完成区间的逐点值：[d0, d0+copied) 内取源字节，否则 m0。"""
    return If(
        And(ULE(d0, w), ULT(w, d0 + copied)),
        Select(m0, w - d0 + s0),
        Select(m0, w),
    )


def _mcopy_no_wrap_premises(d0, s0, size0):
    return [
        ULT(size0, BitVecVal(1 << 63, 64)),      # signed jl/jle 与 unsigned 一致
        ULE(d0, d0 + size0),                     # dst 区间不回绕
        ULE(s0, s0 + size0),                     # src 区间不回绕
    ]


def prove_low_word(blocks: Sequence[X86Block], header: int, exit_addr: int,
                   tail_addr: int, binding: Dict[str, object],
                   timeout_ms: int = 60000) -> LemmaResult:
    """mcopy-low-word：Inv(C) ≜ mem = F(C)（升序已拷 C 字节）
    ∧ DST = r15+D0+C ∧ SRC = r15+S0+C ∧ S = SIZE0-C。

    前提含 FromLow 分派方向 D0 ≤ S0（保证尚未读取的源区间未被覆写，
    §5.1 快照相对不变式的关键）。
    """
    ctx = _ProofContext("mcopy-low-word", timeout_ms)
    reg_dst, reg_src = binding["DST"], binding["SRC"]
    reg_s, reg_t = binding["S"], binding["T"]

    m0 = Array("t2_lw_m0", BV64, BV8)
    d0 = BitVec("t2_lw_d0", 64)
    s0 = BitVec("t2_lw_s0", 64)
    size0 = BitVec("t2_lw_size0", 64)
    c = BitVec("t2_lw_c", 64)
    w = BitVec("t2_lw_w", 64)

    state = _fresh_lemma_state()
    r15 = state.callengine_memory_base
    a = BitVec("t2_lw_lam", 64)
    _install_mem(state, Lambda([a], _copy_region_byte(m0, d0, s0, c, a)))
    _set_reg(state, reg_dst, r15 + d0 + c, PointerTag.EVM_PTR)
    _set_reg(state, reg_src, r15 + s0 + c, PointerTag.EVM_PTR)
    _set_reg(state, reg_s, size0 - c)

    premises = [ULE(c, size0), ULE(d0, s0)] + _mcopy_no_wrap_premises(d0, s0, size0)

    paths, defects = _run_segment(
        blocks, state.copy(), header, {header, exit_addr, tail_addr}
    )
    if defects:
        ctx.failures.append("; ".join(defects))
        return ctx.result()
    latch = [p for p in paths if p.kind != "terminal" and p.location == header]
    exits = [p for p in paths if p.kind != "terminal" and p.location == exit_addr]
    tails = [p for p in paths if p.kind != "terminal" and p.location == tail_addr]
    if len(latch) != 1 or len(exits) != 1 or len(tails) != 1:
        ctx.failures.append(
            f"unexpected path shape: {[(p.kind, p.location) for p in paths]}"
        )
        return ctx.result()

    # ② 归纳步（整字轮：S ≥ 8）
    lp = latch[0]
    pre = premises + [lp.condition]
    ctx.prove("② latch ⇒ 8 ≤ size0-c", pre, ULE(BitVecVal(8, 64), size0 - c))
    ctx.prove_pointwise_split(
        "② mem' = F(c+8)", pre, w, d0 + c, 8,
        _read_mem_at(lp.state, r15, w) == _copy_region_byte(m0, d0, s0, c + 8, w),
    )
    ctx.prove("② dst' = +8", pre, _reg(lp.state, reg_dst) == r15 + d0 + (c + 8))
    ctx.prove("② src' = +8", pre, _reg(lp.state, reg_src) == r15 + s0 + (c + 8))
    ctx.prove("② s' = size0-(c+8)", pre, _reg(lp.state, reg_s) == size0 - (c + 8))

    # ③ je 出口（S=0 ⇒ 拷贝完成）
    ep = exits[0]
    pre = premises + [ep.condition]
    ctx.prove("③ je 出口 ⇒ c = size0", pre, c == size0)
    ctx.prove("③ mem = F(size0)（MCOPY 闭式）", pre,
              _read_mem_at(ep.state, r15, w)
              == _copy_region_byte(m0, d0, s0, size0, w))

    # ③ jl 出口（0 < S < 8，状态原样交给 tail 段）
    tp = tails[0]
    pre = premises + [tp.condition]
    ctx.prove("③ jl 出口 ⇒ 剩余 < 8", pre, ULT(size0 - c, BitVecVal(8, 64)))
    ctx.prove("③ jl 出口 mem 未变", pre,
              _read_mem_at(tp.state, r15, w)
              == _copy_region_byte(m0, d0, s0, c, w))
    ctx.prove("③ jl 出口 dst 未变", pre, _reg(tp.state, reg_dst) == r15 + d0 + c)
    ctx.prove("③ jl 出口 src 未变", pre, _reg(tp.state, reg_src) == r15 + s0 + c)
    ctx.prove("③ jl 出口 s 未变", pre, _reg(tp.state, reg_s) == size0 - c)
    return ctx.result()


def prove_high_word(blocks: Sequence[X86Block], header: int, exit_addr: int,
                    exit2_addr: int, binding: Dict[str, object],
                    timeout_ms: int = 60000) -> LemmaResult:
    """mcopy-high-word：Inv(S) ≜ mem = G(S)（降序，顶部 [D0+S, D0+SIZE0)
    已拷）∧ DST = r15+D0+S-8 ∧ SRC = r15+S0+S-8 ∧ 寄存器 S 为剩余字节。

    前提含 FromHigh 分派方向 S0 < D0 与可达栈深约束 S=0 ∨ S ≥ 8
    （首入 S=SIZE0>8，latch 要求 S-8≥8，真实可达头状态满足）。
    """
    ctx = _ProofContext("mcopy-high-word", timeout_ms)
    reg_dst, reg_src = binding["DST"], binding["SRC"]
    reg_s, reg_t = binding["S"], binding["T"]

    m0 = Array("t2_hw_m0", BV64, BV8)
    d0 = BitVec("t2_hw_d0", 64)
    s0 = BitVec("t2_hw_s0", 64)
    size0 = BitVec("t2_hw_size0", 64)
    s = BitVec("t2_hw_s", 64)
    w = BitVec("t2_hw_w", 64)

    def g_mem(remaining, addr):
        return If(
            And(ULE(d0 + remaining, addr), ULT(addr, d0 + size0)),
            Select(m0, addr - d0 + s0),
            Select(m0, addr),
        )

    state = _fresh_lemma_state()
    r15 = state.callengine_memory_base
    a = BitVec("t2_hw_lam", 64)
    _install_mem(state, Lambda([a], g_mem(s, a)))
    _set_reg(state, reg_dst, r15 + d0 + s - 8, PointerTag.EVM_PTR)
    _set_reg(state, reg_src, r15 + s0 + s - 8, PointerTag.EVM_PTR)
    _set_reg(state, reg_s, s)

    premises = [
        ULE(s, size0),
        Or(s == 0, ULE(BitVecVal(8, 64), s)),
        ULT(s0, d0),
    ] + _mcopy_no_wrap_premises(d0, s0, size0)

    paths, defects = _run_segment(
        blocks, state.copy(), header, {header, exit_addr, exit2_addr}
    )
    if defects:
        ctx.failures.append("; ".join(defects))
        return ctx.result()
    latch = [p for p in paths if p.kind != "terminal" and p.location == header]
    exits = [p for p in paths if p.kind != "terminal" and p.location == exit_addr]
    exit2s = [p for p in paths if p.kind != "terminal" and p.location == exit2_addr]
    if len(latch) != 1 or len(exits) != 1 or len(exit2s) != 1:
        ctx.failures.append(
            f"unexpected path shape: {[(p.kind, p.location) for p in paths]}"
        )
        return ctx.result()

    # ② 归纳步（S ≥ 8 且 S-8 ≥ 8）
    lp = latch[0]
    pre = premises + [lp.condition]
    ctx.prove_pointwise_split(
        "② mem' = G(s-8)", pre, w, d0 + s - 8, 8,
        _read_mem_at(lp.state, r15, w) == g_mem(s - 8, w),
    )
    ctx.prove("② dst' = r15+d0+(s-8)-8", pre,
              _reg(lp.state, reg_dst) == r15 + d0 + (s - 8) - 8)
    ctx.prove("② src' = r15+s0+(s-8)-8", pre,
              _reg(lp.state, reg_src) == r15 + s0 + (s - 8) - 8)
    ctx.prove("② s' = s-8", pre, _reg(lp.state, reg_s) == s - 8)

    # ③ je 出口（仅 S=0 可达 ⇒ 全部拷完）
    ep = exits[0]
    pre = premises + [ep.condition]
    ctx.prove("③ je 出口 ⇒ s = 0", pre, s == 0)
    ctx.prove("③ mem = G(0)（MCOPY 闭式）", pre,
              _read_mem_at(ep.state, r15, w) == g_mem(BitVecVal(0, 64), w))

    # ③ jl 出口（本轮已拷一字，剩余 S' = S-8 < 8；dst 未回退，交给 glue）
    tp = exit2s[0]
    pre = premises + [tp.condition]
    ctx.prove("③ jl 出口 ⇒ 剩余 < 8", pre, ULT(s - 8, BitVecVal(8, 64)))
    ctx.prove_pointwise_split(
        "③ jl 出口 mem = G(s-8)", pre, w, d0 + s - 8, 8,
        _read_mem_at(tp.state, r15, w) == g_mem(s - 8, w),
    )
    ctx.prove("③ jl 出口 dst = r15+d0+(s-8)", pre,
              _reg(tp.state, reg_dst) == r15 + d0 + (s - 8))
    ctx.prove("③ jl 出口 src = r15+s0+(s-8)-8", pre,
              _reg(tp.state, reg_src) == r15 + s0 + (s - 8) - 8)
    ctx.prove("③ jl 出口 s' = s-8", pre, _reg(tp.state, reg_s) == s - 8)
    return ctx.result()


def _getdata_byte(source, off, length, k):
    """getData 语义：源越界补 0。"""
    return If(ULT(off + k, length), Select(source, off + k), BitVecVal(0, 8))


def _prove_byte_copy_common(
    ctx: _ProofContext,
    blocks: Sequence[X86Block],
    header: int,
    exit_addr: int,
    binding: Dict[str, object],
    *,
    source_kind: str,
    n_latch_paths: int,
) -> LemmaResult:
    """returndata/makedata 逐字节倒序拷贝的共用证明骨架。

    Inv(S) ≜ mem = H(S)（已写 [DST+S, DST+SIZE0)，值 = 源字节/getData）
    ∧ 计数寄存器 = S ∧ OFF/LEN/INP/DST 保持。
    """
    reg_s, reg_off = binding["S"], binding["OFF"]
    reg_inp, reg_dst = binding["INP"], binding["DST"]

    d0 = BitVec("t2_bc_dst", 64)
    off0 = BitVec("t2_bc_off", 64)
    size0 = BitVec("t2_bc_size0", 64)
    s = BitVec("t2_bc_s", 64)
    w = BitVec("t2_bc_w", 64)
    m0 = Array("t2_bc_m0", BV64, BV8)

    state = _fresh_lemma_state()
    r15 = state.callengine_memory_base

    if source_kind == "returndata":
        source = state.return_data
        ptr = state.callengine_return_data_pointer
        tag = PointerTag.RETURNDATA_PTR
        length = None
    else:
        source = state.calldata
        ptr = state.callengine_input_pointer
        tag = PointerTag.CALLDATA_PTR
        length = BitVec("t2_bc_len", 64)

    def h_byte(k):
        if length is None:
            return Select(source, off0 + k)
        return _getdata_byte(source, off0, length, k)

    def h_mem(remaining, addr):
        return If(
            And(ULE(d0 + remaining, addr), ULT(addr, d0 + size0)),
            h_byte(addr - d0),
            Select(m0, addr),
        )

    a = BitVec("t2_bc_lam", 64)
    _install_mem(state, Lambda([a], h_mem(s, a)))
    _set_reg(state, reg_s, s)
    _set_reg(state, reg_off, off0)
    _set_reg(state, reg_inp, ptr, tag)
    _set_reg(state, reg_dst, d0)
    if length is not None:
        _set_reg(state, binding["LEN"], length)

    premises = [
        ULE(s, size0),
        ULT(size0, BitVecVal(1 << 63, 64)),
        ULE(d0, d0 + size0),        # dst 区间不回绕
        ULE(off0, off0 + size0),    # 源偏移区间不回绕
    ]

    paths, defects = _run_segment(blocks, state.copy(), header, {header, exit_addr})
    if defects:
        ctx.failures.append("; ".join(defects))
        return ctx.result()
    latch = [p for p in paths if p.kind != "terminal" and p.location == header]
    exits = [p for p in paths if p.kind != "terminal" and p.location == exit_addr]
    if len(latch) != n_latch_paths or len(exits) != 1:
        ctx.failures.append(
            f"unexpected path shape: {[(p.kind, p.location) for p in paths]}"
        )
        return ctx.result()

    for idx, lp in enumerate(latch):
        pre = premises + [lp.condition]
        ctx.prove(f"② latch#{idx} ⇒ 1 ≤ s", pre, ULE(BitVecVal(1, 64), s))
        ctx.prove(f"② latch#{idx} mem' = H(s-1)", pre,
                  _read_mem_at(lp.state, r15, w) == h_mem(s - 1, w))
        ctx.prove(f"② latch#{idx} s' = s-1", pre, _reg(lp.state, reg_s) == s - 1)
        ctx.prove(f"② latch#{idx} off 保持", pre, _reg(lp.state, reg_off) == off0)
        ctx.prove(f"② latch#{idx} dst 保持", pre, _reg(lp.state, reg_dst) == d0)
        ctx.prove(f"② latch#{idx} inp 保持", pre, _reg(lp.state, reg_inp) == ptr)
        if length is not None:
            ctx.prove(f"② latch#{idx} len 保持", pre,
                      _reg(lp.state, binding["LEN"]) == length)

    ep = exits[0]
    pre = premises + [ep.condition]
    ctx.prove("③ 出口 ⇒ s = 0", pre, s == 0)
    ctx.prove("③ mem = H(0)（getData 闭式）", pre,
              _read_mem_at(ep.state, r15, w) == h_mem(BitVecVal(0, 64), w))
    return ctx.result()


def prove_returndata_byte_copy(blocks, header, exit_addr, binding,
                               timeout_ms: int = 60000) -> LemmaResult:
    """returndata-byte-copy：源 = return_data（构造前置已保证不越界，
    循环内无补 0 分支）。"""
    ctx = _ProofContext("returndata-byte-copy", timeout_ms)
    return _prove_byte_copy_common(
        ctx, blocks, header, exit_addr, binding,
        source_kind="returndata", n_latch_paths=1,
    )


def prove_makedata_byte_copy(blocks, header, exit_addr, binding,
                             timeout_ms: int = 60000) -> LemmaResult:
    """makedata-byte-copy（CALLDATACOPY/CODECOPY）：源 = getData 语义
    （off+j ≥ len 补 0），循环体内两条 latch 路径（命中/越界）。"""
    ctx = _ProofContext("makedata-byte-copy", timeout_ms)
    return _prove_byte_copy_common(
        ctx, blocks, header, exit_addr, binding,
        source_kind="calldata", n_latch_paths=2,
    )


# ---------------------------------------------------------------------------
# MCOPY 构造级复合（§5.1 "FromHigh 三段串联复合引理" / FromLow 两段）
# ---------------------------------------------------------------------------

def prove_mcopy_low_composition(
    blocks: Sequence[X86Block],
    glue_entry: int,
    tail_header: int,
    word_binding: Dict[str, object],
    tail_binding: Dict[str, object],
    timeout_ms: int = 60000,
) -> LemmaResult:
    """FromLow 复合：word-jl 出口状态 → glue（跨界 qword 载入）→ tail
    基例成立 + tail 满覆盖 == MCOPY 闭式。

    与 word/tail 两条已证引理按 §5.3 组装出 FromLow 构造级定理：
    word ②*（任意轮）→ jl 出口 → glue → tail Inv(0) → tail ②*（任意轮）
    → tail ③ 满覆盖 → 本函数的复合恒等式收尾。je 直接出口的闭式已由
    word ③ 覆盖。
    """
    ctx = _ProofContext("mcopy-low-composition", timeout_ms)
    reg_dst, reg_src = word_binding["DST"], word_binding["SRC"]
    reg_s, reg_t = word_binding["S"], word_binding["T"]
    # tail 与 word 的寄存器角色必须一致（同一构造的寄存器分配）
    if (tail_binding["DST"], tail_binding["T"], tail_binding["S"]) != (
        reg_dst, reg_t, reg_s
    ):
        ctx.failures.append("tail/word register roles mismatch")
        return ctx.result()

    m0 = Array("t2_lc_m0", BV64, BV8)
    d0 = BitVec("t2_lc_d0", 64)
    s0 = BitVec("t2_lc_s0", 64)
    size0 = BitVec("t2_lc_size0", 64)
    c = BitVec("t2_lc_c", 64)
    w = BitVec("t2_lc_w", 64)

    state = _fresh_lemma_state()
    r15 = state.callengine_memory_base
    a = BitVec("t2_lc_lam", 64)
    f_c = Lambda([a], _copy_region_byte(m0, d0, s0, c, a))
    _install_mem(state, f_c)
    _set_reg(state, reg_dst, r15 + d0 + c, PointerTag.EVM_PTR)
    _set_reg(state, reg_src, r15 + s0 + c, PointerTag.EVM_PTR)
    _set_reg(state, reg_s, size0 - c)

    rem = size0 - c
    premises = (
        [ULE(c, size0), ULE(d0, s0), ULT(rem, BitVecVal(8, 64))]
        + _mcopy_no_wrap_premises(d0, s0, size0)
        # 跨界 qword 读窗不回绕
        + [ULE(s0 + c, s0 + c + BitVecVal(8, 64))]
    )

    # glue：mov T, qword [SRC]（tail 基例的 TMP0 载入）
    paths, defects = _run_segment(blocks, state.copy(), glue_entry, {tail_header})
    if defects:
        ctx.failures.append("; ".join(defects))
        return ctx.result()
    arrivals = [p for p in paths if p.kind != "terminal" and p.location == tail_header]
    if len(arrivals) != 1:
        ctx.failures.append(
            f"unexpected glue paths: {[(p.kind, p.location) for p in paths]}"
        )
        return ctx.result()
    gp = arrivals[0]
    pre = premises + [gp.condition]

    tmp0 = _qword_le(f_c, s0 + c)
    ctx.prove("glue: tmp = 跨界 qword（tail 基例 TMP0）", pre,
              _reg(gp.state, reg_t) == tmp0)
    ctx.prove("glue: mem 未变", pre,
              _read_mem_at(gp.state, r15, w) == _copy_region_byte(m0, d0, s0, c, w))
    ctx.prove("glue: dst 未变", pre, _reg(gp.state, reg_dst) == r15 + d0 + c)
    ctx.prove("glue: s 未变", pre, _reg(gp.state, reg_s) == size0 - c)

    # 复合恒等式：tail 满覆盖(overlay) == MCOPY 闭式（rem < 8 ⇒ 8 点窗口穷尽）
    ctx.prove_pointwise_split(
        "恒等式: overlay(tail 满写) == MCOPY 闭式", premises, w, d0 + c, 8,
        _overlay_byte(tmp0, f_c, d0 + c, rem, w)
        == _copy_region_byte(m0, d0, s0, size0, w),
    )
    return ctx.result()


def prove_mcopy_high_composition(
    blocks: Sequence[X86Block],
    preamble_entry: int,
    word_header: int,
    glue_entry: int,
    shr_header: int,
    tail_header: int,
    word_binding: Dict[str, object],
    shr_binding: Dict[str, object],
    tail_binding: Dict[str, object],
    timeout_ms: int = 60000,
) -> LemmaResult:
    """FromHigh 三段复合：分派后 preamble 建立 word 基例 → word-jl 出口
    → glue（dst 回退 + 跨界 qword 载入 + 移位计数 8-S'）→ SHR 基例 →
    SHR ③（tmp0 >> 8(8-S')）→ tail 基例 → tail 满覆盖 == MCOPY 闭式。
    """
    ctx = _ProofContext("mcopy-high-composition", timeout_ms)
    reg_dst, reg_src = word_binding["DST"], word_binding["SRC"]
    reg_s, reg_t = word_binding["S"], word_binding["T"]
    if (tail_binding["DST"], tail_binding["T"], tail_binding["S"]) != (
        reg_dst, reg_t, reg_s
    ) or shr_binding["T"] != reg_t or shr_binding["C"] != reg_src:
        ctx.failures.append("register roles mismatch across segments")
        return ctx.result()

    m0 = Array("t2_hc_m0", BV64, BV8)
    d0 = BitVec("t2_hc_d0", 64)
    s0 = BitVec("t2_hc_s0", 64)
    size0 = BitVec("t2_hc_size0", 64)
    w = BitVec("t2_hc_w", 64)

    no_wrap = _mcopy_no_wrap_premises(d0, s0, size0)

    # --- 段 A：preamble 建立 word 基例 Inv(S=SIZE0) ---
    state = _fresh_lemma_state()
    r15 = state.callengine_memory_base
    a = BitVec("t2_hc_lam0", 64)
    _install_mem(state, Lambda([a], Select(m0, a)))
    _set_reg(state, reg_dst, r15 + d0, PointerTag.EVM_PTR)
    _set_reg(state, reg_src, r15 + s0, PointerTag.EVM_PTR)
    _set_reg(state, reg_s, size0)

    pre_base = [ULT(BitVecVal(8, 64), size0), ULT(s0, d0)] + no_wrap
    paths, defects = _run_segment(
        blocks, state.copy(), preamble_entry, {word_header, tail_header, shr_header}
    )
    if defects:
        ctx.failures.append("; ".join(defects))
        return ctx.result()
    to_word = [p for p in paths if p.kind != "terminal" and p.location == word_header]
    strays = [p for p in paths if p.kind != "terminal" and p.location != word_header]
    if len(to_word) != 1:
        ctx.failures.append(
            f"unexpected preamble paths: {[(p.kind, p.location) for p in paths]}"
        )
        return ctx.result()
    for sp in strays:
        # 防御性 size<8 分支在 size0>8 前提下不可达
        ctx.prove("preamble: 防御分支不可达", pre_base + [sp.condition], BoolVal(False))
    bp = to_word[0]
    pre = pre_base + [bp.condition]
    ctx.prove("preamble: dst = r15+d0+size0-8", pre,
              _reg(bp.state, reg_dst) == r15 + d0 + size0 - 8)
    ctx.prove("preamble: src = r15+s0+size0-8", pre,
              _reg(bp.state, reg_src) == r15 + s0 + size0 - 8)
    ctx.prove("preamble: s = size0", pre, _reg(bp.state, reg_s) == size0)
    ctx.prove("preamble: mem 未变", pre,
              _read_mem_at(bp.state, r15, w) == Select(m0, w))

    # --- 段 B：word-jl 出口 → glue → SHR 基例 ---
    # word ③(jl) 出口状态（剩余 S' < 8）：mem=G(S')，dst=r15+d0+S'，
    # src=r15+s0+S'-8，s=S'。
    s_rem = BitVec("t2_hc_srem", 64)

    def g_mem(remaining, addr):
        return If(
            And(ULE(d0 + remaining, addr), ULT(addr, d0 + size0)),
            Select(m0, addr - d0 + s0),
            Select(m0, addr),
        )

    state = _fresh_lemma_state()
    r15 = state.callengine_memory_base
    a2 = BitVec("t2_hc_lam1", 64)
    g_arr = Lambda([a2], g_mem(s_rem, a2))
    _install_mem(state, g_arr)
    _set_reg(state, reg_dst, r15 + d0 + s_rem, PointerTag.EVM_PTR)
    _set_reg(state, reg_src, r15 + s0 + s_rem - 8, PointerTag.EVM_PTR)
    _set_reg(state, reg_s, s_rem)

    pre_glue = (
        [ULT(s_rem, BitVecVal(8, 64)), ULE(s_rem, size0), ULT(s0, d0)] + no_wrap
    )
    paths, defects = _run_segment(blocks, state.copy(), glue_entry, {shr_header})
    if defects:
        ctx.failures.append("; ".join(defects))
        return ctx.result()
    arrivals = [p for p in paths if p.kind != "terminal" and p.location == shr_header]
    if len(arrivals) != 1:
        ctx.failures.append(
            f"unexpected glue paths: {[(p.kind, p.location) for p in paths]}"
        )
        return ctx.result()
    gp = arrivals[0]
    pre = pre_glue + [gp.condition]

    tmp0 = _qword_le(g_arr, s0 + s_rem - 8)
    ctx.prove("glue: dst 回退到 r15+d0", pre, _reg(gp.state, reg_dst) == r15 + d0)
    ctx.prove("glue: tmp = 跨界 qword", pre, _reg(gp.state, reg_t) == tmp0)
    ctx.prove("glue: 移位计数 = 8-s'", pre,
              _reg(gp.state, reg_src) == BitVecVal(8, 64) - s_rem)
    ctx.prove("glue: mem 未变", pre,
              _read_mem_at(gp.state, r15, w) == g_mem(s_rem, w))

    # --- 复合恒等式：tail 满覆盖(移位后 tmp) == MCOPY 闭式（8 点窗口穷尽）---
    shifted = LShR(tmp0, BitVecVal(8, 64) * (BitVecVal(8, 64) - s_rem))
    ctx.prove_pointwise_split(
        "恒等式: overlay(shift(tmp), s') == MCOPY 闭式", pre_glue, w, d0, 8,
        _overlay_byte(shifted, g_arr, d0, s_rem, w)
        == _copy_region_byte(m0, d0, s0, size0, w),
    )
    return ctx.result()
