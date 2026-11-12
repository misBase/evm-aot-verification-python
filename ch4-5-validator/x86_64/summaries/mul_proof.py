"""Per-hit glue proof for compileEVMMul slices.

matcher 命中一段 MUL slice 后，summary 进入 runtime 索引前，这里对该 slice 做
端到端 glue 证明：把 p/q limb 放成自由符号，按 checkpoint 逐段 raw 符号执行
（不经过 summary 折叠），证明每段输出寄存器等于分支化 limb 算法的中间值，最后
符号执行尾部 4 条 result store 并证明 stack 内存上的最终值逐 limb 等于算法输出。
证明失败（包括 solver unknown/timeout）一律 raise，fail-closed。

"limb 算法 == Uint256.mul_semantics" 是与具体 slice 无关的纯数学 composition
lemma，由 tests/composition/test_mul_summary_composition.py 覆盖，不在 per-hit
路径重跑。
"""

from __future__ import annotations

from typing import Dict, Sequence, Tuple

from z3 import (
    Array,
    BitVec,
    BitVecSort,
    BitVecVal,
    Concat,
    Extract,
    Or,
    SolverFor,
    ZeroExt,
    unsat,
)

from state.smt_state import MemoryDomain, SMTState
from state.x86_state import X86MemoryState
from x86_64.disassembler import parse_operands
from x86_64.models import Register, X86Instruction
from x86_64.summaries.mul import (
    ConstLimbLocation,
    MulSummary,
    RegisterLimbLocation,
    StackLimbLocation,
)


_ZERO64 = BitVecVal(0, 64)
_ZERO_CARRY = BitVecVal(0, 1)


class MulProofError(ValueError):
    """Per-hit MUL slice proof failure.

    消息固定格式 ``entry=0x..., label=..., reason=..., solver_result=...``，
    production 报错与测试断言都依赖该格式。``from_cache`` 标记该失败是否来自
    失败缓存命中。
    """

    def __init__(
        self,
        entry_addr: int,
        label: str,
        reason: str,
        solver_result: str = "structural",
        *,
        from_cache: bool = False,
    ):
        super().__init__(
            f"entry=0x{entry_addr:x}, label={label}, "
            f"reason={reason}, solver_result={solver_result}"
        )
        self.entry_addr = entry_addr
        self.label = label
        self.reason = reason
        self.solver_result = solver_result
        self.from_cache = from_cache


def _mul64(x, y):
    """64x64 -> hi/lo limb 乘法，对应 x86 ``mul r64`` 的 RDX:RAX 输出。"""
    product = ZeroExt(64, x) * ZeroExt(64, y)
    return Extract(127, 64, product), Extract(63, 0, product)


def _add64(x, y, carry=_ZERO_CARRY):
    """一轮 64-bit 加法与 carry，对应 add/adc 建模。"""
    total = (
        Concat(BitVecVal(0, 1), x)
        + Concat(BitVecVal(0, 1), y)
        + Concat(BitVecVal(0, 64), carry)
    )
    return Extract(63, 0, total), Extract(64, 64, total)


def _umul_hop(z, x, y):
    """一轮 partial-product 累加：lo += z，并把 carry 加回 hi。"""
    hi, lo = _mul64(x, y)
    lo, carry = _add64(lo, z)
    hi, _ = _add64(hi, _ZERO64, carry)
    return hi, lo


def _umul_step(z, x, y, carry):
    """带前序 carry 的规范化 partial-product 累加。"""
    hi, lo = _mul64(x, y)
    lo, carry_bit = _add64(lo, carry)
    hi, _ = _add64(hi, _ZERO64, carry_bit)
    lo, carry_bit = _add64(lo, z)
    hi, _ = _add64(hi, _ZERO64, carry_bit)
    return hi, lo


def _umul_step_x86_order(z, x, y, carry):
    """和 raw x86 add/adc 顺序一致：先加 z，再加前序 carry。"""
    hi, lo = _mul64(x, y)
    lo, carry_bit = _add64(lo, z)
    hi, _ = _add64(hi, _ZERO64, carry_bit)
    lo, carry_bit = _add64(lo, carry)
    hi, _ = _add64(hi, _ZERO64, carry_bit)
    return hi, lo


def _execute_insns(state: SMTState, insns) -> SMTState:
    """按 raw x86 语义顺序执行指令，不经过 summary 折叠（否则自证）。"""
    for insn in insns:
        state = insn.to_z3(state)
    return state


def _is_stack_store(insn: X86Instruction) -> bool:
    """判断指令是否是向内存写 64-bit result limb 的 mov。"""
    ops = parse_operands(insn)
    return (
        insn.mnemonic.lower() == "mov"
        and ops.get("is_memory")
        and ops.get("dest_reg") is None
        and ops.get("src_reg") is not None
    )


def _zero_branch_flags(summary: MulSummary) -> Tuple[bool, bool, bool]:
    """从 summary 的 q2/q3/q4 location 还原编译期零值分支选择。"""
    return tuple(
        isinstance(loc, ConstLimbLocation) and loc.value == 0
        for loc in summary.q_limb_locs[1:]
    )


def _stack_or_register_limb_expr(loc, state: SMTState):
    """register/stack 来源的 limb -> Z3 表达式（const 由调用方单独处理）。"""
    if isinstance(loc, RegisterLimbLocation):
        return state.x86_registers.get_register(loc.reg)
    if isinstance(loc, StackLimbLocation):
        r14 = state.x86_registers.get_register(Register.R14)
        return state.x86_memory.load_limb(
            r14 + BitVecVal(loc.offset, 64),
            domain=MemoryDomain.STACK,
        )
    raise TypeError(f"unknown limb location: {loc!r}")


class _MulSliceProof:
    """单次 per-hit glue 证明的上下文（entry/label/timeout 与失败上报）。"""

    def __init__(
        self,
        summary: MulSummary,
        slice_insns: Sequence[X86Instruction],
        *,
        timeout_ms: int,
        label: str,
    ):
        self.summary = summary
        self.insns = list(slice_insns)
        self.timeout_ms = timeout_ms
        self.label = label
        # 非零 const limb 的 fresh 符号表，key 为 (tag, index)（tag ∈ {"p","q"}）。
        # 同一 slot 全程复用同一符号，让两侧乘法都退化成规整的 sym×sym（避免
        # Z3 对 const×sym 做昂贵的 shift-and-add 展开）。零值 const 不入表。
        self._const_symbols: Dict[Tuple[str, int], BitVec] = {}

    def _fail(self, label: str, reason: str, solver_result: str = "structural"):
        raise MulProofError(
            self.summary.entry_addr,
            f"{self.label} {label}",
            reason,
            solver_result,
        )

    def _require(self, condition: bool, label: str, reason: str) -> None:
        if not condition:
            self._fail(label, reason)

    def _prove_unsat(self, label: str, mismatches) -> None:
        """按"找反例"证明；只有 UNSAT 表示等价成立，unknown 同样 fail-closed。"""
        mismatches = list(mismatches)
        if not mismatches:
            self._fail(label, "no proof obligations")
        # QF_BV 专用 solver 直接装配 bit-blast + SAT，跳过通用预处理。
        solver = SolverFor("QF_BV")
        solver.set(timeout=self.timeout_ms)
        solver.add(Or(*mismatches))
        result = solver.check()
        if result != unsat:
            self._fail(
                label,
                "raw slice semantics do not match limb algorithm",
                solver_result=str(result),
            )

    def _prove_segment_outputs(
        self,
        state: SMTState,
        segment: Sequence[X86Instruction],
        obligations: Sequence[Tuple[str, Register, object]],
        *,
        label: str,
        prelude: Sequence[Tuple[Register, object]] = (),
    ) -> SMTState:
        """证明一个 raw 小段的 checkpoint 寄存器等于期望表达式。

        obligations 是 (role, reg, expected) 列表；同一 checkpoint 内同一寄存器
        出现两次说明角色重叠（dict 会静默吞掉一个 obligation），直接 reject。

        prelude 是 (reg, expr) 列表，在执行 segment 前预置到寄存器——用于把被
        跳过的非零 const load 替换成 fresh 符号，使 raw 侧乘法读到符号而非常量。
        """
        seen: Dict[Register, str] = {}
        for role, reg, _expected in obligations:
            prior = seen.get(reg)
            if prior is not None:
                self._fail(
                    label,
                    f"checkpoint register overlap: roles {prior} and {role} "
                    f"both use {reg.value}",
                )
            seen[reg] = role

        for reg, expr in prelude:
            state.x86_registers.set_register(reg, expr)
        final = _execute_insns(state, segment)
        for role, reg, expected in obligations:
            self._prove_unsat(
                f"{label} checkpoint {role}={reg.value}",
                (final.x86_registers.get_register(reg) != expected,),
            )

        # 小步归纳：证明过的 checkpoint 用规范表达式继续，避免后续 query 反复展开。
        for _role, reg, expected in obligations:
            final.x86_registers.set_register(reg, expected)
        return final

    def _symbolic_initial_state(self) -> Tuple[SMTState, BitVecVal]:
        """构造 glue 证明的初始状态。

        - R14 取具体基址，让所有 stack 地址都是具体值，array 推理退化为常量索引；
        - stack 域换成完全自由的符号 Array，p/q 的 stack limb 因此是任意符号值。
        """
        state = SMTState()
        r14_base = BitVecVal(0x20000, 64)
        state.x86_registers.set_register(Register.R14, r14_base)
        state.x86_memory = X86MemoryState.from_arrays(
            state.x86_memory.call_engine_mem,
            Array(
                f"glue_stack_mem_{abs(hash(self.label)) & 0xFFFF:x}",
                BitVecSort(64),
                BitVecSort(8),
            ),
            state.x86_memory.evm_mem,
        )
        return state, r14_base

    def _seed_stack_source_limbs(self, state: SMTState, r14_base) -> None:
        """把 stack 来源的 p/q limb 预写成自由符号，降低 byte-array 噪声。"""
        symbolic_by_offset = {}
        for loc in (*self.summary.p_limb_locs, *self.summary.q_limb_locs):
            if not isinstance(loc, StackLimbLocation):
                continue
            if loc.offset not in symbolic_by_offset:
                symbolic_by_offset[loc.offset] = BitVec(
                    f"glue_stack_limb_{abs(hash(self.label)) & 0xFFFF:x}_{loc.offset}",
                    64,
                )
            state.x86_memory = state.x86_memory.store_limb(
                r14_base + BitVecVal(loc.offset, 64),
                symbolic_by_offset[loc.offset],
                domain=MemoryDomain.STACK,
            )

    def _seed_const_source_limbs(self) -> None:
        """给每个非零 const limb 分配 fresh 符号，丢弃其具体值。

        glue 证的是数据流 wiring，与非零常量取值无关；用自由符号证的是更强的
        ∀c 命题（蕴含 c=具体值 的特例）。这让 const 来源的乘法和 register/stack
        来源一样保持 sym×sym 结构，避免 Z3 对 const×sym 的昂贵展开。零值 const
        不入表——它走 _consume_mov_group 零分支、不进 mul，且 _zero_branch_flags
        依赖其具体 0 值，必须保留 BitVecVal。
        """
        for tag, locs in (
            ("p", self.summary.p_limb_locs),
            ("q", self.summary.q_limb_locs),
        ):
            for index, loc in enumerate(locs):
                if isinstance(loc, ConstLimbLocation) and loc.value != 0:
                    self._const_symbols[(tag, index)] = BitVec(
                        f"glue_const_{abs(hash(self.label)) & 0xFFFF:x}_{tag}{index}",
                        64,
                    )

    def _limb_expr(self, tag: str, index: int, loc, state: SMTState):
        """期望侧 limb -> Z3 表达式；非零 const 用 fresh 符号，其余照常。"""
        sym = self._const_symbols.get((tag, index))
        if sym is not None:
            return sym
        if isinstance(loc, ConstLimbLocation):
            return BitVecVal(loc.value, 64)
        return _stack_or_register_limb_expr(loc, state)

    def _consume_mul_group(
        self,
        index: int,
        *,
        add_pairs: int,
        save_carry: bool,
        q_key: Tuple[str, int] | None = None,
        p_key: Tuple[str, int] | None = None,
    ):
        """消费一个 mul 加若干 add/adc 的固定小段。

        返回 (exec_insns, prelude, cursor, lo_reg, hi_reg)。当 q/p load 对应的
        limb 是非零 const（q_key/p_key 命中 _const_symbols）时，仍对该 load 做
        结构断言，但**不执行**它，改为在 prelude 里把目标寄存器预置成该 slot 的
        fresh 符号——这样后续 mul 读到符号而非具体常量，与期望侧对齐。
        """
        insns = self.insns
        cursor = index
        exec_insns: list[X86Instruction] = []
        prelude: list[Tuple[Register, BitVec]] = []

        def step(message: str) -> X86Instruction:
            if cursor >= len(insns):
                self._fail("structure", f"slice ended early: {message}")
            return insns[cursor]

        insn = step("missing q load")
        ops = parse_operands(insn)
        self._require(
            ops.get("dest_reg") == Register.RAX,
            "structure",
            f"expected q load into rax at index {cursor}",
        )
        q_sym = self._const_symbols.get(q_key) if q_key is not None else None
        if q_sym is not None:
            prelude.append((Register.RAX, q_sym))
        else:
            exec_insns.append(insn)
        cursor += 1

        insn = step("missing p load")
        param_ops = parse_operands(insn)
        param_reg = param_ops.get("dest_reg")
        self._require(
            param_reg is not None,
            "structure",
            f"expected p load into register at index {cursor}",
        )
        p_sym = self._const_symbols.get(p_key) if p_key is not None else None
        if p_sym is not None:
            prelude.append((param_reg, p_sym))
        else:
            exec_insns.append(insn)
        cursor += 1

        insn = step("missing mul")
        self._require(
            insn.mnemonic.lower() == "mul"
            and parse_operands(insn).get("dest_reg") == param_reg,
            "structure",
            f"expected mul by param register at index {cursor}",
        )
        exec_insns.append(insn)
        cursor += 1

        for _ in range(add_pairs):
            insn = step("missing add")
            add_ops = parse_operands(insn)
            self._require(
                insn.mnemonic.lower() == "add"
                and add_ops.get("dest_reg") == Register.RAX,
                "structure",
                f"expected add rax at index {cursor}",
            )
            exec_insns.append(insn)
            cursor += 1
            insn = step("missing adc")
            adc_ops = parse_operands(insn)
            self._require(
                insn.mnemonic.lower() == "adc"
                and adc_ops.get("dest_reg") == Register.RDX
                and adc_ops.get("immediate") == 0,
                "structure",
                f"expected adc rdx, 0 at index {cursor}",
            )
            exec_insns.append(insn)
            cursor += 1

        insn = step("missing lo save mov")
        lo_ops = parse_operands(insn)
        self._require(
            insn.mnemonic.lower() == "mov"
            and lo_ops.get("src_reg") == Register.RAX
            and lo_ops.get("dest_reg") is not None,
            "structure",
            f"expected mov reg, rax at index {cursor}",
        )
        lo_reg = lo_ops.get("dest_reg")
        exec_insns.append(insn)
        cursor += 1

        hi_reg = None
        if save_carry:
            insn = step("missing hi save mov")
            hi_ops = parse_operands(insn)
            self._require(
                insn.mnemonic.lower() == "mov"
                and hi_ops.get("src_reg") == Register.RDX
                and hi_ops.get("dest_reg") is not None,
                "structure",
                f"expected mov reg, rdx at index {cursor}",
            )
            hi_reg = hi_ops.get("dest_reg")
            exec_insns.append(insn)
            cursor += 1

        return exec_insns, prelude, cursor, lo_reg, hi_reg

    def _consume_mov_group(self, index: int):
        """消费零值分支里把中间结果直接搬到 result register 的 mov。"""
        if index >= len(self.insns):
            self._fail("structure", "slice ended early: missing zero-branch mov")
        insn = self.insns[index]
        ops = parse_operands(insn)
        self._require(
            insn.mnemonic.lower() == "mov"
            and ops.get("dest_reg") is not None
            and ops.get("src_reg") is not None
            and not ops.get("is_memory"),
            "structure",
            f"expected zero-branch reg-to-reg mov at index {index}",
        )
        return [insn], index + 1, ops.get("dest_reg"), ops.get("src_reg")

    def _prove_result_stores(
        self,
        state: SMTState,
        tail: Sequence[X86Instruction],
        r14_base,
        limbs,
    ) -> None:
        """执行尾部 4 条 result store，证明 stack 上的最终内存值逐 limb 正确。

        这是语义级检查（不是 offset->寄存器结构映射）：即使某个结果寄存器在
        checkpoint 之后被后续段当 tmp 覆盖，这里也会暴露。
        """
        self._require(
            len(tail) == 4,
            "tail",
            f"expected exactly 4 result stores after groups, got {len(tail)}",
        )
        offsets = []
        for insn in tail:
            ops = parse_operands(insn)
            self._require(
                _is_stack_store(insn)
                and ops.get("base_reg") == Register.R14
                and ops.get("memory_size") == 8,
                "tail",
                f"expected R14-based 8-byte stack store, got "
                f"{insn.mnemonic} {insn.op_str}",
            )
            offsets.append(ops.get("offset"))
        self._require(
            tuple(offsets) == self.summary.result_stack_offsets,
            "tail",
            f"store offsets {tuple(offsets)} != summary result offsets "
            f"{self.summary.result_stack_offsets}",
        )

        final = _execute_insns(state, tail)
        for limb_index, (offset, expected) in enumerate(
            zip(self.summary.result_stack_offsets, limbs)
        ):
            stored = final.x86_memory.load_limb(
                r14_base + BitVecVal(offset, 64),
                domain=MemoryDomain.STACK,
            )
            self._prove_unsat(
                f"result store z{limb_index}@{offset}",
                (stored != expected,),
            )

    def run(self) -> None:
        summary = self.summary
        state, r14_base = self._symbolic_initial_state()
        self._seed_stack_source_limbs(state, r14_base)
        # 必须先于 p/q 构造 seed，否则期望侧 _limb_expr 查不到 const 符号。
        self._seed_const_source_limbs()

        # 必须先在未执行的初始状态上读取 p/q：result offsets 会覆盖 p 所在的 slot。
        p = [
            self._limb_expr("p", i, loc, state)
            for i, loc in enumerate(summary.p_limb_locs)
        ]
        q = [
            self._limb_expr("q", i, loc, state)
            for i, loc in enumerate(summary.q_limb_locs)
        ]
        q2_zero, q3_zero, q4_zero = _zero_branch_flags(summary)
        index = 0

        carry0, z0 = _mul64(p[0], q[0])
        segment, prelude, index, z0_reg, carry0_reg = self._consume_mul_group(
            index, add_pairs=0, save_carry=True, q_key=("q", 0), p_key=("p", 0)
        )
        state = self._prove_segment_outputs(
            state,
            segment,
            (("z0", z0_reg, z0), ("carry0", carry0_reg, carry0)),
            label="q1p1",
            prelude=prelude,
        )

        carry0, res1 = _umul_hop(carry0, p[1], q[0])
        segment, prelude, index, res1_reg, carry0_reg = self._consume_mul_group(
            index, add_pairs=1, save_carry=True, q_key=("q", 0), p_key=("p", 1)
        )
        state = self._prove_segment_outputs(
            state,
            segment,
            (("res1", res1_reg, res1), ("carry0", carry0_reg, carry0)),
            label="q1p2",
            prelude=prelude,
        )

        carry0, res2 = _umul_hop(carry0, p[2], q[0])
        segment, prelude, index, res2_reg, carry0_reg = self._consume_mul_group(
            index, add_pairs=1, save_carry=True, q_key=("q", 0), p_key=("p", 2)
        )
        state = self._prove_segment_outputs(
            state,
            segment,
            (("res2", res2_reg, res2), ("carry0", carry0_reg, carry0)),
            label="q1p3",
            prelude=prelude,
        )

        _discarded_carry0, res3 = _umul_hop(carry0, p[3], q[0])
        segment, prelude, index, res3_reg, _ = self._consume_mul_group(
            index, add_pairs=1, save_carry=False, q_key=("q", 0), p_key=("p", 3)
        )
        state = self._prove_segment_outputs(
            state, segment, (("res3", res3_reg, res3),), label="q1p4", prelude=prelude
        )

        if q2_zero:
            z1 = res1
            segment, index, z1_reg, _ = self._consume_mov_group(index)
            state = self._prove_segment_outputs(
                state, segment, (("z1", z1_reg, z1),), label="q2-zero"
            )
        else:
            carry1, z1 = _umul_hop(res1, p[0], q[1])
            segment, prelude, index, z1_reg, carry1_reg = self._consume_mul_group(
                index, add_pairs=1, save_carry=True, q_key=("q", 1), p_key=("p", 0)
            )
            state = self._prove_segment_outputs(
                state,
                segment,
                (("z1", z1_reg, z1), ("carry1", carry1_reg, carry1)),
                label="q2p1",
                prelude=prelude,
            )

            carry1, res2 = _umul_step_x86_order(res2, p[1], q[1], carry1)
            segment, prelude, index, res2_reg, carry1_reg = self._consume_mul_group(
                index, add_pairs=2, save_carry=True, q_key=("q", 1), p_key=("p", 1)
            )
            state = self._prove_segment_outputs(
                state,
                segment,
                (("res2", res2_reg, res2), ("carry1", carry1_reg, carry1)),
                label="q2p2",
                prelude=prelude,
            )

            _discarded_carry1, res3 = _umul_step_x86_order(res3, p[2], q[1], carry1)
            segment, prelude, index, res3_reg, _ = self._consume_mul_group(
                index, add_pairs=2, save_carry=False, q_key=("q", 1), p_key=("p", 2)
            )
            state = self._prove_segment_outputs(
                state,
                segment,
                (("res3", res3_reg, res3),),
                label="q2p3",
                prelude=prelude,
            )

        if q3_zero:
            z2 = res2
            segment, index, z2_reg, _ = self._consume_mov_group(index)
            state = self._prove_segment_outputs(
                state, segment, (("z2", z2_reg, z2),), label="q3-zero"
            )
        else:
            carry2, z2 = _umul_hop(res2, p[0], q[2])
            segment, prelude, index, z2_reg, carry2_reg = self._consume_mul_group(
                index, add_pairs=1, save_carry=True, q_key=("q", 2), p_key=("p", 0)
            )
            state = self._prove_segment_outputs(
                state,
                segment,
                (("z2", z2_reg, z2), ("carry2", carry2_reg, carry2)),
                label="q3p1",
                prelude=prelude,
            )

            _discarded_carry2, res3 = _umul_step_x86_order(res3, p[1], q[2], carry2)
            segment, prelude, index, res3_reg, _ = self._consume_mul_group(
                index, add_pairs=2, save_carry=False, q_key=("q", 2), p_key=("p", 1)
            )
            state = self._prove_segment_outputs(
                state,
                segment,
                (("res3", res3_reg, res3),),
                label="q3p2",
                prelude=prelude,
            )

        if q4_zero:
            z3 = res3
            segment, index, z3_reg, _ = self._consume_mov_group(index)
            state = self._prove_segment_outputs(
                state, segment, (("z3", z3_reg, z3),), label="q4-zero"
            )
        else:
            _discarded_carry3, z3 = _umul_hop(res3, p[0], q[3])
            segment, prelude, index, z3_reg, _ = self._consume_mul_group(
                index, add_pairs=1, save_carry=False, q_key=("q", 3), p_key=("p", 0)
            )
            state = self._prove_segment_outputs(
                state, segment, (("z3", z3_reg, z3),), label="q4p1", prelude=prelude
            )

        self._prove_result_stores(
            state, self.insns[index:], r14_base, (z0, z1, z2, z3)
        )


def prove_mul_slice_refines_summary(
    summary: MulSummary,
    slice_insns: Sequence[X86Instruction],
    *,
    timeout_ms: int = 10_000,
    label: str | None = None,
) -> None:
    """对一次 matcher 命中跑端到端 glue 证明；失败 raise MulProofError。"""
    proof = _MulSliceProof(
        summary,
        slice_insns,
        timeout_ms=timeout_ms,
        label=label or f"mul@0x{summary.entry_addr:x}",
    )
    proof.run()


# 进程内证明缓存。discover 在主线程 X86Program.to_z3 中一次性发生（path-pair
# 并行不重跑 discover），无需加锁。成功是语义事实，可按 semantic key 跨 timeout
# 复用；失败可能由 timeout 预算导致，缓存 key 额外带 timeout_ms。
_PROOF_SUCCESS_CACHE: set = set()
_PROOF_FAILURE_CACHE: dict = {}


def clear_proof_cache() -> None:
    _PROOF_SUCCESS_CACHE.clear()
    _PROOF_FAILURE_CACHE.clear()


def _semantic_cache_key(
    summary: MulSummary,
    slice_insns: Sequence[X86Instruction],
) -> tuple:
    return (
        b"".join(insn.bytes for insn in slice_insns),
        summary.p_limb_locs,
        summary.q_limb_locs,
        summary.result_stack_offsets,
        summary.clobber_registers,
    )


def prove_mul_slice_cached(
    summary: MulSummary,
    slice_insns: Sequence[X86Instruction],
    *,
    timeout_ms: int = 10_000,
    label: str | None = None,
) -> str:
    """带缓存的 per-hit 证明。

    返回 ``"proven"``（真实跑了 solver 并成功）或 ``"cache_hits"``（成功缓存
    命中）；失败 raise MulProofError，失败缓存命中时异常带 ``from_cache=True``。
    """
    key = _semantic_cache_key(summary, slice_insns)
    if key in _PROOF_SUCCESS_CACHE:
        return "cache_hits"

    failure_key = key + (timeout_ms,)
    cached_failure = _PROOF_FAILURE_CACHE.get(failure_key)
    if cached_failure is not None:
        raise MulProofError(
            cached_failure.entry_addr,
            cached_failure.label,
            cached_failure.reason,
            cached_failure.solver_result,
            from_cache=True,
        )

    try:
        prove_mul_slice_refines_summary(
            summary, slice_insns, timeout_ms=timeout_ms, label=label
        )
    except MulProofError as exc:
        # Keep error data, not the traceback's solvers and execution states.
        _PROOF_FAILURE_CACHE[failure_key] = type(exc)(
            exc.entry_addr, exc.label, exc.reason, exc.solver_result, from_cache=exc.from_cache)
        raise
    _PROOF_SUCCESS_CACHE.add(key)
    return "proven"
