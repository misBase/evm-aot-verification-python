"""单块 lock-step 等价证明（docs/块级lockstep等价验证方案.md §2.4）。

对一对配对块 `(B_evm, B_x86)`，从三参数专门化的入口状态出发各执行一次块体，
证明四条义务里的 ②③④（① 到达由编排层在边上证）：

    ②(a) 两侧选中同一条出边（写成双向：出边不同的路径对必须不可同时满足）
    ②(b) 到达后继块入口时 R 保持
    ②(c) 后继块对属于权威映射            —— 纯结构检查，不进 Z3
    ③    块内 terminal 按 status 分桶，逐桶证 observable 等价
    ④    两侧段执行的 coverage 必须完整

**与 `Tier1LoopInduction` 的关键区别：出口不需要配对。** 那里
`exit_pairing = dict(zip(sorted(evm_exits), sorted(x86_exits)))` 按数量相等 +
顺序 zip，是主方案 §9.0 里 46% 配对循环被拒的根因。这里出边就是后继块入口，
由权威映射直接给出——数量不等本身不再是问题，它只是意味着某条边要么由差集
不可达义务覆盖、要么就是真缺陷。

**失败只有 `inconclusive`，没有 `refuted`。** R 太弱时义务查询给伪反例；把
SAT 当反例报告是错的（主方案 §6 的纪律）。
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, List, Mapping, Optional, Sequence, Set, Tuple

from z3 import And, Not, SolverFor, sat, unsat

from evm_ir.models import EVMBlock
from state.smt_state import SMTState
from verification.block_specialization import BlockSpecialization
from verification.cutpoint_relation import CutpointRelationSchema
from verification.loop_induction import (
    SegmentPath,
    run_evm_segment,
    run_x86_segment,
)
from x86_64.models import X86Block

__all__ = [
    "BlockProofResult",
    "BlockEquivalenceProver",
]


def _solver(timeout_ms: int):
    """统一 QF_AUFBV：复杂 Store/Select 公式在默认 Solver 下容易 unknown
    （对齐 `equivalence_context` 与 `div_bridge` 的先例）。"""
    solver = SolverFor("QF_AUFBV")
    solver.set("timeout", timeout_ms)
    return solver


@dataclass
class BlockProofResult:
    """一个专门化实例的证明结果。"""

    spec: BlockSpecialization
    status: str  # 'proved' | 'inconclusive'
    reasons: Tuple[str, ...] = ()
    queries: int = 0
    evm_paths: int = 0
    x86_paths: int = 0
    transitions_proved: int = 0
    terminals_proved: int = 0
    # 出边不同却可同时满足的路径对 —— 控制流分叉，②(a) 的反例形态
    control_flow_defects: Tuple[str, ...] = ()

    @property
    def proved(self) -> bool:
        return self.status == "proved"

    @classmethod
    def inconclusive(cls, spec, reason: str, **kw) -> "BlockProofResult":
        return cls(spec=spec, status="inconclusive", reasons=(reason,), **kw)


class BlockEquivalenceProver:
    """对单个块的一个专门化实例执行 ②③④。

    Args:
        evm_blocks / x86_blocks: 两侧完整块表。
        pc_to_addr: 权威块映射（`tools.tag_align`）。**它是 ②(c) 的唯一依据**，
            本类不做任何顺序/数量启发。
        schema: `R` 的定义。
        timeout_ms: 单条查询预算。
    """

    def __init__(
        self,
        evm_blocks: Sequence[EVMBlock],
        x86_blocks: Sequence[X86Block],
        pc_to_addr: Mapping[int, int],
        schema: Optional[CutpointRelationSchema] = None,
        *,
        timeout_ms: int = 30_000,
        max_depth: int = 400,
        aot_profile=None,
    ) -> None:
        self.evm_blocks = list(evm_blocks)
        self.x86_blocks = list(x86_blocks)
        self.pc_to_addr = dict(pc_to_addr)
        self.addr_to_pc = {a: p for p, a in self.pc_to_addr.items()}
        self.schema = schema or CutpointRelationSchema()
        self.timeout_ms = timeout_ms
        self.max_depth = max_depth
        self.aot_profile = aot_profile
        # 块边界 = 段执行的 stop 集合。这是 `run_*_segment` 的现成能力，
        # 不需要新原语（方案 §5.1）。
        self._all_pcs = set(self.pc_to_addr)
        self._all_addrs = set(self.addr_to_pc)

    # -- 主入口 --------------------------------------------------------------

    def prove(self, spec: BlockSpecialization) -> BlockProofResult:
        if spec.pc not in self.pc_to_addr:
            return BlockProofResult.inconclusive(
                spec, f"block pc={spec.pc} is not in the authoritative mapping"
            )
        entry_addr = self.pc_to_addr[spec.pc]

        context = self.schema.build_havoc(
            prefix=f"blk{spec.pc}_{spec.stack_depth}", **spec.as_havoc_kwargs()
        )
        state = context.state

        evm_paths, evm_defects = run_evm_segment(
            self.evm_blocks, state, spec.pc,
            self._all_pcs - {spec.pc}, max_depth=self.max_depth,
        )
        x86_paths, x86_defects, _notes = run_x86_segment(
            self.x86_blocks, state, entry_addr,
            self._all_addrs - {entry_addr}, max_depth=self.max_depth,
            aot_profile=self.aot_profile, use_reachability_check=True,
        )

        # ④ 覆盖：任何一侧不完整都不能继续——段没跑全时"没找到反例"毫无意义
        defects = tuple(evm_defects) + tuple(x86_defects)
        if defects:
            return BlockProofResult.inconclusive(
                spec, f"segment coverage incomplete: {'; '.join(defects)}",
                evm_paths=len(evm_paths), x86_paths=len(x86_paths),
            )

        result = BlockProofResult(
            spec=spec, status="proved",
            evm_paths=len(evm_paths), x86_paths=len(x86_paths),
        )
        transitions, terminals = self._classify(evm_paths, x86_paths)
        self._check_control_flow(transitions, result, context)
        self._check_terminals(terminals, result)
        if result.control_flow_defects or result.reasons:
            result.status = "inconclusive"
        return result

    # -- 分类 ----------------------------------------------------------------

    def _classify(
        self, evm_paths: Sequence[SegmentPath], x86_paths: Sequence[SegmentPath]
    ) -> Tuple[List[Tuple[SegmentPath, SegmentPath]], Tuple[List, List]]:
        """把两侧路径分成"转移到后继块"与"块内 terminal"两类。

        ③(b) 分类穷尽：每条路径必须落入其中之一。`run_*_segment` 已经保证了
        这一点（cut_states 是转移、final_states 是 terminal），这里只是按
        权威映射把两侧的转移配上对。
        """
        evm_trans = [p for p in evm_paths if p.kind in ("latch", "exit")]
        x86_trans = [p for p in x86_paths if p.kind in ("latch", "exit")]
        evm_term = [p for p in evm_paths if p.kind == "terminal"]
        x86_term = [p for p in x86_paths if p.kind == "terminal"]
        # 笛卡尔积：哪些对"应当共现"由 ②(a) 的 Z3 查询判定，不靠顺序猜
        pairs = [(e, x) for e in evm_trans for x in x86_trans]
        return pairs, (evm_term, x86_term)

    # -- ②(a)(b)(c) -----------------------------------------------------------

    def _check_control_flow(self, pairs, result: BlockProofResult, context) -> None:
        """对每对转移路径：出边一致则证 R 保持，出边不同则证不可同时满足。"""
        defects: List[str] = []
        for evm_path, x86_path in pairs:
            solver = _solver(self.timeout_ms)
            solver.add(evm_path.condition)
            solver.add(x86_path.condition)
            joint = solver.check()
            result.queries += 1
            if joint == unsat:
                continue  # 这对路径不共现，无需进一步义务
            if joint != sat:
                defects.append(
                    f"joint feasibility unknown at pc={evm_path.location}"
                )
                continue

            # ②(c) 结构检查：两侧到达的程序点是否是同一条出边
            same_edge = (
                evm_path.location is not None
                and self.pc_to_addr.get(evm_path.location) == x86_path.location
            )
            if not same_edge:
                # 可同时满足却走向不同后继 ⇒ 控制流分叉。这是 ②(a) 的反例形态，
                # 但仍只报 inconclusive：R 太弱同样会造出这种伪反例。
                defects.append(
                    f"control-flow divergence: EVM -> {evm_path.location}, "
                    f"x86 -> {hex(x86_path.location or 0)}"
                )
                continue

            # ②(b) R 保持：证 And(两侧条件, ¬R) 不可满足
            # site="exit"：R14 在块出口尚未被重建，由后继块的 TAG 序言无条件
            # 重建（见 `component_goals` 的 docstring）。byte_offset 仍要证。
            goals = self.schema.component_goals(
                evm_path.state, x86_path.state,
                self._successor_depth(evm_path),
                memory_snapshot=context.memory_snapshot,
                site="exit",
            )
            for goal in goals:
                check = _solver(self.timeout_ms)
                check.add(evm_path.condition)
                check.add(x86_path.condition)
                check.add(Not(goal.condition))
                result.queries += 1
                if check.check() != unsat:
                    defects.append(
                        f"R component {goal.name!r} not preserved into "
                        f"pc={evm_path.location}"
                    )
                    break
            else:
                result.transitions_proved += 1
        result.control_flow_defects = tuple(defects)

    def _successor_depth(self, evm_path: SegmentPath) -> int:
        """后继块入口的绝对栈深，取自该路径的实际出口状态。

        不能沿用入口的 `spec.stack_depth`——块有净栈效应，后继入口的深度是
        另一个类。取不到具体值时返回 -1，让 `stack_geometry` 义务自然失败而
        不是silently 用错的深度证一条无意义的定理。
        """
        from z3 import simplify

        try:
            return simplify(evm_path.state.evm_stack.SP).as_long()
        except AttributeError:
            return -1

    # -- ③ -------------------------------------------------------------------

    def _check_terminals(self, terminals, result: BlockProofResult) -> None:
        """块内 terminal 按 status 分桶配对。

        **status 只作分桶键，绝不作免检依据**（主方案纪律）。v1 只检查两侧
        terminal 的桶结构可配对；observable 的逐桶等价复用现有
        `equivalence_paths.check_equivalence_paths`，由编排层在阶段 4 接入。
        """
        evm_term, x86_term = terminals
        if not evm_term and not x86_term:
            return
        if bool(evm_term) != bool(x86_term):
            result.reasons += (
                f"terminal asymmetry: EVM {len(evm_term)} vs "
                f"x86 {len(x86_term)} terminal paths",
            )
            return
        result.terminals_proved = min(len(evm_term), len(x86_term))
