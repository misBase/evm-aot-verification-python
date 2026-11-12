"""P2 验收基准：Compound CErc20 string 存储循环的 Tier 1 锁步归纳。

目标循环（docs/循环处理增强方案.md §7 验收基准）：
- EVM pc=0x739：`DUP SLOAD DUP MSTORE SWAP PUSH ADD SWAP PUSH ADD DUP DUP
  GT JUMPI` 单块自环——name/symbol getter 的动态 string 存储读循环，
  trip count = ceil(len/32)，len 为符号值（有界展开永远无法封闭）。
- x86 0x107a2：对应编译产物（TAG 序言 + SLOAD host 桥 + 内存扩展逻辑
  + MSTORE bswap 写 + 4-limb GT 比较链，28 个基本块）。

归纳步 ② 在 havoc 后的循环头 cutpoint 上证明：任意第 n 轮到达时若 R
成立，则一轮之后 R 保持（回边/出口），分支决策两侧一致——**符号 bound
被归纳吞掉，不调 max_depth**。

结论**不带** no-OOG/no-stack-limit envelope：该 envelope 已取消（§4.3——
两侧 gas/OOG/status 现已对照）。x86 侧 TAG 序言的错误终态不再被丢弃，而是
作为 terminal outcome 进入 ②(d) 与 EVM 侧对应终态配对证明。本文件的断言
直接盯这一点：错误路径若又被静默排除，验收基准就退回了 envelope 时代。

**运行方式（显式 opt-in）**：本测试实测约 8–9 分钟（约 170 条 Z3 查询，
单条 budget 120s），默认 skip 以免拖垮常规 pytest/CI::

    RUN_LOOP_INDUCTION_ACCEPTANCE=1 poetry run pytest \
        tests/integration/test_loop_induction_cerc20.py
"""

import os
import re

import pytest

_CERC20_JSON = os.path.join(
    os.path.dirname(__file__), "..", "data", "ext_contracts",
    "compound_cerc20", "CErc20.json",
)
_CERC20_HEX = os.path.join(
    os.path.dirname(__file__), "..", "data", "ext_contracts",
    "compound_cerc20", "CErc20.hex",
)

pytestmark = [
    pytest.mark.skipif(
        not os.environ.get("RUN_LOOP_INDUCTION_ACCEPTANCE"),
        reason=(
            "~9 min acceptance run; set RUN_LOOP_INDUCTION_ACCEPTANCE=1 "
            "to enable"
        ),
    ),
    pytest.mark.skipif(
        not (os.path.exists(_CERC20_JSON) and os.path.exists(_CERC20_HEX)),
        reason="CErc20 fixture missing",
    ),
]

# 归纳步失败时逐分量复查的单条预算。刻意比 checker 的 timeout_ms 小：诊断只是
# 报告用，不该把一次失败拖成十几分钟；代价是这里的 `unknown` 可能只是预算不够，
# 报告里会标明预算，别把它当成"全预算下也解不动"。
_DIAGNOSTIC_TIMEOUT_MS = 20000

# `_verify_path_matrix` 的失败原因里嵌的配对标签，形如 `evm#0(exit)/x86#1(exit)`。
_PAIR_LABEL = re.compile(r"evm#(\d+)\((\w+)\)/x86#(\d+)\((\w+)\)")


def _loop_exits(loop, succs):
    out = set()
    for node in loop.body:
        for target in succs.get(node, []):
            if target not in loop.body:
                out.add(target)
    return sorted(out)


# ---------------------------------------------------------------------------
# 失败诊断
#
# `check_inductive_step` 只报"这一对 R 不保持"：`_prove` 把十几个分量并成一条
# `Not(And(...))` 交给 Z3，失败信息里没有分量名。而"哪个分量失守、是 sat 还是
# unknown"正是唯一能指导修复的信息（sat=关系式真的不成立，unknown=解不动，
# 两者的修法完全不同）。因此失败时重跑一次段执行并逐条查。
#
# 诊断本身**自证可信**：重建的那一对若在完整前提下把义务证成 unsat，说明下标
# 没对上（`_verify_path_matrix` 的过滤逻辑变了），此时如实报告"复现不出"，而
# 不是指着一个可能无关的分量。
# ---------------------------------------------------------------------------


def _rebuild_paths(checker):
    """按 `check_inductive_step` 的做法重跑一轮段执行，返回 (evm 路径, x86 路径,
    assumptions)。cut state 必须重新构造：路径状态与 `_relation_context` 必须
    出自同一次 havoc，否则逐分量查的是两组互不相干的符号。"""
    from verification.loop_induction import run_evm_segment, run_x86_segment

    cut_state = checker.build_cut_state()
    evm_paths, _ = run_evm_segment(
        checker.evm_blocks, cut_state.copy(), checker.evm_header,
        {checker.evm_header, *checker.evm_exits}, max_depth=checker.max_depth,
    )
    x86_paths, _, _ = run_x86_segment(
        checker.x86_blocks, cut_state.copy(), checker.x86_header,
        {checker.x86_header, *checker.x86_exits}, max_depth=checker.max_depth,
        aot_profile=checker.aot_profile,
    )
    assumptions = list(getattr(cut_state, "assumptions", None) or [])
    assumptions.extend(checker._invariant_premises(cut_state))
    return evm_paths, x86_paths, assumptions


def _feasible(paths, base, timeout_ms):
    """复现 `_verify_path_matrix` 的可行性预过滤——失败标签里的下标是**过滤后**
    的下标，不还原这一步就会指向错误的路径。预算必须与 checker 一致：预算变小会
    把 unsat 变成 unknown，保留集合随之改变，下标再次错位。"""
    from verification.loop_induction import _make_solver
    from z3 import And, unsat

    kept = []
    for path in paths:
        solver = _make_solver(timeout_ms)
        solver.add(And(base, path.condition))
        if solver.check() != unsat:
            kept.append(path)
    return kept


def _named_goals(checker, evm_path, x86_path):
    """重建一对路径的证明义务并逐条命名，与 `check_inductive_step._goals` 同源。

    terminal 对走 ②(d) 的可观测量清单（无具名分量，按序号标）；latch/exit 对走
    R 的具名分量 + 域约束 + 结构前提。

    Returns:
        ``(具名义务列表, None)``；结构前提在 Python 层当场违例时返回
        ``([], 原因)``——那不是求解结果，不该混进 Z3 verdict 里报。
    """
    from verification.loop_induction import terminal_observable_conditions

    if evm_path.kind == "terminal":
        return [
            (f"terminal_observable#{i}", condition)
            for i, condition in enumerate(terminal_observable_conditions(
                evm_path.state, x86_path.state, cut_mem0=checker._cut_mem0,
                compare_gas=checker.compare_terminal_gas,
            ))
        ], None

    named = [
        (goal.name, goal.condition)
        for goal in checker.relation_schema.component_goals(
            evm_path.state, x86_path.state, checker.stack_depth,
            context=checker._relation_context,
        )
    ]
    # `_domain_goals` 把两侧域约束拼成一条列表，这里分侧调同一个谓词：报告要能
    # 指出破的是哪一侧（"x86 侧 MSize 跨出 4MiB" 与 EVM 侧跨出的修法并不相同）。
    context = checker._relation_context
    predicate = context.domain_predicate if context is not None else None
    if predicate is None:
        named += [
            (f"domain#{i}", condition)
            for i, condition in enumerate(
                checker._domain_goals(evm_path.state, x86_path.state)
            )
        ]
    else:
        for side, state in (("evm", evm_path.state), ("x86", x86_path.state)):
            named += [
                (f"domain[{side}]#{i}", condition)
                for i, condition in enumerate(predicate(state))
            ]
    site = "latch_reentry" if evm_path.kind == "latch" else "exit_edge"
    structural, defect = checker._structural_goals(
        evm_path.state, x86_path.state, site
    )
    if structural is None:
        return [], f"structural[{site}]: {defect}"
    named += [
        (f"structural[{site}]#{i}", condition)
        for i, condition in enumerate(structural)
    ]
    if checker.extra_invariant is not None:
        named += [
            (f"extra_invariant#{i}", condition)
            for i, condition in enumerate(
                checker.extra_invariant(evm_path.state, x86_path.state)
            )
        ]
    return named, None


def _component_verdicts(checker, result):
    """把 inconclusive 结论还原成「哪个分量、什么 verdict」的报告行。"""
    from common.store_forwarding import forward_selects
    from verification.loop_induction import _make_solver
    from z3 import And, BoolVal, Not, simplify, unsat

    reason = result.reasons[0] if result.reasons else ""
    match = _PAIR_LABEL.search(reason)
    if match is None:
        # 失败不在配对矩阵上（结构预检 / 段缺陷 / 空洞守卫），没有分量可拆。
        return ["  逐分量复查: 跳过（失败原因不含配对标签，非 R 义务失败）"]

    evm_index, evm_kind = int(match.group(1)), match.group(2)
    x86_index, x86_kind = int(match.group(3)), match.group(4)
    evm_paths, x86_paths, assumptions = _rebuild_paths(checker)
    base = And(BoolVal(True), *assumptions)
    evm_paths = _feasible(evm_paths, base, checker.timeout_ms)
    x86_paths = _feasible(x86_paths, base, checker.timeout_ms)
    if evm_index >= len(evm_paths) or x86_index >= len(x86_paths):
        return [
            f"  逐分量复查: 复现不出（重建后 evm {len(evm_paths)} 条 / "
            f"x86 {len(x86_paths)} 条，下标 {evm_index}/{x86_index} 越界）"
        ]

    evm_path, x86_path = evm_paths[evm_index], x86_paths[x86_index]
    if (evm_path.kind, x86_path.kind) != (evm_kind, x86_kind):
        # 下标对上了但路径种类没对上 ⇒ 重建的不是同一对，别指着无关分量。
        return [
            f"  逐分量复查: 复现不出（下标 {evm_index}/{x86_index} 重建出 "
            f"{evm_path.kind}/{x86_path.kind}，失败标签是 {evm_kind}/{x86_kind}）"
        ]

    named, defect = _named_goals(checker, evm_path, x86_path)
    if defect is not None:
        # 结构前提在 Python 层就违例，根本没走到求解——这本身就是结论。
        return [f"  逐分量复查 evm#{evm_index}/x86#{x86_index}: {defect}"]

    header = (
        f"  逐分量复查 evm#{evm_index}({evm_path.kind})/"
        f"x86#{x86_index}({x86_path.kind})"
        f"（{len(named)} 条义务，单条预算 {_DIAGNOSTIC_TIMEOUT_MS} ms，只列非 unsat）:"
    )
    lines = [header]

    # 自证：整体义务若在这里反而 unsat，说明重建的不是失败的那一对。
    whole = _make_solver(_DIAGNOSTIC_TIMEOUT_MS)
    whole.add(base, evm_path.condition, x86_path.condition)
    whole.add(Not(And(*[
        simplify(forward_selects(condition)) for _name, condition in named
    ])))
    if whole.check() == unsat:
        return [header, (
            "    ** 复现不出：重建的这一对在完整前提下 unsat（义务成立）。"
            "下标很可能对不上——诊断代码需与 _verify_path_matrix 的过滤逻辑重新对齐 **"
        )]

    offenders = 0
    for name, condition in named:
        solver = _make_solver(_DIAGNOSTIC_TIMEOUT_MS)
        solver.add(base, evm_path.condition, x86_path.condition)
        solver.add(Not(simplify(forward_selects(condition))))
        verdict = solver.check()
        if verdict != unsat:
            lines.append(f"    {name:32s} {verdict}")
            offenders += 1
    if offenders == 0:
        lines.append(
            "    （逐条全 unsat，但合取不成立：分量之间存在耦合，"
            "或诊断预算不足以复现——加大 _DIAGNOSTIC_TIMEOUT_MS 再看）"
        )
    return lines


def _failing_obligation_lines(result):
    """失败义务本身的每片 verdict（sat=关系式不成立，unknown=解不动）。"""
    if not result.queries:
        return ["  失败义务: （无查询记录）"]
    last_label = result.queries[-1][0]
    prefix = last_label.rsplit(" [", 1)[0]
    lines = [f"  失败义务: {prefix}"]
    for label, verdict in result.queries:
        if label.startswith(prefix):
            lines.append(f"    {label[len(prefix):].strip() or '(无切片标签)'}"
                         f"  {verdict}")
    return lines


def _failure_report(checker, result):
    """assert 的失败消息。只在断言失败时才会被求值（Python 语义），故可以昂贵。"""
    lines = [
        "CErc20 string 循环归纳步未证成（验收基准 1，docs/循环处理增强方案.md §8）",
        f"  status : {result.status}",
    ]
    lines += [f"  reason : {reason}" for reason in result.reasons[:3]]
    lines += _failing_obligation_lines(result)
    try:
        lines += _component_verdicts(checker, result)
    except Exception as exc:  # noqa: BLE001
        # 诊断只是报告的增值部分。它自己炸了不能把"归纳步没证成"这个真结论
        # 盖成一个莫名其妙的异常——那样失败就不"红得清楚"了。
        lines.append(f"  逐分量复查: 诊断自身抛错 {type(exc).__name__}: {exc}")
        lines.append(f"  queries tail: {result.queries[-6:]}")
    lines.append(f"  查询总数: {len(result.queries)}")
    return "\n".join(lines)


def test_cerc20_string_loop_inductive_step_proved():
    from evm_ir.json_parser import load_ir_from_json
    from x86_64.cfg import identify_basic_blocks
    from x86_64.disassembler import disassemble_hex
    from verification.loop_induction import Tier1LoopInduction
    from verification.loop_pairing import (
        analyze_evm_blocks,
        analyze_x86_blocks,
        build_evm_cfg,
        build_x86_cfg,
    )

    evm_blocks = load_ir_from_json(_CERC20_JSON).blocks
    hex_str = open(_CERC20_HEX).read().strip()
    x86_blocks = identify_basic_blocks(disassemble_hex(hex_str, base_addr=0))

    evm_succs, _ = build_evm_cfg(evm_blocks)
    x86_succs, _ = build_x86_cfg(x86_blocks)
    evm_analysis, _ = analyze_evm_blocks(evm_blocks)
    x86_analysis, _ = analyze_x86_blocks(x86_blocks)

    evm_loop = next(l for l in evm_analysis.loops if l.header == 0x739)
    x86_loop = next(l for l in x86_analysis.loops if l.header == 0x107A2)

    checker = Tier1LoopInduction(
        evm_blocks,
        x86_blocks,
        evm_header=0x739,
        x86_header=0x107A2,
        evm_exits=_loop_exits(evm_loop, evm_succs),
        x86_exits=_loop_exits(x86_loop, x86_succs),
        stack_depth=3,  # IR block min_depth：循环体触碰的栈窗口
        timeout_ms=120000,
        evm_body=set(evm_loop.body),
    )
    result = checker.check_inductive_step()

    assert result.proved, _failure_report(checker, result)
    # envelope 已取消：x86 侧 TAG 错误终态**没有**被排除，而是作为 terminal
    # outcome 参与配对证明。段说明里必须留下这条记录——它没了就说明错误路径
    # 又被静默丢弃，那是退回 envelope 的假绿。
    assert any(
        "proved as a paired terminal outcome" in reason
        for reason in result.reasons
    ), f"未见错误终态的配对记录，疑似退回 envelope 排除: {result.reasons[:5]}"
    # 且这些终态确实被 ②(d) 证过（光有说明不算——义务得真的发出去）
    assert any("②(d) terminal" in label for label, _ in result.queries)
    # ②(b) 回边 R 保持、②(c) 出口 R 保持都确实被证明过（非空洞）
    assert any("②(b)" in label for label, _ in result.queries)
    assert any("②(c)" in label for label, _ in result.queries)
