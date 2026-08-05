"""EVM↔x86 无符号除法/取余的 refinement 提速桥接（生产 + 测试共享）。

SDIV/SMOD（及任何先取负再除的路径）里，EVM 侧与 x86 侧对**同一个**无符号除法
的建模在 AST 上不一致：取负 `0-x` 的 limb 链、holiman 分段 ITE 的展开形式、Z3
`bvudiv` vs simplify 后 `bvudiv_i` 等都会让两侧的除法子表达式 syntactic 不同。
要证两个 256-bit `bvudiv` 相等，Z3 需要 bit-blast 而 unknown/超时。

这里提供一个**已验证的桥接**：在给定约束（path condition + assumptions）下，逐对
配对两侧的除法子表达式，**先证它们的实参恒等**，再注入 `evm_div == x86_div` 等式让
solver 跳过 bit-blast。配对/验证 fail-closed：任何歧义或验证不通过都不注入桥接，
绝不在未证实参恒等时加 `==` 约束（那会越界约束、藏住真实 counterexample）。

桥接是**恒真 + soundness 中性**的纯提速 hint：同一无符号除法函数、同实参 ⟹ 同结果。
"""

from collections import defaultdict

from z3 import Or, SolverFor, unsat


# EVM 与 x86 侧语义里同一无符号除法/取余的不同建模 decl，按语义类别归并以便配对。
# bvudiv（Z3_OP_BUDIV）与 bvudiv_i（Z3_OP_BUDIV_I，simplify 后的 interpreted 形式）
# 语义完全等价（含 div-by-0），归同一类；urem 同理；holiman_* 是各自的未解释函数。
DIV_BRIDGE_CATEGORIES = {
    "bvudiv": "udiv",
    "bvudiv_i": "udiv",
    "bvurem": "urem",
    "bvurem_i": "urem",
    "holiman_udiv": "holiman_udiv",
    "holiman_udivrem": "holiman_udivrem",
}

# 桥接验证（证实参恒等）的默认预算。单个 query 通常 ≤1s；留余量避免满负载抖动。
_DEFAULT_VERIFY_TIMEOUT_MS = 8_000


def collect_div_subexprs(exprs):
    """收集 exprs（单个或可迭代）里的 div/rem 子表达式，按 (category, size) 分组去重。

    **必须用显式栈**：这里的表达式上千层嵌套，递归版在 Python 默认上限 1000 处抛
    RecursionError。调高 recursionlimit 不是修法——那只盖住 pytest，CLI 照样崩。
    """
    grouped = defaultdict(list)
    seen = set()

    iterable = exprs if isinstance(exprs, (list, tuple)) else (exprs,)
    stack = list(iterable)
    while stack:
        node = stack.pop()
        node_id = node.get_id()
        if node_id in seen:
            continue
        seen.add(node_id)
        category = DIV_BRIDGE_CATEGORIES.get(node.decl().name())
        if category is not None:
            grouped[(category, node.size())].append(node)
        stack.extend(node.arg(index) for index in range(node.num_args()))
    return grouped


def verified_div_bridges(
    evm_exprs,
    x86_exprs,
    constraint,
    assumptions=(),
    ctx=None,
    verify_timeout_ms=_DEFAULT_VERIFY_TIMEOUT_MS,
):
    """返回一组已验证的 `evm_div == x86_div` 桥接（fail-closed）。

    对每个 (category, size)：仅当两侧都恰好唯一、实参个数一致、且其实参在
    constraint + assumptions 下可证逐参相等（验证 solver 返回 unsat）时，才加入桥接。
    任何歧义/验证非 unsat（含 unknown/超时）都跳过——绝不在未证实参恒等时注入 `==`。

    Args:
        evm_exprs / x86_exprs: 两侧待比较的 z3 表达式（单个或可迭代）。
        constraint: 桥接成立的前提（如 path condition）；验证时一并加入。
        assumptions: 顶层无损先验（如 CALLDATALOAD hi-192==0、借位链 lemma）。
        ctx: z3 Context（并行 worker 用独立 context 时必须传，保证 verifier solver
             与待验证 AST 同 context，避免跨 context 混用）。
        verify_timeout_ms: 每对桥接验证的预算。

    Returns:
        list[BoolRef]：可作为恒真 assumption 加入主 solver 的桥接等式。
    """
    x86_groups = collect_div_subexprs(x86_exprs)
    evm_groups = collect_div_subexprs(evm_exprs)

    bridges = []
    for key in set(x86_groups) & set(evm_groups):
        x86_nodes = x86_groups[key]
        evm_nodes = evm_groups[key]
        if len(x86_nodes) != 1 or len(evm_nodes) != 1:
            continue
        x86_div, evm_div = x86_nodes[0], evm_nodes[0]
        if x86_div.num_args() != evm_div.num_args():
            continue
        args_differ = Or(
            *[x86_div.arg(i) != evm_div.arg(i) for i in range(x86_div.num_args())]
        )
        verifier = (
            SolverFor("QF_AUFBV", ctx=ctx) if ctx is not None else SolverFor("QF_AUFBV")
        )
        verifier.set("timeout", verify_timeout_ms)
        for assumption in assumptions:
            verifier.add(assumption)
        verifier.add(constraint)
        verifier.add(args_differ)
        # unsat ⟺ 在该约束下实参必相等 ⟹ 同无符号除法函数同输入 ⟹ 结果相等，桥接 sound。
        if verifier.check() == unsat:
            bridges.append(x86_div == evm_div)

    return bridges
