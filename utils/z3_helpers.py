"""
Z3 表达式分析辅助工具。

提供用于分析、解析和轻量结构化遍历 Z3 表达式的通用 helper。
"""

from typing import List, Tuple, Optional
from z3 import BitVec, BitVecVal, BitVecNumRef, is_const, is_bv, And, Not, simplify
from dataclasses import dataclass


@dataclass
class JumpTargetAnalysis:
    """跳转目标分析结果。"""
    is_static: bool  # 是否为静态跳转
    targets: List[Tuple[int, Optional[object]]]  # (target_pc, condition) 列表
    # 对于常量：targets = [(42, None)]
    # 对于 If 表达式：targets = [(target1, condition1), (target2, condition2)]


def is_bv_const_value(expr: BitVec) -> bool:
    """检查 BitVec 表达式是否为常量值（BitVecVal）。"""
    return isinstance(expr, BitVecNumRef)


def get_bv_const_value(expr: BitVec) -> Optional[int]:
    """从 BitVecVal 中提取整数值。"""
    if is_bv_const_value(expr):
        return expr.as_long()
    return None


def get_simplified_bv_const_value(expr) -> Optional[int]:
    """先 simplify，再从 BitVecVal 中提取整数值。"""
    try:
        simplified = simplify(expr)
    except Exception:
        simplified = expr
    return get_bv_const_value(simplified)


def collect_and_conjuncts(expr):
    """把一个 BoolRef 展平成它的 And-conjunct 列表（递归穿透嵌套 And）。"""
    from z3 import Z3_OP_AND

    out = []
    stack = [expr]
    while stack:
        cur = stack.pop()
        if cur is None:
            continue
        try:
            if hasattr(cur, "decl") and cur.decl().kind() == Z3_OP_AND:
                stack.extend(cur.children())
                continue
        except Exception:
            pass
        out.append(cur)
    return out


def decompose_store_chain(arr):
    """将一个 Z3 Array 表达式分解为 (base_array, [(key, value), ...]) 形式。"""
    from z3 import Z3_OP_STORE

    stores = []
    cur = arr
    try:
        while True:
            if not hasattr(cur, "decl"):
                break
            decl_kind = cur.decl().kind()
            if decl_kind != Z3_OP_STORE:
                break
            args = cur.children()  # [base, key, value]
            if len(args) != 3:
                break
            stores.append((args[1], args[2]))
            cur = args[0]
    except Exception:
        return arr, []
    stores.reverse()  # 顺序从最早到最近
    return cur, stores


def expr_has_uninterpreted_decl(expr, predicate) -> bool:
    """Return True if any uninterpreted declaration in expr matches predicate."""
    try:
        from z3 import Z3_OP_UNINTERPRETED
    except Exception:
        return False

    seen = set()
    stack = [expr]
    while stack:
        cur = stack.pop()
        if cur is None:
            continue
        try:
            key = cur.hash()
        except Exception:
            continue
        if key in seen:
            continue
        seen.add(key)
        try:
            decl = cur.decl()
            if decl.kind() == Z3_OP_UNINTERPRETED and predicate(decl, cur):
                return True
            stack.extend(cur.children())
        except Exception:
            continue
    return False


def expr_mentions_symbol(expr, symbol_name: str) -> bool:
    """判断表达式是否包含指定名称的未解释常量。"""
    return expr_has_uninterpreted_decl(
        expr,
        lambda decl, node: decl.name() == symbol_name and len(node.children()) == 0,
    )


def is_if_expression(expr: BitVec) -> bool:
    """检查表达式是否为 Z3 If (ITE) 表达式。"""
    return expr.decl().name() == 'if'


def extract_if_branches(if_expr: BitVec) -> Tuple[object, BitVec, BitVec]:
    """从 If 表达式中提取条件和分支。

    Args:
        if_expr: If 表达式

    Returns:
        (condition, then_branch, else_branch) 元组

    Raises:
        ValueError: 如果输入不是 If 表达式
    """
    if not is_if_expression(if_expr):
        raise ValueError(f"Expected If expression, got {if_expr}")
    return (if_expr.arg(0), if_expr.arg(1), if_expr.arg(2))


def analyze_jump_target(target_expr: BitVec) -> JumpTargetAnalysis:
    """分析跳转目标表达式，判断是否可以静态解析。

    Args:
        target_expr: 从栈中获取的目标值表达式（BitVec）

    Returns:
        JumpTargetAnalysis 分析结果
    """
    # 先简化表达式，消除冗余结构、常量折叠等
    simplified_expr = simplify(target_expr)

    # 情况1：直接常量
    const_value = get_bv_const_value(simplified_expr)
    if const_value is not None:
        return JumpTargetAnalysis(is_static=True, targets=[(const_value, None)])

    # 情况2：If 表达式（包括嵌套）
    if is_if_expression(simplified_expr):
        targets = _extract_targets_from_if(simplified_expr)
        if targets:
            return JumpTargetAnalysis(is_static=True, targets=targets)

    # 情况3：其他符号值 - 真正的动态跳转
    return JumpTargetAnalysis(is_static=False, targets=[])


def _extract_targets_from_if(if_expr: BitVec, path_condition: Optional[object] = None) -> List[Tuple[int, object]]:
    """递归地从 If 表达式中提取所有可能的常量目标。

    Args:
        if_expr: If 表达式
        path_condition: 当前路径条件（用于嵌套 If）

    Returns:
        (target_pc, combined_condition) 列表
    """
    condition, then_branch, else_branch = extract_if_branches(if_expr)
    results = []

    # 处理 then 分支
    then_value = get_bv_const_value(then_branch)
    if then_value is not None:
        combined_cond = condition if path_condition is None else And(path_condition, condition)
        results.append((then_value, simplify(combined_cond)))
    elif is_if_expression(then_branch):
        nested_cond = condition if path_condition is None else And(path_condition, condition)
        nested_results = _extract_targets_from_if(then_branch, nested_cond)
        results.extend(nested_results)

    # 处理 else 分支
    else_value = get_bv_const_value(else_branch)
    if else_value is not None:
        negated_cond = Not(condition) if path_condition is None else And(path_condition, Not(condition))
        results.append((else_value, simplify(negated_cond)))
    elif is_if_expression(else_branch):
        negated_cond = Not(condition) if path_condition is None else And(path_condition, Not(condition))
        nested_results = _extract_targets_from_if(else_branch, negated_cond)
        results.extend(nested_results)

    return results
