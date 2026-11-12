"""Select-over-Store 链的保守解析与 R15 平移下推（循环归纳 R 目标化简器）。

背景：x86 内存模型把 64-bit 写展开成 8 个字节 Store；一轮段执行后的
栈窗口读数嵌着上百层 Store 链。Z3 默认 rewriter 不做符号地址的 store
forwarding（只处理数值地址），直接把 R 保持目标交给求解器会 unknown。

本模块在 Python 层做**保守**的别名判定与改写——只有可证明时才动手：

- 地址线性化为（非常量项多重集, 常量和 mod 2^64）；
- 同基（非常量部分完全相同）⇒ 常量差直接判等/判异；
- 异基 ⇒ 可能别名 ⇒ 放弃改写（fail-closed，留给求解器）。

改写是语义保持的（等价变换），因此对证明目标与前提都可用。
"""

from typing import Dict, List, Optional, Tuple

from z3 import (
    BitVecVal,
    BitVecSort,
    Concat,
    Extract,
    FreshConst,
    Z3_OP_BADD,
    Z3_OP_CONCAT,
    Z3_OP_EXTRACT,
    Lambda,
    main_ctx,
    Select,
    Store,
    is_app,
    is_bv,
    is_bv_value,
    is_const,
    is_const_array,
    is_quantifier,
    is_select,
    is_store,
    is_true,
    is_var,
    get_var_index,
    simplify,
    substitute_vars,
)

# 线性化地址的规范键：((term_id, count), ...) 排序元组（AST 哈希共享：同项同 id）
class _AddrKey(tuple):
    """Keep normalized atoms alive while their ids are used, including across cache clears."""
    def __new__(cls, terms, normalized):
        key = super().__new__(cls, terms)
        key._normalized = normalized
        return key


def memory_as_offset_view(memory, base):
    """Translate absolute byte addresses to offsets, preserving every byte.

    Addition modulo 2**64 is a bijection, so Store addresses can be translated
    exactly without alias or no-overflow assumptions.
    """
    stores = []
    while is_store(memory):
        stores.append((simplify(memory.arg(1) - base), memory.arg(2)))
        memory = memory.arg(0)
    offset = FreshConst(BitVecSort(64), "memory_view_offset")
    result = simplify(Lambda([offset], Select(memory, base + offset)))
    if is_quantifier(result) and result.is_lambda():
        body = result.body()
        # Z3 leaves Lambda(i, A[i]) intact; a free array A is already that view.
        if (is_select(body) and is_const(body.arg(0))
                and is_var(body.arg(1)) and get_var_index(body.arg(1)) == 0):
            result = body.arg(0)
    for address, value in reversed(stores):
        result = Store(result, address, value)
    return result


# Pure functions of their AST arguments. Values keep the argument ASTs (and so
# their contexts) alive, so neither ids nor contexts can be recycled while cached.
# An AST id is unique only within its context: equal ids in two contexts are
# unrelated terms, so the key names the context too. ponytail: cleared wholesale
# at _MEMO_LIMIT entries; an LRU if that ever thrashes.
_MEMO: Dict[tuple, tuple] = {}
_MEMO_LIMIT = 200_000


def _memoized(name, args, compute, keep=None):
    """compute(), memoized per (name, context and AST id of each arg); with `keep`, only values it accepts."""
    key = (name, *((id(a.ctx), a.get_id()) for a in args))
    hit = _MEMO.get(key)
    if hit is not None:
        return hit[1]
    value = compute()
    if keep is None or keep(value):
        if len(_MEMO) >= _MEMO_LIMIT:
            _MEMO.clear()
        _MEMO[key] = (args, value)
    return value


def clear_memo():
    """Drop every memoized term. Pure caches, so only speed changes; long-lived
    worker processes call this between nodes, since entries keep their ASTs alive."""
    _MEMO.clear()
    _SHARED_FORWARD.clear()


# One forward_selects cache for the whole process (see forward_selects_shared), cleared
# wholesale at a scope boundary (shared_forward_scope) once it holds _SHARED_FORWARD_LIMIT
# entries. ponytail: one Aave Pool 7200 DIV hit adds ~22k; an LRU if that ever thrashes.
_SHARED_FORWARD: Dict[int, object] = {}
_SHARED_FORWARD_LIMIT = 25_000


def linearize_address(addr) -> Optional[Tuple[_AddrKey, int]]:
    if not is_bv(addr):
        return None
    return _memoized("linearize", (addr,), lambda: _linearize_address(addr))


def _linearize_address(addr) -> Optional[Tuple[_AddrKey, int]]:
    """把位向量地址拆成（非常量项多重集, 常量和）。

    先做 z3 simplify：折叠常量算术（如 ``(8-4)*8``）、归一化
    ``Extract(Concat(0,a)+Concat(0,b))`` 形态、融合 Concat-of-Extracts——
    否则同一地址的不同书写形态会被误判异基。乘法/拼接等仍视为原子项。
    返回 None 表示非 BV。
    """
    if not is_bv(addr):
        return None
    addr = simplify(addr)
    width = addr.size()
    mask = (1 << width) - 1
    const = 0
    terms: Dict[int, Tuple[object, int]] = {}
    stack = [addr]
    while stack:
        node = stack.pop()
        if is_bv_value(node):
            const = (const + node.as_long()) & mask
        elif is_app(node) and node.decl().kind() == Z3_OP_BADD:
            stack.extend(node.children())
        else:
            key = node.get_id()  # hash-consed: same term <=> same id, no printing
            prev = terms.get(key)
            terms[key] = (node, (prev[1] + 1) if prev else 1)
    addr_key = _AddrKey(sorted((k, v[1]) for k, v in terms.items()), addr)
    return addr_key, const


def resolve_select_over_store(select_expr, max_chain: int = 4096):
    """解析 Select(Store(...), addr)：沿链下钻，可判等返回存值，可判异
    继续下钻，判不了返回 None（不改写）。

    链底若是非 Store 数组（K/常量数组/自由数组/Lambda），返回对链底的
    Select（链被整体剥离，也是收益）。
    """
    if not is_select(select_expr):
        return None
    lin = linearize_address(select_expr.arg(1))
    if lin is None:
        return None
    sel_key, sel_const = lin

    node = select_expr.arg(0)
    depth = 0
    changed = False
    while is_store(node):
        depth += 1
        if depth > max_chain:
            return None
        st_lin = linearize_address(node.arg(1))
        if st_lin is None:
            return None
        st_key, st_const = st_lin
        if st_key == sel_key:
            if st_const == sel_const:
                return node.arg(2)  # 命中：读到这次写的值
            node = node.arg(0)      # 可证不别名：跳过这层
            changed = True
            continue
        return None                 # 异基：可能别名，放弃
    if not changed:
        return None
    return Select(node, select_expr.arg(1))


def compact_dead_stores(array_expr, *, min_chain: int = 256):
    """Drop every Store shadowed by a newer Store at a provably-equal address.

    Store(Store(A, i, v1), i', v2) == Store(A, i, v2) when i' == i is an array
    identity (extensionality), and it stays one with unrelated stores between
    the two writes. Address equality is proved exactly as resolve_select_over_store
    proves its hits (linearize_address: constant folding + bvadd AC); anything
    not provably equal is kept (fail-closed). Chains grow by 8 Stores per limb
    written and are never shortened, so a long segment re-walks a chain of
    thousands of stores in every summary hit (Aave Pool 7200). Returns the
    original expression when nothing is droppable, keeping its AST ids (and
    every memo keyed by them) alive.

    Chains shorter than ``min_chain`` are returned unchanged: the walk itself
    linearizes every address, and a fresh EVM-memory address can cost ~0.3 s in
    simplify -- far more than forwarding a short chain ever could (Pool 7200:
    32-store chains at 9.5 s). Short chains have nothing worth dropping.
    """
    if not is_store(array_expr):
        return array_expr
    stores = []
    node = array_expr
    while is_store(node):
        stores.append(node)
        node = node.arg(0)
    if len(stores) <= min_chain:
        return array_expr
    kept, seen = [], set()
    for store in stores:                # newest first: keep the shadowing write
        lin = linearize_address(store.arg(1))
        if lin is not None:
            key = (lin[0], lin[1])
            if key in seen:
                continue                # dead: a newer store hits the same address
            seen.add(key)
        kept.append(store)
    if len(kept) == len(stores):
        return array_expr
    result = node
    for store in reversed(kept):
        result = Store(result, store.arg(1), store.arg(2))
    return result


_ALIVE = "alive"  # cache slot holding every keyed node: its id cannot be reused while cached


def _put(cache, node, value):
    cache[node.get_id()] = value
    cache.setdefault(_ALIVE, []).append(node)


def forward_selects(expr, _cache: Optional[Dict[int, object]] = None):
    """自底向上改写表达式中所有可解析的 Select-over-Store。

    量词/Lambda 节点保守跳过（不深入改写其体）。
    """
    # Iterative post-order (explicit stack): Store chains of real contracts
    # exceed Python's recursion limit. Stage 0 expands, 1 rebuilds, 2 adopts
    # the forwarded result of a resolved Select.
    if _cache is None:
        _cache = {}
    if _cache.get("_ctx") is not expr.ctx:
        _cache.clear()
        _cache["_ctx"] = expr.ctx
    stack = [(expr, 0, None)]
    while stack:
        node, stage, resolved = stack.pop()
        key = node.get_id()
        if stage == 0:
            if key in _cache:
                continue
            if is_quantifier(node) or not is_app(node):
                _put(_cache, node, node)
                continue
            stack.append((node, 1, None))
            stack.extend((c, 0, None) for c in node.children() if c.get_id() not in _cache)
        elif stage == 1:
            originals = node.children()
            children = [_cache[c.get_id()] for c in originals]
            result = node
            # children() may return different Python wrappers for the same AST.
            # Native AST equality avoids rebuilding structurally unchanged children;
            # it does not establish how much of a real forwarding hit this saves.
            if any(not c.eq(o) for c, o in zip(children, originals)):
                result = node.decl()(*children)
            if is_select(result):
                target = resolve_select_over_store(result)
                if target is not None:
                    if target.get_id() not in _cache:
                        stack.append((node, 2, target))
                        stack.append((target, 0, None))
                        continue
                    result = _cache[target.get_id()]
            _put(_cache, node, result)
        else:
            _put(_cache, node, _cache[resolved.get_id()])
    return _cache[expr.get_id()]


def forward_selects_shared(expr):
    """forward_selects(expr) through one process-level cache.

    forward_selects is a pure function of each node (the cache keeps every
    keyed node alive, so an id is never another term's), so the result is
    the same as with a fresh cache. Callers that forward many terms over one
    growing memory get the shared store chain forwarded once: the DIV summary
    forwards 8 stack limbs per hit, each a read through the whole x86 memory
    (Aave Pool 7200: ~500s per hit, 53% of the x86 segment, re-forwarding the
    same chain per limb and again on every path).

    Never cleared here: within a scope (shared_forward_scope) every call
    shares it, whatever its size. Keyed by AST id, so only main-context terms
    share it (an id names different terms in different contexts)."""
    return forward_selects(expr, _SHARED_FORWARD if expr.ctx is main_ctx() else None)


def shared_forward_scope():
    """Start a scope of forward_selects_shared calls (one summary hit): the
    cache is dropped first if it holds _SHARED_FORWARD_LIMIT entries.

    Entries keep their nodes alive, and on a long x86 segment they are the
    store chains of every path forwarded so far: with a 2M-entry limit that
    was never reached the cache held most of Z3's memory (Aave Pool 7200:
    ~2.4 GB/h of growth). Dropping it only between hits keeps the sharing
    across one hit's 8 limb loads (most of the gain) and between the hits
    that follow, until the bound. A pure cache: only speed and memory change."""
    if len(_SHARED_FORWARD) >= _SHARED_FORWARD_LIMIT:
        _SHARED_FORWARD.clear()


def join_extracts(expr, _cache: Optional[Dict[int, object]] = None):
    """Concat(…, s[h:m+1], s[m:l], …) -> Concat(…, s[h:l], …), and s[w-1:0] -> s, bottom-up.

    A limb written with store_64bit and read back with load_64bit forwards
    to Concat(Extract(63,56,V), …, Extract(7,0,V)). Z3's simplifier pushes
    each Extract into V before it would rejoin them (into ite, bvadd, the low
    bits of bvmul), so `limb == V` becomes a multiplier-circuit equivalence
    once V carries memory-cost squares (CErc20 10233 H2 callEngine
    gas_remaining mirror: unknown after 1868s; joined: V == V, False at once).
    A bit-vector identity, so the rewrite is exact. Binders are not entered.
    """
    if _cache is None:
        _cache = {}
    if _cache.get("_ctx") is not expr.ctx:
        _cache.clear()
        _cache["_ctx"] = expr.ctx
    stack = [(expr, False)]
    while stack:
        node, built = stack.pop()
        key = node.get_id()
        if key in _cache:
            continue
        if is_quantifier(node) or not is_app(node) or node.num_args() == 0:
            _put(_cache, node, node)
            continue
        if not built:
            stack.append((node, True))
            stack.extend((c, False) for c in node.children() if c.get_id() not in _cache)
            continue
        originals = node.children()
        children = [_cache[c.get_id()] for c in originals]
        result = node if all(c.eq(o) for c, o in zip(children, originals)) else node.decl()(*children)
        if result.decl().kind() == Z3_OP_CONCAT:
            parts = []  # [hi, lo, source]; hi None: not an extract
            for arg in result.children():
                if arg.decl().kind() == Z3_OP_EXTRACT:
                    hi, lo = arg.params()
                    if parts and parts[-1][0] is not None and parts[-1][1] == hi + 1 and parts[-1][2].eq(arg.arg(0)):
                        parts[-1][1] = lo
                        continue
                    parts.append([hi, lo, arg.arg(0)])
                else:
                    parts.append([None, None, arg])
            if len(parts) < result.num_args():
                terms = [t if hi is None or (hi == t.size() - 1 and lo == 0) else Extract(hi, lo, t)
                         for hi, lo, t in parts]
                result = terms[0] if len(terms) == 1 else Concat(*terms)
        _put(_cache, node, result)
    return _cache[expr.get_id()]


def _subtract_base_term(addr, base_term) -> Optional[object]:
    """从地址的 bvadd 线性组合中移除一次 base_term；不含则返回 None（按两个 AST 记忆）。"""
    return _memoized("subtract", (addr, base_term), lambda: _subtract_base_term_raw(addr, base_term))


def _subtract_base_term_raw(addr, base_term) -> Optional[object]:
    if not is_bv(addr):
        return None
    addr = simplify(addr)
    width = addr.size()
    base = simplify(base_term)
    const = 0
    rest: List[object] = []
    removed = False
    stack = [addr]
    while stack:
        node = stack.pop()
        if is_bv_value(node):
            const = (const + node.as_long()) & ((1 << width) - 1)
        elif is_app(node) and node.decl().kind() == Z3_OP_BADD:
            stack.extend(node.children())
        elif not removed and node.eq(base):
            removed = True
        else:
            rest.append(node)
    if not removed:
        return None
    result = BitVecVal(const, width)
    for term in rest:
        result = result + term
    return result


def unshift_store_chain(array_expr, base_term, base_array) -> Optional[object]:
    return _memoized("unshift", (array_expr, base_term, base_array),
                     lambda: _unshift_store_chain(array_expr, base_term, base_array))


def _unshift_store_chain(array_expr, base_term, base_array) -> Optional[object]:
    """把 Store 链从绝对地址空间（base_term + offset）下推到 offset 空间。

    要求链上每个 Store 地址都线性含 base_term（系数 1），链底等于
    构造时的平移视图（其展开即 base_array）。返回 offset 空间的
    Store 链（根为 base_array）；任一环节不满足返回 None（fail-closed）。

    语义依据：x ↦ base+x 是 mod 2^64 双射，
    view(Store(A, base+t, v)) = Store(view(A), t, v)。
    """
    if not (array_expr.ctx is base_term.ctx is base_array.ctx):
        return None
    stores: List[Tuple[object, object]] = []
    node = array_expr
    while is_store(node):
        offset = _subtract_base_term(node.arg(1), base_term)
        if offset is None:
            return None
        stores.append((offset, node.arg(2)))
        node = node.arg(0)

    # 必须核对平移索引，不能仅凭读取了同一数组就丢弃 Lambda。
    if node.get_id() == base_array.get_id():
        if not (is_const_array(node) or is_true(simplify(base_term == 0))):
            return None
        root = base_array
    elif is_quantifier(node) and node.is_lambda() and node.num_vars() == 1:
        body = node.body()
        if is_select(body) and body.arg(0).get_id() == base_array.get_id():
            offset = FreshConst(BitVecSort(64), "unshift_probe")
            index = substitute_vars(body.arg(1), base_term + offset)
            if not is_true(simplify(index == offset)):
                return None
            root = base_array
        else:
            return None
    else:
        return None

    result = root
    for offset, value in reversed(stores):
        result = Store(result, offset, value)
    return result
