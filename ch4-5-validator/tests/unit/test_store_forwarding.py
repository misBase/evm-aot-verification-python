#!/usr/bin/env python3
"""store_forwarding 归一化器单元测试。"""

from z3 import (
    Array, BitVec, BitVecSort, BitVecVal, Concat, Extract, Lambda, Select,
    Store, simplify, is_true, eq,
)

from common.store_forwarding import (
    forward_selects,
    linearize_address,
    resolve_select_over_store,
    unshift_store_chain,
    memory_as_offset_view,
)

B = BitVec("B", 64)
O = BitVec("O", 64)
ARR = Array("A", BitVecSort(64), BitVecSort(8))
V1 = BitVec("v1", 8)
V2 = BitVec("v2", 8)


def test_linearize_groups_terms_and_constants():
    key1, c1 = linearize_address(B + O + 5 + 3)
    key2, c2 = linearize_address(3 + O + B + 5)
    assert key1 == key2 and c1 == c2 == 8

    key3, c3 = linearize_address(B + 5)
    assert key3 != key1


def test_resolve_hit_and_skip():
    chain = Store(Store(ARR, B + O + 1, V1), B + O + 2, V2)
    # 命中最外层
    assert eq(resolve_select_over_store(Select(chain, B + O + 2)), V2)
    # 跳过外层（判异）命中内层
    assert eq(resolve_select_over_store(Select(chain, B + O + 1)), V1)
    # 全链判异：剥到链底
    stripped = resolve_select_over_store(Select(chain, B + O + 7))
    assert stripped is not None
    assert eq(stripped, Select(ARR, B + O + 7))


def test_resolve_bails_on_unknown_base():
    other = BitVec("other", 64)
    chain = Store(ARR, other, V1)  # 异基：可能别名
    assert resolve_select_over_store(Select(chain, B + O)) is None


def test_forward_selects_rewrites_nested():
    chain = Store(ARR, B + 8, V1)
    expr = Concat(Select(chain, B + 8), Select(chain, B + 9))
    rewritten = forward_selects(expr)
    assert eq(rewritten, Concat(V1, Select(ARR, B + 9)))


def test_unshift_store_chain_removes_lambda_view():
    mem0 = Array("mem0", BitVecSort(64), BitVecSort(8))
    r15 = BitVec("r15", 64)
    addr = BitVec("__a", 64)
    view = Lambda([addr], Select(mem0, addr - r15))
    chain = Store(Store(view, r15 + 5, V1), r15 + O + 9, V2)

    unshifted = unshift_store_chain(chain, r15, mem0)
    assert unshifted is not None
    expected = Store(Store(mem0, BitVecVal(5, 64), V1), BitVecVal(9, 64) + O, V2)
    # 结构可能项序不同，用 z3 判等价（具体地址代入）
    from z3 import Solver, Not, unsat
    s = Solver()
    s.add(Not(unshifted == expected))
    assert s.check() == unsat


def test_unshift_bails_without_base_term():
    mem0 = Array("mem0", BitVecSort(64), BitVecSort(8))
    r15 = BitVec("r15", 64)
    chain = Store(mem0, BitVecVal(5, 64), V1)  # 地址不含 r15
    assert unshift_store_chain(chain, r15, mem0) is None


def test_offset_view_preserves_arbitrary_bytes_and_wrapping_addresses():
    from z3 import Solver, unsat
    # Neither store needs to syntactically contain B. They may alias or wrap.
    absolute = Store(Store(ARR, O, V1), B + 1, V2)
    offset = BitVec("view_probe", 64)
    view = memory_as_offset_view(absolute, B)
    solver = Solver()
    solver.add(Select(view, offset) != Select(absolute, B + offset))
    assert solver.check() == unsat


def test_unshift_rejects_wrong_translation_and_untranslated_array():
    index = BitVec("bad_view_index", 64)
    for memory in (ARR, Lambda([index], Select(ARR, index - B + 1))):
        assert unshift_store_chain(Store(memory, B + 5, V1), B, ARR) is None


def test_memo_keys_name_the_context():
    # Fresh contexts number their first ASTs alike: equal ids, unrelated terms.
    from z3 import BitVec, Context
    from common.store_forwarding import _memoized
    a, b = BitVec("memo_ctx_a", 8, Context()), BitVec("memo_ctx_b", 8, Context())
    assert a.get_id() == b.get_id()
    assert _memoized("memo_ctx_probe", (a,), lambda: "a") == "a"
    assert _memoized("memo_ctx_probe", (b,), lambda: "b") == "b"
    assert _memoized("memo_ctx_probe", (a,), lambda: "other") == "a"


def test_forward_selects_rebuilds_only_changed_parents(monkeypatch):
    # Unchanged subterms keep their AST: rebuilding them was pure overhead.
    from z3 import Array, BitVec, BitVecSort, Concat, Select, Store, FuncDeclRef
    import common.store_forwarding as sf
    m = Array("fwd_eq_m", BitVecSort(64), BitVecSort(8))
    a, x = BitVec("fwd_eq_a", 64), BitVec("fwd_eq_x", 8)
    unchanged = Concat(Select(m, a), Select(m, a + 1))
    calls = []
    real = FuncDeclRef.__call__
    monkeypatch.setattr(FuncDeclRef, "__call__", lambda self, *args: calls.append(self.name()) or real(self, *args))
    assert sf.forward_selects(unchanged, {}).eq(unchanged) and calls == []
    forwarded = sf.forward_selects(Concat(Select(Store(m, a, x), a), Select(m, a + 1)), {})
    assert forwarded.eq(Concat(x, Select(m, a + 1))) and calls == ["concat"]
