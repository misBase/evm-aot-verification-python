"""A caller-owned SF memo cannot reuse native AST ids across Z3 Contexts."""
import pytest
import z3 as z

from common import store_forwarding as sf


def _answer(formula):
    solver = z.Solver(ctx=formula.ctx)
    solver.set(timeout=1000, rlimit=100000, random_seed=0)
    solver.add(formula)
    return solver.check()


def _live_collision():
    # Context-local native ids naturally overlap. Retain every padding/root.
    for left_padding in range(4):
        for right_padding in range(4):
            left, right = z.Context(), z.Context()
            anchors = [z.BitVec(f'left_padding_{i}', 8, ctx=left) for i in range(left_padding)]
            anchors += [z.BitVec(f'right_padding_{i}', 8, ctx=right) for i in range(right_padding)]
            a = z.BitVec('left_a', 8, ctx=left)
            b, c = z.BitVecs('right_b right_c', 8, ctx=right)
            impossible, possible = a != a, b != c
            if impossible.get_id() == possible.get_id():
                return impossible, possible, anchors
    pytest.fail('bounded natural Context-local id collision was not observed')


@pytest.mark.parametrize('name', ['forward_selects', 'join_extracts'])
def test_explicit_cache_context_switch_preserves_the_formula(name):
    impossible, possible, anchors = _live_collision()
    assert _answer(impossible) == z.unsat
    assert _answer(possible) == z.sat
    rewrite, cache = getattr(sf, name), {}
    for formula in (impossible, possible, impossible):
        value = rewrite(formula, cache)
        assert value.ctx is formula.ctx
        assert _answer(value != formula) == z.unsat
        assert rewrite(formula, cache) is value
        if formula is possible:
            assert _answer(value) == z.sat


@pytest.mark.parametrize('name', ['forward_selects', 'join_extracts'])
def test_untagged_legacy_cache_is_discarded_before_use(name):
    impossible, possible, anchors = _live_collision()
    # This is the pre-fence cache layout, populated by real original ASTs.
    rewrite, cache = getattr(sf, name), {}
    rewrite(impossible, cache)
    cache.pop('_ctx', None)
    assert '_ctx' not in cache
    value = rewrite(possible, cache)
    assert value.ctx is possible.ctx
    assert _answer(value) == z.sat
    assert _answer(value != possible) == z.unsat


@pytest.mark.parametrize('name', ['forward_selects', 'join_extracts'])
def test_same_context_reuse_and_explicit_clear(name):
    ctx = z.Context()
    a, b = z.BitVecs('clear_a clear_b', 8, ctx=ctx)
    formula, cache = a != b, {}
    rewrite = getattr(sf, name)
    first = rewrite(formula, cache)
    assert rewrite(formula, cache) is first
    assert cache[sf._ALIVE]
    cache.clear()
    after = rewrite(formula, cache)
    assert after.ctx is ctx and _answer(after != formula) == z.unsat
    assert cache[sf._ALIVE]


def test_real_select_store_and_concat_extract_in_each_context():
    for ctx in (z.Context(), z.Context()):
        address = z.BitVec('rewrite_address', 64, ctx=ctx)
        byte = z.BitVec('rewrite_byte', 8, ctx=ctx)
        memory = z.Array('rewrite_memory', z.BitVecSort(64, ctx=ctx), z.BitVecSort(8, ctx=ctx))
        read = z.Select(z.Store(memory, address, byte), address)
        forwarded = sf.forward_selects(read, {})
        assert forwarded.ctx is ctx and forwarded.eq(byte)
        assert _answer(forwarded != read) == z.unsat
        word = z.BitVec('rewrite_word', 64, ctx=ctx)
        pieces = z.Concat(z.Extract(63, 32, word), z.Extract(31, 0, word))
        joined = sf.join_extracts(pieces, {})
        assert joined.ctx is ctx and joined.eq(word)
        assert _answer(joined != pieces) == z.unsat


def test_shared_helper_does_not_reuse_main_cache_for_a_foreign_context():
    original = dict(sf._SHARED_FORWARD)
    if sf._ALIVE in original:
        original[sf._ALIVE] = list(original[sf._ALIVE])
    try:
        a = z.BitVec('shared_main_a', 8)
        sf.forward_selects_shared(a != a)
        signature = {key: id(value) for key, value in sf._SHARED_FORWARD.items()}
        ctx = z.Context()
        b, c = z.BitVecs('shared_foreign_b shared_foreign_c', 8, ctx=ctx)
        value = sf.forward_selects_shared(b != c)
        assert value.ctx is ctx and _answer(value) == z.sat
        assert signature == {key: id(value) for key, value in sf._SHARED_FORWARD.items()}
    finally:
        sf._SHARED_FORWARD.clear()
        sf._SHARED_FORWARD.update(original)
