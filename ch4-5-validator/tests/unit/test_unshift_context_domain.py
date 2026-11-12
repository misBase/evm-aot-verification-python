"""Unshift's native AST-id comparisons require one input Context."""
import z3 as z

from common import store_forwarding as sf


def _live_root_collision():
    for left_padding in range(9):
        for right_padding in range(9):
            left, right = z.Context(), z.Context()
            anchors = [z.BitVec(f'unshift_left_pad_{i}', 8, ctx=left) for i in range(left_padding)]
            anchors += [z.BitVec(f'unshift_right_pad_{i}', 8, ctx=right) for i in range(right_padding)]
            raw = z.K(z.BitVecSort(64, ctx=left), z.BitVecVal(0, 8, ctx=left))
            base = z.BitVecVal(0, 64, ctx=left)
            foreign = z.Array('unshift_foreign', z.BitVecSort(64, ctx=right), z.BitVecSort(8, ctx=right))
            if raw.get_id() == foreign.get_id():
                return raw, base, foreign, anchors
    raise AssertionError('bounded natural native-id overlap was not observed')


def test_unshift_rejects_a_foreign_array_even_when_native_ids_match():
    raw, base, foreign, anchors = _live_root_collision()
    assert raw.ctx is not foreign.ctx
    assert sf.unshift_store_chain(raw, base, foreign) is None


def test_unshift_rejects_a_foreign_base_term():
    raw, base, foreign, anchors = _live_root_collision()
    foreign_base = z.BitVecVal(0, 64, ctx=foreign.ctx)
    assert sf.unshift_store_chain(raw, foreign_base, raw) is None


def test_same_main_context_shifted_store_output_is_unchanged():
    memory = z.Array('unshift_main_memory', z.BitVecSort(64), z.BitVecSort(8))
    base, index = z.BitVecs('unshift_main_base unshift_main_index', 64)
    value = z.BitVec('unshift_main_value', 8)
    view = z.Lambda([index], z.Select(memory, index - base))
    shifted = z.Store(view, base + 5, value)
    result = sf.unshift_store_chain(shifted, base, memory)
    assert result is not None
    assert result.eq(z.Store(memory, z.BitVecVal(5, 64), value))
    assert z.is_true(z.simplify(z.Select(result, z.BitVecVal(5, 64)) == value))


def test_same_main_context_zero_base_constant_array_is_unchanged():
    raw = z.K(z.BitVecSort(64), z.BitVecVal(0, 8))
    result = sf.unshift_store_chain(raw, z.BitVecVal(0, 64), raw)
    assert result is raw
    assert z.is_true(z.simplify(z.Select(result, z.BitVecVal(0, 64)) == 0))
