"""Transport orders only Boolean OR, after canonicalizing its complete children."""
import gzip
from pathlib import Path

import pytest
import z3 as z

import verification.block_equivalence as be
from verification.alpha_canon import canon_binders


def transport(expr, cache=None):
    return canon_binders(expr, cache, _transport_or=True)


def assert_identity(before, after):
    solver = z.Solver(ctx=before.ctx)
    solver.set(timeout=250, rlimit=250000)
    solver.add(before != after)
    assert solver.check() == z.unsat


def test_or_permutation_preserves_all_children_and_is_unconditionally_equal():
    p, q, r = z.Bools('transport_or_p transport_or_q transport_or_r')
    forward, reverse = z.Or(p, q, r, p), z.Or(p, r, q, p)
    normal = transport(forward)
    assert normal.eq(transport(reverse))
    assert normal.num_args() == 4  # Preserve multiplicity; this mode only orders.
    assert sorted(k.get_id() for k in normal.children()) == sorted(k.get_id() for k in forward.children())
    assert_identity(forward, normal)
    assert not normal.eq(transport(z.Or(p, q, r)))


@pytest.mark.parametrize('transport_first', [False, True])
def test_shared_cache_keeps_transport_policy_separate_and_inputs_alive(transport_first):
    p, q = z.Bools('transport_cache_p transport_cache_q')
    original = z.Or(q, p)
    cache = {}
    operations = (transport, canon_binders) if transport_first else (canon_binders, transport)
    for operation in operations:
        operation(original, cache)
    assert canon_binders(original, cache).eq(original)
    assert transport(original, cache).eq(transport(z.Or(p, q)))
    assert all(z.is_expr(source) and z.is_expr(result) for source, result, _ in cache.values())
    assert (id(original.ctx), 'binders', original.get_id()) in cache
    assert (id(original.ctx), 'transport_or', original.get_id()) in cache


def test_nested_binders_order_after_child_canonicalization_and_keep_meaning():
    x, y = z.BitVecs('transport_bound_x transport_bound_y', 8)
    a = z.Lambda(x, z.Or(x == 1, x == 2))
    b = z.Lambda(y, z.Or(y == 2, y == 1))
    assert transport(a).eq(transport(b))
    assert_identity(a, transport(a))
    outer = z.Lambda(x, z.Select(z.Lambda(y, z.Or(y == x, y == 0)), x + 1))
    assert_identity(outer, transport(outer))


def test_named_or_uf_is_not_permuted():
    p, q = z.Bools('transport_uf_p transport_uf_q')
    function = z.Function('or', p.sort(), p.sort(), p.sort())
    expression = function(q, p)
    assert transport(expression).eq(expression)
    assert not transport(expression).eq(transport(function(p, q)))


def test_copy_word_gas_gate_is_stable_across_repeated_same_context_history():
    fixture = Path(__file__).with_name('data') / 'x86_reachability_copy_word_gas.smt2.gz'
    formula = z.parse_smt2_string(gzip.decompress(fixture.read_bytes()).decode())[0]
    for _ in range(10):
        text = be._to_smt2(formula)
        parsed = z.parse_smt2_string(text)[0]
        # The returned input remains equivalent; do not replace it with a normalized query.
        before = transport(z.simplify(canon_binders(formula)))
        after = transport(z.simplify(parsed))
        assert before.eq(after)
        assert_identity(before, after)
