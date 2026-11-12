"""Address keys must keep their normalized atoms alive while consumers hold them."""
import json

import pytest
import z3 as z

import common.store_forwarding as sf


@pytest.fixture(autouse=True)
def clean_memo():
    sf.clear_memo()
    yield
    sf.clear_memo()


def assert_unsat(formula):
    solver = z.Solver(ctx=formula.ctx)
    solver.set(timeout=1000, rlimit=100000)
    solver.add(formula)
    assert solver.check() == z.unsat


def wrapped_product(x, coefficient, offset=0):
    width = x.size()
    return z.Extract(width-1, 0, z.ZeroExt(width, x)*z.BitVecVal(coefficient, 2*width, x.ctx)
                     + z.BitVecVal(offset, 2*width, x.ctx))


@pytest.mark.parametrize("width", [8, 64])
@pytest.mark.parametrize("limit", [1, 4])
def test_retained_keys_survive_eviction_and_explicit_clear(monkeypatch, width, limit):
    monkeypatch.setattr(sf, "_MEMO_LIMIT", limit)
    x, y = z.BitVecs(f"retained_x{width} retained_y{width}", width)
    addresses = [wrapped_product(v, c) for v in (x, y) for c in range(2, 18)]
    retained = [(a, sf.linearize_address(a)) for a in addresses]
    sf.clear_memo()
    for a in addresses:
        z.simplify(a + 17)
    for a, (key, constant) in retained:
        current, current_constant = sf.linearize_address(a)
        assert key == current and hash(key) == hash(current)
        assert constant == current_constant == 0
        assert isinstance(key, tuple) and dict(key) == dict(current)
        assert json.loads(json.dumps(key)) == [list(pair) for pair in key]


def test_forwarding_after_normalized_address_id_churn(record_property):
    variables = z.BitVecs("churn_x0 churn_x1 churn_x2 churn_x3", 8)
    literals = [z.BitVecVal(n, 8) for n in range(64)]
    addresses = [wrapped_product(x, c, offset) for offset in (0, 1)
                 for x in variables for c in range(2, 34)]
    unrelated = [(x+z.BitVecVal(c, 8))*(variables[(i+1) % 4]+1)
                 for i, x in enumerate(variables) for c in range(8)]
    prior, pairs = {}, []
    for index, a in enumerate(addresses):
        key, _ = sf.linearize_address(a)
        if key in prior:
            pairs.append((prior[key], a))
        else:
            prior[key] = a
        z.simplify(unrelated[index % len(unrelated)])
    base = z.K(z.BitVecSort(8), z.BitVecVal(0, 8))
    pairs = [(addresses[0], addresses[0]), (addresses[0], addresses[128]),
             (addresses[0], addresses[32])] + pairs[:16]
    for stored_at, read_at in pairs:
        original = z.Select(z.Store(base, stored_at, z.BitVecVal(90, 8)), read_at)
        assert_unsat(original != sf.forward_selects(original, {}))
    record_property("smt_difference_queries", len(pairs))
    assert len(pairs) >= 3
    assert len(literals) == 64


def test_contexts_and_clear_keep_each_retained_key_valid(monkeypatch):
    monkeypatch.setattr(sf, "_MEMO_LIMIT", 1)
    retained = []
    for ctx, coefficient in ((z.Context(), 3), (z.Context(), 5)):
        x = z.BitVec("context_address", 8, ctx)
        a = wrapped_product(x, coefficient)
        retained.append((a, sf.linearize_address(a)))
    sf.clear_memo()
    for a, before in retained:
        assert before[0]._normalized.ctx is a.ctx
        assert before == sf.linearize_address(a)
        zero, value = z.BitVecVal(0, 8, a.ctx), z.BitVecVal(90, 8, a.ctx)
        original = z.Select(z.Store(z.K(a.sort(), zero), a, value), a)
        assert_unsat(original != sf.forward_selects(original, {}))
    assert retained[0][1][0] is not retained[1][1][0]


@pytest.mark.parametrize("width", [8, 64])
def test_base_offset_consumer_survives_mid_computation_eviction(monkeypatch, width):
    import verification.block_equivalence as be
    monkeypatch.setattr(sf, "_MEMO_LIMIT", 1)
    x, y = z.BitVecs(f"base_offset_x{width} base_offset_y{width}", width)
    a, b = wrapped_product(x, 3, 5), wrapped_product(y, 3, 7)
    found = be._base_offset_uncached(a, b)
    assert found is not None
    left, right, offset = found
    assert_unsat(z.Xor(a == b, left == right + offset))


def test_full_64_bit_wraparound_alias_and_nonalias(monkeypatch):
    monkeypatch.setattr(sf, "_MEMO_LIMIT", 1)
    x = z.BitVec("full_width_address", 64)
    a = wrapped_product(x, 3)
    zero, value = z.BitVecVal(0, 8), z.BitVecVal(90, 8)
    base = z.K(z.BitVecSort(64), zero)
    memory = z.Store(base, a + z.BitVecVal((1 << 64)-1, 64), value)
    for read_at in (a-1, a):
        original = z.Select(memory, read_at)
        assert_unsat(original != sf.forward_selects(original, {}))
    wrapped_zero = z.BitVecVal((1 << 64)-1, 64) + 1
    original = z.Select(z.Store(base, wrapped_zero, value), z.BitVecVal(0, 64))
    assert_unsat(original != sf.forward_selects(original, {}))


def test_non_bv_input_remains_unsupported():
    assert sf.linearize_address(z.Bool("not_an_address")) is None
