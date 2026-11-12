"""Only native BV addition has the algebra used by address normalization."""
import z3 as z

from common import store_forwarding as sf


def _answer(formula):
    solver = z.Solver(ctx=formula.ctx)
    solver.set(timeout=1000, rlimit=100000, random_seed=0)
    solver.add(formula)
    return solver.check()


def _fixture():
    x = z.BitVec('builtin_add_x', 64)
    fake = z.Function('bvadd', z.BitVecSort(64), z.BitVecSort(64), z.BitVecSort(64))
    memory = z.Array('builtin_add_memory', z.BitVecSort(64), z.BitVecSort(8))
    return x, fake, memory


def test_uf_named_bvadd_stays_an_atomic_address():
    x, fake, memory = _fixture()
    assert fake(x, 0).decl().kind() == z.Z3_OP_UNINTERPRETED
    assert (x + 0).decl().kind() == z.Z3_OP_BADD
    fake_key = sf.linearize_address(fake(x, 0))
    real_key = sf.linearize_address(x)
    assert fake_key[0] != real_key[0]


def test_uf_named_bvadd_does_not_change_a_select_store_read():
    x, fake, memory = _fixture()
    address = fake(x, 0)
    raw = z.Select(z.Store(memory, address, z.BitVecVal(0, 8)), x)
    premise = z.And(address != x, z.Select(memory, x) == 1)
    assert _answer(z.And(premise, raw != 0)) == z.sat
    assert _answer(z.And(premise, raw == 0)) == z.unsat
    forwarded = sf.forward_selects(raw, {})
    assert _answer(z.And(premise, forwarded != raw)) == z.unsat
    assert _answer(z.And(premise, forwarded != 0)) == z.sat


def test_uf_named_bvadd_is_not_removed_as_a_base_sum():
    base, fake, memory = _fixture()
    raw = fake(base, 5)
    assert _answer(raw != base + 5) == z.sat
    assert sf._subtract_base_term(raw, base) is None


def test_builtin_add_around_a_uf_keeps_the_uf_operand():
    base, fake, memory = _fixture()
    atom = fake(base, 0)
    raw = base + atom + 5
    offset = sf._subtract_base_term(raw, base)
    assert offset is not None
    assert _answer(offset != atom + 5) == z.unsat
    assert _answer(raw != base + offset) == z.unsat


def test_builtin_add_forwarding_remains_exact():
    base, fake, memory = _fixture()
    value = z.BitVec('builtin_add_value', 8)
    stores = z.Store(z.Store(memory, base + 5, value), base + 6, z.BitVecVal(7, 8))
    raw = z.Select(stores, base + 5)
    forwarded = sf.forward_selects(raw, {})
    assert forwarded.eq(value)
    assert _answer(raw != forwarded) == z.unsat


def test_builtin_base_subtraction_remains_exact():
    base, fake, memory = _fixture()
    offset = sf._subtract_base_term(base + 5, base)
    assert offset is not None and z.is_true(z.simplify(offset == 5))
    assert _answer(base + 5 != base + offset) == z.unsat
