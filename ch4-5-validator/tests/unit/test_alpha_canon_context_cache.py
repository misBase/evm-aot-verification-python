"""canon_binders cache entries must not cross Z3 Contexts (native ids are per-Context)."""
import z3 as z

from verification import alpha_canon as module
def answer(formula):
    solver = z.Solver(ctx=formula.ctx)
    solver.set(timeout=2000, rlimit=100000, random_seed=0)
    solver.add(formula)
    return str(solver.check())


def test_cache_is_scoped_by_context():
    left, right = z.Context(), z.Context()
    padding = z.BitVec('padding', 8, ctx=left)  # align two live native ID namespaces without mocking
    a = z.BitVec('a', 8, ctx=left)
    b, c = z.BitVec('b', 8, ctx=right), z.BitVec('c', 8, ctx=right)
    impossible, possible = a != a, b != c
    assert impossible.get_id() == possible.get_id()
    cache = {}
    module.canon_binders(impossible, cache)
    rewritten = module.canon_binders(possible, cache)
    assert rewritten.ctx is right
    assert answer(possible) == answer(rewritten) == 'sat'
    assert answer(rewritten != possible) == 'unsat'


def test_same_context_binder_modes_and_clear():
    ctx = z.Context()
    x, k = z.BitVec('x', 8, ctx=ctx), z.BitVec('k', 8, ctx=ctx)
    original = z.Lambda(x, x + 1)
    cache = {}
    normalized = module.canon_binders(original, cache)
    assert module.canon_binders(original, cache) is normalized
    assert answer(z.Select(normalized, k) != z.Select(original, k)) == 'unsat'
    formula = z.Or(k == 2, k == 1)
    ordinary = module.canon_binders(formula, cache)
    transport = module.canon_binders(formula, cache, _transport_or=True)
    assert answer(ordinary != transport) == 'unsat'
    cache.clear()
    assert normalized.eq(module.canon_binders(original, cache))
