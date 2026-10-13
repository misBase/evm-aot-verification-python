"""AST-id-independent structural hash of a z3 expression.

Commutative operators hash their children as a multiset (z3's simplifier orders
AC arguments by AST id, which differs between processes); symbol names have
process-specific numbers masked (id(runtime) addresses, fresh-name counters).
"""
import hashlib
import re

from z3 import (Z3_OP_AND, Z3_OP_OR, Z3_OP_EQ, Z3_OP_DISTINCT, Z3_OP_BADD, Z3_OP_BMUL, Z3_OP_BAND, Z3_OP_BOR,
                Z3_OP_BXOR, Z3_OP_IFF, Z3_OP_XOR, is_app, is_quantifier, is_var, get_var_index)

AC = {Z3_OP_AND, Z3_OP_OR, Z3_OP_EQ, Z3_OP_DISTINCT, Z3_OP_BADD, Z3_OP_BMUL, Z3_OP_BAND, Z3_OP_BOR, Z3_OP_BXOR,
      Z3_OP_IFF, Z3_OP_XOR}


def _mask(name):
    return re.sub(r"!\d+", "!N", re.sub(r"\d{6,}", "N", name))


def canon_hash(e, memo=None):
    memo = {} if memo is None else memo
    stack = [(e, False)]
    while stack:
        x, done = stack.pop()
        k = x.get_id()
        if k in memo:
            continue
        if is_quantifier(x):
            kids = [x.body()]
        elif is_app(x):
            kids = x.children()
        else:
            kids = []
        if not done:
            stack.append((x, True))
            stack.extend((c, False) for c in kids if c.get_id() not in memo)
            continue
        if is_var(x):
            head = f"var{get_var_index(x)}"
        elif is_quantifier(x):
            head = f"q{x.is_lambda()}{x.num_vars()}" + ",".join(str(x.var_sort(i)) for i in range(x.num_vars()))
        else:
            d = x.decl()
            params = ",".join(str(p) for p in d.params()) if d.params() else ""
            head = _mask(d.name()) + "|" + params + "|" + str(x.sort())
            if not kids:
                head += "|" + _mask(str(x))
        hs = [memo[c.get_id()] for c in kids]
        if is_app(x) and not is_quantifier(x) and x.decl().kind() in AC:
            hs = sorted(hs)
        memo[k] = hashlib.sha256((head + "(" + ",".join(hs) + ")").encode()).hexdigest()[:20]
    return memo[e.get_id()]


if __name__ == "__main__":
    from z3 import BitVec, And
    x, y = BitVec("x", 8), BitVec("y", 8)
    assert canon_hash(x + y == 1) == canon_hash(1 == y + x)
    assert canon_hash(And(x > 0, y > 0)) == canon_hash(And(y > 0, x > 0))
    assert canon_hash(x - y == 1) != canon_hash(y - x == 1)
    print("ok")
