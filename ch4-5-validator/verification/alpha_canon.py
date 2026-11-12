"""Alpha-canonical binders: rebuild every quantifier/lambda with canonical bound-variable
names over its unchanged de Bruijn body.

Bound occurrences in a z3 body are de Bruijn Vars, not named constants, so renaming
the binder symbols cannot capture anything in memory: the result is the same term up
to alpha-renaming (same meaning, same models). Alpha-equivalent subterms then become
one hash-consed AST, so id-keyed caches and syntactic sharing see them as equal.

Names matter only when printed (SMT2 round trips, records): a binder is named after
its height h (1 + the largest height of a binder inside its body), so a binder never
shadows another of the same name on any path, and the reserved prefix is checked
absent from the free constants.
"""
from z3 import QuantifierRef, is_app, is_quantifier, to_symbol, Z3_OP_UNINTERPRETED, Z3_OP_OR
from z3 import z3core as C

PREFIX = "alpha_b"


def _rebuild_binder(q, body, height):
    ctx = q.ctx
    n = q.num_vars()
    sorts = (C.Sort * n)(*[q.var_sort(i).ast for i in range(n)])
    names = (C.Symbol * n)(*[to_symbol(f"{PREFIX}{height}_{i}", ctx) for i in range(n)])
    if q.is_lambda():
        ast = C.Z3_mk_lambda(ctx.ref(), n, sorts, names, body.as_ast())
    else:
        ast = C.Z3_mk_quantifier(ctx.ref(), q.is_forall(), q.weight(), 0, None, n, sorts, names, body.as_ast())
    return QuantifierRef(ast, ctx)


def canon_binders(expr, cache=None, *, _transport_or=False):
    """expr with every binder renamed canonically (iterative post-order, memoised by id;
    the cache keeps its inputs alive, so their ids are never recycled while it lives)."""
    # Transport additionally orders builtin OR's already-canonical children.
    # It is an exact Boolean permutation, including inside binders. Keep its
    # entries separate when a caller reuses the ordinary binder cache.
    cache = {} if cache is None else cache  # key -> (input, result, binder height)
    def key_of(node):
        return (id(node.ctx), "transport_or" if _transport_or else "binders", node.get_id())
    stack = [(expr, False)]
    while stack:
        node, ready = stack.pop()
        key = key_of(node)
        if key in cache:
            continue
        kids = [node.body()] if is_quantifier(node) else (node.children() if is_app(node) else [])
        if not ready:
            stack.append((node, True))
            stack.extend((k, False) for k in kids if key_of(k) not in cache)
            continue
        done = [cache[key_of(k)] for k in kids]
        height = max((d[2] for d in done), default=0)
        new = [d[1] for d in done]
        if _transport_or and is_app(node) and node.decl().kind() == Z3_OP_OR:
            new.sort(key=lambda child: child.get_id())
        if is_quantifier(node):
            height += 1
            result = _rebuild_binder(node, new[0], height)
        elif kids and any(not a.eq(b) for a, b in zip(new, kids)):
            result = node.decl()(*new)
        else:
            if (not kids and is_app(node) and node.decl().kind() == Z3_OP_UNINTERPRETED
                    and node.decl().name().startswith(PREFIX)):
                raise ValueError(f"free constant {node} uses the reserved binder prefix")
            result = node
        cache[key] = (node, result, height)
    return cache[key_of(expr)][1]


def binder_capture_risk(term):
    """True iff printing `term` as SMT2 could change its meaning: a binder q nested under an
    enclosing binder with one of q's own names, whose body refers to that enclosing variable
    (Z3's printer does not rename, so parsing binds the reference to q instead). Fast path:
    without two binders sharing a name there is no shadowing at all."""
    from z3 import get_var_index, is_var
    names, seen, work = set(), set(), [term]
    duplicate = False
    while work and not duplicate:
        t = work.pop()
        if t.get_id() in seen:
            continue
        seen.add(t.get_id())
        if is_quantifier(t):
            for i in range(t.num_vars()):
                if t.var_name(i) in names:
                    duplicate = True
                names.add(t.var_name(i))
            work.append(t.body())
        elif is_app(t):
            work.extend(t.children())
    if not duplicate:
        return False
    seen = set()
    stack = [(term, ())]  # (node, names of the enclosing bound variables, innermost last)
    while stack:
        node, outer = stack.pop()
        if (node.get_id(), outer) in seen:
            continue
        seen.add((node.get_id(), outer))
        if is_quantifier(node):
            own = tuple(node.var_name(i) for i in range(node.num_vars()))
            if set(own) & set(outer):
                refs, visited = [(node.body(), 0)], set()
                while refs:
                    t, depth = refs.pop()
                    if (t.get_id(), depth) in visited:
                        continue
                    visited.add((t.get_id(), depth))
                    if is_var(t):
                        j = get_var_index(t) - depth - len(own)
                        if 0 <= j < len(outer) and outer[len(outer) - 1 - j] in own:
                            return True
                    elif is_quantifier(t):
                        refs.append((t.body(), depth + t.num_vars()))
                    elif is_app(t):
                        refs.extend((c, depth) for c in t.children())
            stack.append((node.body(), outer + tuple(reversed(own))))
        elif is_app(node):
            stack.extend((c, outer) for c in node.children())
    return False
