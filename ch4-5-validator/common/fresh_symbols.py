"""Fresh declarations disjoint from an input's free and bound symbol names."""
from z3 import FreshConst, FreshFunction, FuncDeclRef, Z3_OP_UNINTERPRETED, is_app, is_quantifier


class FreshSymbols:
    """One allocator per input/batch; keep it across that input's rewrite rounds.

    Z3's Fresh* counter does not reserve user/parser-provided names. Rejecting
    occupied names across all sorts also keeps printed declarations unambiguous.
    """

    def __init__(self, *inputs):
        self._names = set()
        self.has_overloads = False
        by_name = {}
        seen, declarations, work = set(), set(), list(inputs)
        while work:
            node = work.pop()
            key = (id(node.ctx), node.get_id())
            if isinstance(node, FuncDeclRef):
                if key in declarations:
                    continue
                declarations.add(key)
                if node.kind() == Z3_OP_UNINTERPRETED:
                    name = str(node.name())
                    prior = by_name.setdefault(name, node)
                    self.has_overloads |= not prior.eq(node)
                    self._names.add(name)
                # Map/as-array can reference a UF only as a declaration parameter.
                work.extend(p for p in node.params() if isinstance(p, FuncDeclRef))
                continue
            if key in seen:
                continue
            seen.add(key)
            if is_quantifier(node):
                self._names.update(str(node.var_name(i)) for i in range(node.num_vars()))
                work.append(node.body())
                for i in range(node.num_patterns()):
                    work.extend(node.pattern(i).children())
                work.extend(node.no_pattern(i) for i in range(node.num_no_patterns()))
            elif is_app(node):
                work.append(node.decl())
                work.extend(node.children())

    def const(self, sort, prefix="c"):
        while True:
            value = FreshConst(sort, prefix)
            name = str(value.decl().name())
            if name not in self._names:
                self._names.add(name)
                return value

    def function(self, *signature):
        while True:
            value = FreshFunction(*signature)
            name = str(value.name())
            if name not in self._names:
                self._names.add(name)
                return value
