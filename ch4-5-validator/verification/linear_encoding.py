"""Exact linear-integer reading of bit-vector formulas (a refutation route).

Limb arithmetic that both sides build differently (holiman MUL in EVM operand
order vs compileEVMMul's swapped operands and x86 add order, borrow chains,
carry bits) is a linear identity once products are atoms, but bit-blasting
cannot see it: the carry-sum reassociation of a 256-bit product is unknown
after minutes. Read as integers it is a few hundred LIA variables.

`lia_query(F)` is an over-approximation of F: every BV model of F extends to
an integer model (atoms take their BV values, k the quotients, bits the
bits). Only UNSAT transfers back; SAT/unknown establish nothing.
"""

from z3 import (And, Concat, Distinct, Extract, If, Implies, Int, IntVal, Not, Or, Sum, simplify,
                is_app, is_bool, is_bv, is_bv_value, is_false, is_true,
                Z3_OP_AND, Z3_OP_BADD, Z3_OP_BAND, Z3_OP_BMUL, Z3_OP_BNOT, Z3_OP_BOR, Z3_OP_CONCAT,
                Z3_OP_DISTINCT, Z3_OP_EQ, Z3_OP_EXTRACT, Z3_OP_IMPLIES, Z3_OP_ITE, Z3_OP_NOT, Z3_OP_OR,
                Z3_OP_UGEQ, Z3_OP_UGT, Z3_OP_ULEQ, Z3_OP_ULT, Z3_OP_ZERO_EXT, Bool)

# Bitwise ops are read bit by bit (exact for 0/1 integers); wider ones stay atoms.
_MAX_BITWISE_WIDTH = 64


def _zext_operand(t):
    """k if t is Concat(0, x) / ZeroExt(n, x) with |x| = k (a zero-extended operand), else None."""
    if is_app(t) and t.decl().kind() == Z3_OP_ZERO_EXT:
        return t.arg(0).size()
    if (is_app(t) and t.decl().kind() == Z3_OP_CONCAT and t.num_args() == 2
            and is_bv_value(t.arg(0)) and t.arg(0).as_long() == 0):
        return t.arg(1).size()
    return None


class _Encoder:
    def __init__(self):
        self.memo, self.side, self.count = {}, [], 0
        self.applications = {}  # decl -> opaque applications, for congruence

    def fresh(self, hi=None, lo=0):
        self.count += 1
        v = Int(f"lia!{self.count}")
        if lo is not None:
            self.side.append(v >= lo)
        if hi is not None:
            self.side.append(v <= hi)
        return v

    def term(self, t):
        """(integer expression, upper bound) of a BV term; value in [0, bound]."""
        key = t.get_id()
        if key not in self.memo:
            self.memo[key] = self._bv(t)
        return self.memo[key]

    def value(self, t):
        return self.term(t)[0]

    def _atom(self, t):
        bound = (1 << t.size()) - 1
        if is_app(t) and t.decl().kind() == Z3_OP_BMUL and t.num_args() == 2:
            widths = [_zext_operand(a) for a in t.children()]
            if None not in widths and sum(widths) <= t.size():
                bound = ((1 << widths[0]) - 1) * ((1 << widths[1]) - 1)  # product of zext operands cannot wrap
        if is_app(t) and t.num_args() > 0 and t.decl().kind() != Z3_OP_BMUL:  # products are hash-consed (bv_sort_ac)
            self.applications.setdefault(t.decl(), []).append(t)
        return self.fresh(bound), bound

    def congruence(self):
        """Equal arguments give equal results (holds for any function, so in every model)."""
        axioms = []
        for apps in list(self.applications.values()):
            for i, s in enumerate(apps):
                for t in apps[i + 1:]:
                    same = []
                    for x, y in zip(s.children(), t.children()):
                        if x.eq(y):
                            continue
                        if not is_bv(x):
                            break  # arrays etc.: only syntactic equality is readable here
                        same.append(self.value(x) == self.value(y))
                    else:
                        axioms.append(Implies(And(*same), self.value(s) == self.value(t)))
        return axioms

    def _wrap(self, expr, lo, hi, w):
        """expr mod 2^w for expr in [lo, hi]: r = expr - 2^w*k, k in [lo >> w, hi >> w]."""
        if lo >= 0 and hi < (1 << w):
            return expr, hi
        r = self.fresh((1 << w) - 1)
        self.side.append(r == expr - (1 << w) * self.fresh(hi >> w, lo >> w))
        return r, (1 << w) - 1

    @staticmethod
    def _signed(c, w):
        """c or c - 2^w, whichever is nearer 0: -1 keeps k in {0, 1} instead of [0, 2^w)."""
        c %= 1 << w
        return c - (1 << w) if c > (1 << (w - 1)) else c

    def _bits(self, t):
        key = ("bits", t.get_id())
        if key not in self.memo:
            bits = [self.fresh(1) for _ in range(t.size())]
            self.side.append(self.value(t) == Sum([b * (1 << i) for i, b in enumerate(bits)]))
            self.memo[key] = bits
        return self.memo[key]

    def _bv(self, t):
        if is_bv_value(t):
            return IntVal(t.as_long()), t.as_long()
        if not is_app(t):
            return self._atom(t)
        kind, w, args = t.decl().kind(), t.size(), t.children()
        if kind == Z3_OP_BADD:
            expr, lo, hi = [], 0, 0
            for a in args:
                if is_bv_value(a):
                    c = self._signed(a.as_long(), w)
                    expr.append(IntVal(c))
                    lo, hi = lo + min(c, 0), hi + max(c, 0)
                else:
                    e, b = self.term(a)
                    expr.append(e)
                    hi += b
            return self._wrap(Sum(expr), lo, hi, w)
        variables = [a for a in args if not is_bv_value(a)]
        if kind == Z3_OP_BMUL and len(variables) == 1:
            c = 1
            for a in args:
                c = c * a.as_long() if is_bv_value(a) else c
            c = self._signed(c, w)
            e, b = self.term(variables[0])
            return self._wrap(c * e, min(c * b, 0), max(c * b, 0), w)
        if kind == Z3_OP_ZERO_EXT:
            return self.term(args[0])
        if kind == Z3_OP_CONCAT:
            expr, bound = IntVal(0), 0
            for a in args:
                e, b = self.term(a)
                expr, bound = expr * (1 << a.size()) + e, (bound << a.size()) + b
            return expr, bound
        if kind == Z3_OP_EXTRACT:
            hi, lo = t.params()
            x = args[0]
            top = self.fresh((1 << (x.size() - hi - 1)) - 1) if hi + 1 < x.size() else IntVal(0)
            mid = self.fresh((1 << (hi - lo + 1)) - 1)
            low = self.fresh((1 << lo) - 1) if lo > 0 else IntVal(0)
            self.side.append(self.value(x) == top * (1 << (hi + 1)) + mid * (1 << lo) + low)
            return mid, (1 << (hi - lo + 1)) - 1
        if kind == Z3_OP_ITE:
            (a, ba), (b, bb) = self.term(args[1]), self.term(args[2])
            return If(self.formula(args[0]), a, b), max(ba, bb)
        if kind == Z3_OP_BNOT:
            return (1 << w) - 1 - self.value(args[0]), (1 << w) - 1
        if kind in (Z3_OP_BOR, Z3_OP_BAND) and w <= _MAX_BITWISE_WIDTH:
            columns = [self._bits(a) for a in args]
            out = []
            for i in range(w):
                o, xs = self.fresh(1), [col[i] for col in columns]
                if kind == Z3_OP_BOR:
                    self.side += [o >= x for x in xs] + [o <= Sum(xs)]
                else:
                    self.side += [o <= x for x in xs] + [o >= Sum(xs) - (len(xs) - 1)]
                out.append(o)
            return Sum([o * (1 << i) for i, o in enumerate(out)]), (1 << w) - 1
        return self._atom(t)

    def formula(self, f):
        key = ("bool", f.get_id())
        if key not in self.memo:
            self.memo[key] = self._bool(f)
        return self.memo[key]

    def _bool(self, f):
        if is_true(f) or is_false(f):
            return f
        if not is_app(f):
            return self._fresh_bool()
        kind, args = f.decl().kind(), f.children()
        connectives = {Z3_OP_AND: And, Z3_OP_OR: Or, Z3_OP_NOT: Not, Z3_OP_IMPLIES: Implies, Z3_OP_ITE: If}
        if kind in connectives:
            return connectives[kind](*[self.formula(a) for a in args])
        if kind == Z3_OP_EQ and is_bool(args[0]):
            return self.formula(args[0]) == self.formula(args[1])
        if kind == Z3_OP_EQ and is_bv(args[0]):
            return self.value(args[0]) == self.value(args[1])
        if kind == Z3_OP_DISTINCT and is_bv(args[0]):
            return Distinct(*[self.value(a) for a in args])
        compare = {Z3_OP_ULEQ: lambda a, b: a <= b, Z3_OP_ULT: lambda a, b: a < b,
                   Z3_OP_UGEQ: lambda a, b: a >= b, Z3_OP_UGT: lambda a, b: a > b}
        if kind in compare:
            return compare[kind](self.value(args[0]), self.value(args[1]))
        return self._fresh_bool()  # any other atom: an unconstrained Boolean only adds models

    def _fresh_bool(self):
        self.count += 1
        return Bool(f"lia_b!{self.count}")


def lia_query(formula):
    """Integer over-approximation of `formula` (see module doc), or None if too deep."""
    encoder = _Encoder()
    try:
        root = encoder.formula(formula)
        congruence = encoder.congruence()
    except RecursionError:
        return None  # ponytail: recursive encoder; deep Store chains fall back to the other routes
    return And(root, *encoder.side, *congruence)


def split_limb_joins(formula):
    """(old, new) candidates Concat(.., Extract(h, l, X), Y, ..) -> Concat(.., Extract(h, 0, X), ..).

    A limb stored and reloaded byte-wise comes back as such a concat once the
    simplifier pushes Extract(l-1, 0, ·) into X's sum of products, and the low
    byte then no longer shares X's atoms. Y must be the simplified low part of
    X; the caller still proves old == new before rewriting.
    """
    pairs, seen, work = [], set(), [formula]
    while work:
        t = work.pop()
        if t.get_id() in seen or not is_app(t):
            continue
        seen.add(t.get_id())
        work.extend(t.children())
        if t.decl().kind() != Z3_OP_CONCAT:
            continue
        args, out, i = t.children(), [], 0
        while i < len(args):
            x = args[i]
            if (i + 1 < len(args) and is_app(x) and x.decl().kind() == Z3_OP_EXTRACT
                    and x.params()[1] == args[i + 1].size()
                    and simplify(Extract(x.params()[1] - 1, 0, x.arg(0)), bv_sort_ac=True).eq(args[i + 1])):
                out.append(Extract(x.params()[0], 0, x.arg(0)))
                i += 2
            else:
                out.append(x)
                i += 1
        if len(out) < len(args):
            pairs.append((t, Concat(*out) if len(out) > 1 else out[0]))
    return pairs
