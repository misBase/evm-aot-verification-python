"""Complete finite block theorems at the pre-TAG boundary.

A local theorem is diagnostic until block_program proves Base and every edge.
SAT from a havoc state is an unclosed obligation, not a concrete-program refutation.
"""
from __future__ import annotations

import re
from collections import Counter
from itertools import count
from dataclasses import dataclass, field, replace
from hashlib import sha256
from pathlib import Path
from enum import Enum
from time import monotonic
from typing import Tuple

from z3 import (And, Not, Or, is_expr, Solver, SolverFor, sat, unsat, simplify, is_bool, is_app, is_bv_value,
                is_quantifier, Z3_BOOL_SORT, Z3_BV_SORT, Z3_ARRAY_SORT,
                substitute, BitVecSort, FreshFunction, Z3_OP_BMUL, Z3_OP_UNINTERPRETED, ULE,
                is_and, is_array, FreshConst, Select, BoolVal, Z3_OP_ITE, is_false, is_bv, BitVecVal,
                Implies, ULT, Var, substitute_funs, Extract, If, Z3_OP_EXTRACT, Z3_OP_BADD, Z3_OP_CONCAT, Z3_OP_EQ, Z3_OP_SELECT, is_true,
                is_store, is_select, substitute_vars, Concat, Z3_OP_BUDIV, Z3_OP_BUDIV_I, Z3_OP_BOR, Store,
                is_not, is_eq, is_distinct, ForAll, Z3_get_array_arity, Then, Lambda, ArraySort, Const, FuncDeclRef,
                UGT, Z3_OP_BSHL, Z3_OP_BLSHR, Z3_OP_BASHR, BoolSort)
from concurrent.futures import TimeoutError as FutureTimeout
from concurrent.futures import BrokenExecutor
from random import Random
from state.host_gas import HOST_GAS_UPPER_BOUNDS
from verification import proof_cache

from verification.block_specialization import BlockSpecialization
from verification.block_relation import BlockRelationSchema
from verification.linear_encoding import lia_query, split_limb_joins
from common.store_forwarding import _memoized, _subtract_base_term, forward_selects, linearize_address, unshift_store_chain
from verification.alpha_canon import binder_capture_risk, canon_binders
from verification.loop_induction import run_evm_segment, run_x86_segment, terminal_observable_conditions
from x86_64.aot_profile import GO_HPC_EVM_PROFILE
from x86_64.cfg_state import PrefixSolver


def _semantic_sources_digest():
    root = Path(__file__).resolve().parents[1]
    value = sha256()
    for package in ("common", "state", "evm_ir", "x86_64", "verification"):
        for path in sorted((root / package).rglob("*.py")):
            value.update(str(path.relative_to(root)).encode())
            value.update(path.read_bytes())
    return value.hexdigest()


_SEMANTIC_SOURCES = _semantic_sources_digest()


def _bv_array_formula(formula):
    def supported(sort):
        if sort.kind() in (Z3_BOOL_SORT, Z3_BV_SORT):
            return True
        return sort.kind() == Z3_ARRAY_SORT and supported(sort.domain()) and supported(sort.range())
    work, seen = [formula], set()
    while work:
        term = work.pop()
        if term.get_id() in seen:
            continue
        seen.add(term.get_id())
        # Lambda is an array constructor supported by Z3's array/BV tactic.
        if not supported(term.sort()) or (is_quantifier(term) and not term.is_lambda()):
            return False
        work.extend(term.children())
    return True


def _solver(timeout_ms, formula=None):
    # Concrete SP eliminates Int from most block queries. Keep the general
    # solver for mixed sorts and quantifiers; neither route changes assertions.
    solver = SolverFor("QF_AUFBV") if formula is not None and _bv_array_formula(formula) else Solver()
    solver.set(timeout=timeout_ms)
    return solver


def solve_query(formula, timeout_ms, trust_unknown=True):
    """Retry incomplete array tactics with the same query and remaining budget.

    Answers go through proof_cache (env BLOCK_PROOF_CACHE): an alpha-equivalent
    query decided in any earlier run, or timed out with at least this budget,
    is not solved again. trust_unknown=False solves a cached timeout again:
    for checks expected SAT (entry_nonempty), where one timeout under load
    would otherwise fail every later node of that shape at once.
    """
    key = proof_cache.query_key("check", formula) if proof_cache.enabled() else None
    if key is not None:
        cached = proof_cache.cached_answer(key, timeout_ms)
        if cached is not None and (trust_unknown or cached != "unknown"):
            return cached
    answer = _solve_query(formula, timeout_ms)
    if key is not None:
        proof_cache.record_answer(key, answer, timeout_ms)
    return answer


def _solve_query(formula, timeout_ms):
    end = monotonic() + timeout_ms / 1000
    solver = _solver(timeout_ms, formula)
    solver.add(formula)
    answer = str(solver.check())
    # Lambda arrays passed to UFs can be incomplete in QF_AUFBV even though
    # all sorts pass the guard. A general solver can discharge those queries.
    remaining = int((end - monotonic()) * 1000)
    if (answer == "unknown" and remaining > 0
            and "incomplete" in getattr(solver, "reason_unknown", lambda: "")()):
        solver = _solver(remaining)
        solver.add(formula)
        answer = str(solver.check())
    return answer


def _array_argument_ufs(formula):
    """Uninterpreted functions of arity >= 1 with an array-sorted parameter,
    including applications under lambda/quantifier binders; None when some
    function is referenced as a value (as-array, map), which substitute_funs
    does not rewrite."""
    seen, found, work = set(), {}, [formula]
    while work:
        term = work.pop()
        if term.get_id() in seen:
            continue
        seen.add(term.get_id())
        if is_quantifier(term):
            work.append(term.body())
            continue
        if not is_app(term):
            continue
        f = term.decl()
        if any(isinstance(p, FuncDeclRef) for p in f.params()):
            return None
        if (f.kind() == Z3_OP_UNINTERPRETED and f.arity() > 0
                and any(f.domain(i).kind() == Z3_ARRAY_SORT for i in range(f.arity()))):
            found[f.get_id()] = f
        work.extend(term.children())
    return sorted(found.values(), key=lambda f: (f.name(), f.get_id()))


def _binder_argument_ufs(formula):
    """Uninterpreted functions of arity >= 1 with an application (outside
    binders) whose arguments contain a lambda/quantifier: sha3_bytes_N over
    bytes read through the R15 offset view λa. M[a - R15] (PoolManager 5802),
    and every UF applied to such a term (host_gas_sload of that hash)."""
    found, binder, seen, work = {}, {}, set(), [(formula, False)]
    order = []
    while work:  # post-order: a term's binder flag needs its children's
        term, ready = work.pop()
        if term.get_id() in seen:
            continue
        if is_quantifier(term):
            seen.add(term.get_id())
            binder[term.get_id()] = True
            continue
        if not is_app(term):
            seen.add(term.get_id())
            binder[term.get_id()] = False
            continue
        if not ready:
            work.append((term, True))
            work.extend((c, False) for c in term.children() if c.get_id() not in seen)
            continue
        seen.add(term.get_id())
        inner = any(binder[c.get_id()] for c in term.children())
        binder[term.get_id()] = inner
        f = term.decl()
        if inner and f.kind() == Z3_OP_UNINTERPRETED and f.arity() > 0 and f.get_id() not in found:
            found[f.get_id()] = f
            order.append(f)
    return sorted(order, key=lambda f: (f.name(), f.get_id()))


def _all_ufs(formula):
    """Every uninterpreted function of arity >= 1, under binders too."""
    seen, found, work = set(), {}, [formula]
    while work:
        term = work.pop()
        if term.get_id() in seen:
            continue
        seen.add(term.get_id())
        if is_quantifier(term):
            work.append(term.body())
            continue
        if not is_app(term):
            continue
        f = term.decl()
        if f.kind() == Z3_OP_UNINTERPRETED and f.arity() > 0:
            found[f.get_id()] = f
        work.extend(term.children())
    return sorted(found.values(), key=lambda f: (f.name(), f.get_id()))


def _witness_tiers(formula):
    """Growing sets of functions to restrict to constants (sat_by_constant_array_ufs):
    array-parameter UFs, then also UFs over binder terms, then every UF; each set
    strictly larger than the last. [] if some function is referenced as a value."""
    arrays = _array_argument_ufs(formula)
    if arrays is None:
        return []
    tiers, chosen = [], {}
    for group in (arrays, _binder_argument_ufs(formula), _all_ufs(formula)):
        grown = {**chosen, **{f.get_id(): f for f in group}}
        if len(grown) > len(chosen):
            chosen = grown
            tiers.append(sorted(chosen.values(), key=lambda f: (f.name(), f.get_id())))
    return tiers


def sat_by_constant_array_ufs(formula, timeout_ms):
    """"sat" with a checked witness, else "unknown"; never "unsat".

    An uninterpreted function applied to a lambda array (sha3_slice over a
    memory window) makes Z3's array theory incomplete: such a query is never
    answered "sat" (even ULE(g(h(lambda i. m[x+i])), 100) is unknown), while
    "unsat" is unaffected. A witness restricts every such function f to a
    constant function c_f (a fresh constant of its range): F' = F[f := c_f]
    has no array arguments left under UFs. A model M of F' extended with
    f := (lambda args. M(c_f)) is a model of F (substitution lemma; f does
    not occur in F'), so SAT(F') implies SAT(F). The model is evaluated on F'
    and only a literal True counts. UNSAT(F') proves nothing (F may need f
    non-constant) and is reported as "unknown".

    The lemma holds for any set of UFs, so the restriction grows in tiers
    (_witness_tiers) until one is SAT: the same incompleteness arises with a
    lambda inside a bit-vector argument (sha3_bytes_58 of bytes read through
    the R15 offset view, PoolManager 5802 model_domain_nonempty: no
    array-parameter UF, so the first tier is empty), and host_gas_sload of
    that hash is only bounded above, so a constant one always fits.
    """
    tiers = _witness_tiers(formula)
    end = monotonic() + timeout_ms / 1000
    for n, functions in enumerate(tiers):
        left = int((end - monotonic()) * 1000)
        if left <= 0:
            break
        restricted = substitute_funs(formula, *[(f, FreshConst(f.range(), "const_uf")) for f in functions])
        solver = _solver(left // (len(tiers) - n), restricted)  # an equal share of what is left
        solver.add(restricted)
        if solver.check() == sat and is_true(solver.model().eval(restricted, model_completion=True)):
            return "sat"
    return "unknown"


def unsat_core(assertions, goal, timeout_ms, outcome=None):
    """Indices of `assertions` in an unsat core of assertions ∧ goal, or None.
    `outcome` (optional dict) gets the solver's answer as "answer"."""
    key = proof_cache.query_key("core", *assertions, goal) if proof_cache.enabled() else None
    if key is not None:
        cached = proof_cache.lookup(key)
        if isinstance(cached, list):
            if outcome is not None:
                outcome["answer"] = "unsat"
            return cached
    core = _unsat_core(assertions, goal, timeout_ms, outcome)
    if key is not None and core is not None:
        proof_cache.store(key, core)
    return core


def _unsat_core(assertions, goal, timeout_ms, outcome=None):
    solver = _solver(timeout_ms, And(*assertions, goal))
    tracks = [FreshConst(BoolVal(True).sort(), "core") for _ in assertions]
    for assertion, track in zip(assertions, tracks):
        solver.assert_and_track(assertion, track)
    solver.add(goal)
    answer = solver.check()
    if outcome is not None:
        outcome["answer"] = str(answer)
    if answer != unsat:
        return None
    core = {t.get_id() for t in solver.unsat_core()}
    return [i for i, t in enumerate(tracks) if t.get_id() in core]


def digest(value):
    return sha256(repr(value).encode()).hexdigest()


def host_model_axioms(expressions):
    """Ground instances of the explicit, bounded host-cost oracle model.

    These are model axioms, not input assumptions or learned path conditions.
    Instantiating for all terms on both sides permits each side's coverage to
    be checked in the SAME oracle model. No arbitrary pending constraint is
    admitted here. The table and this implementation are bound to the identity.
    """
    seen, axioms, work = set(), {}, list(expressions)
    while work:
        term = work.pop()
        if term.get_id() in seen:
            continue
        seen.add(term.get_id())
        if not is_app(term):
            continue
        name = str(term.decl().name())
        if term.decl().kind() == Z3_OP_UNINTERPRETED and name.startswith("host_gas_"):
            opcode = name[len("host_gas_"):].upper()
            if opcode in HOST_GAS_UPPER_BOUNDS:
                if term.size() != 64 or any(arg.size() != 256 for arg in term.children()):
                    raise ValueError("host gas oracle signature mismatch")
                axioms[term.sexpr()] = ULE(term, HOST_GAS_UPPER_BOUNDS[opcode])
        work.extend(term.children())
    return tuple(axioms[k] for k in sorted(axioms))


def _generalize_products(formula):
    """formula with every bvmul subterm replaced by a fresh constant.

    Valid(result) implies Valid(formula), which is a substitution instance.
    """
    seen, products, work = set(), {}, [formula]
    while work:
        t = work.pop()
        if t.get_id() in seen or not is_app(t):
            continue
        seen.add(t.get_id())
        if t.decl().kind() == Z3_OP_BMUL:
            products[t.get_id()] = t
            continue
        work.extend(t.children())
    return substitute(formula, *[(p, FreshConst(p.sort(), "gen")) for p in products.values()]) if products else formula


def _generalize_product_words(formula, min_width=128):
    """formula with every maximal concat of >= min_width bits that contains a
    bvmul replaced by a fresh constant (None when there is none).

    A limb-wise 256-bit product is one such word; a borrow-chain hint about it
    (Aave 11831 rayDiv: `P == 1e27` iff neither `P - 1e27` nor `1e27 - P`
    borrows) is a tautology about the word, while _generalize_products leaves
    the limbs as sums of fresh products with carries (30s unknown -> 0.0s).
    Valid(result) implies Valid(formula), which is a substitution instance.
    """
    with_mul, seen, words, work = {}, set(), {}, [formula]

    def has_mul(t):
        stack = [t]
        while stack:
            u = stack[-1]
            if u.get_id() in with_mul:
                stack.pop()
                continue
            kids = [c for c in u.children() if c.get_id() not in with_mul] if is_app(u) else []
            if kids:
                stack.extend(kids)
                continue
            stack.pop()
            with_mul[u.get_id()] = is_app(u) and (u.decl().kind() == Z3_OP_BMUL
                                                  or any(with_mul[c.get_id()] for c in u.children()))
        return with_mul[t.get_id()]

    while work:
        t = work.pop()
        if t.get_id() in seen or not is_app(t):
            continue
        seen.add(t.get_id())
        if is_bv(t) and t.decl().kind() == Z3_OP_CONCAT and t.size() >= min_width and has_mul(t):
            words[t.get_id()] = t
            continue
        work.extend(t.children())
    return substitute(formula, *[(w, FreshConst(w.sort(), "word")) for w in words.values()]) if words else None


def div_quotient_axioms(expressions):
    """y != 0 => q[2n-1:n] == 0 for every q = x / y whose operands both fit n bits.

    A tautology (q <= x < 2^n once y >= 1), not an assumption: it is the x86
    `div r64` quotient-fits hint (RDX = 0), which the executor records in the
    state's assumptions where block obligations never read it. bvudiv_i is
    bvudiv off y == 0, hence the guard.
    """
    seen, axioms, work = set(), {}, list(expressions)
    while work:
        term = work.pop()
        if term.get_id() in seen or not is_app(term):
            continue
        seen.add(term.get_id())
        work.extend(term.children())
        if term.decl().kind() not in (Z3_OP_BUDIV, Z3_OP_BUDIV_I) or term.size() % 2:
            continue
        n = term.size() // 2
        x, y = term.arg(0), term.arg(1)
        if all(simplify(Extract(2 * n - 1, n, v)).eq(BitVecVal(0, n)) for v in (x, y)):
            axioms[term.sexpr()] = Implies(Extract(n - 1, 0, y) != 0, Extract(2 * n - 1, n, term) == 0)
    return tuple(axioms[k] for k in sorted(axioms))


def _nonlinear_mul_terms(formula):
    """BV multiplications whose operands are all non-literal — the ones that
    force the eager bit-blaster to build a full multiplier circuit."""
    found, seen, work = {}, set(), [formula]
    while work:
        term = work.pop()
        if term.get_id() in seen or not is_app(term):
            continue
        seen.add(term.get_id())
        if (term.decl().kind() == Z3_OP_BMUL and term.num_args() > 1
                and not any(is_bv_value(arg) for arg in term.children())):
            found[term.get_id()] = term
        work.extend(term.children())
    return list(found.values())


def abstract_nonlinear_mul(formula, max_rounds=8, functions=None):
    """Forget multiplication semantics, retaining congruence in a fresh UF.

    Every original model extends to this formula by interpreting the UF as
    bvmul. Only UNSAT transfers back; abstract SAT/unknown establish nothing.
    """
    original, changed = formula, False
    formula = simplify(formula)
    functions = {} if functions is None else functions  # caller may keep the UFs to undo the abstraction
    for _ in range(max_rounds):
        terms = _nonlinear_mul_terms(formula)
        if not terms:
            return formula, changed
        pairs = []
        for term in terms:
            sort = BitVecSort(term.size())
            key = (term.size(), term.num_args())
            if key not in functions:
                functions[key] = FreshFunction(*([sort] * (term.num_args() + 1)))
            uf = functions[key]
            pairs.append((term, uf(*term.children())))
        formula = substitute(formula, *pairs)
        changed = True
    # Deeply nested products: leave the obligation to the exact solver rather
    # than reporting a half-abstracted formula as the thing that was proved.
    return original, False


def mul_truncation_axioms(formula, functions):
    """p[k-1:0] == q for abstracted products p = x*y (n bits), q = u*v (k < n bits), u = x[k-1:0], v = y[k-1:0].

    Valid for bvmul ((x*y) mod 2^k depends only on x, y mod 2^k), so UNSAT
    still transfers back. simplify pushes a product's low extract down to a
    product of the operands' low parts (byte-wise stack reloads, 64-bit limbs
    of zero-extended 128-bit products); without this the abstraction treats
    the two products as unrelated.
    """
    decls = {f.get_id() for f in functions.values()}
    apps, seen, work = {}, set(), [formula]
    while work:
        t = work.pop()
        if t.get_id() in seen or not is_app(t):
            continue
        seen.add(t.get_id())
        work.extend(t.children())
        if t.decl().get_id() in decls and t.num_args() == 2:
            apps[t.get_id()] = t
    by_operands = {(t.size(), *sorted((t.arg(0).get_id(), t.arg(1).get_id()))): t for t in apps.values()}
    sizes = {t.size() for t in apps.values()}
    axioms = []
    for p in apps.values():
        for k in sorted(s for s in sizes if s < p.size()):
            low = [simplify(Extract(k - 1, 0, a)) for a in p.children()]
            q = by_operands.get((k, *sorted(x.get_id() for x in low)))
            if q is not None:
                axioms.append(Extract(k - 1, 0, p) == q)
    return axioms


def concretize_mul(formula, functions):
    """Read abstract_nonlinear_mul's UFs as bvmul again.

    Lemmas proved over the abstraction hold for every UF interpretation, so
    also for bvmul: a model of the original formula is a model of the
    rewritten one read this way, and UNSAT of the result transfers back.
    Unification shares the squared word counts; exact products can then
    bound the small ones (e.g. msize < 96) that the UF leaves free.
    """
    pairs = []
    for f in functions.values():
        product = Var(0, f.domain(0))
        for i in range(1, f.arity()):
            product = product * Var(i, f.domain(i))
        pairs.append((f, product))
    return substitute_funs(formula, *pairs) if pairs else formula


def _abstract_squares(formula, functions):
    decls = {f.get_id() for f in functions.values()}
    squares, seen, work = {}, set(), [formula]
    while work:
        t = work.pop()
        if t.get_id() in seen or not is_app(t):
            continue
        seen.add(t.get_id())
        if t.decl().get_id() in decls and t.num_args() == 2 and t.arg(0).eq(t.arg(1)):
            squares[t.get_id()] = t
        work.extend(t.children())
    return list(squares.values())


def square_shift_axioms(formula, functions, seeds=4):
    """Valid facts `v == u + d ⇒ sq(v) == sq(u) + 2d·u + d²` for hidden squares.

    A ring identity modulo 2^n, so every instance holds when the UF is read as
    bvmul, whatever d is: conjoining keeps every original model. d is only
    guessed (v - u under random leaf values); a wrong guess is a useless but
    harmless axiom. Telescoped memory costs C(w+1) - C(w) become linear.
    """
    squares = _abstract_squares(formula, functions)
    if len(squares) < 2:
        return []
    opaque = _uf_app_constants(*(s.arg(0) for s in squares))
    hide = (lambda t: substitute(t, *opaque)) if opaque else (lambda t: t)
    leaves, seen, work = {}, set(), [hide(s.arg(0)) for s in squares]
    while work:
        t = work.pop()
        if t.get_id() in seen or not is_app(t):
            continue
        seen.add(t.get_id())
        if is_bv(t) and t.num_args() == 0 and t.decl().kind() == Z3_OP_UNINTERPRETED:
            leaves[t.get_id()] = t
        work.extend(t.children())
    samples = []
    for seed in range(seeds):
        rng = Random(seed)
        samples.append([(c, BitVecVal(rng.choice((rng.getrandbits(7), rng.getrandbits(12) * 32, rng.getrandbits(20))),
                                      c.size())) for c in leaves.values()])
    values = {}
    for s in squares:
        vs = [simplify(substitute(hide(s.arg(0)), *sample)) for sample in samples]
        if all(is_bv_value(v) for v in vs):
            values[s.get_id()] = [v.as_long() for v in vs]
    axioms = []
    for a in squares:
        for b in squares:
            if a.eq(b) or a.size() != b.size() or a.get_id() not in values or b.get_id() not in values:
                continue
            mask = (1 << a.size()) - 1
            diffs = {(vb - va) & mask for va, vb in zip(values[a.get_id()], values[b.get_id()])}
            if len(diffs) != 1:
                continue
            d = BitVecVal(diffs.pop(), a.size())
            u, v = a.arg(0), b.arg(0)
            axioms.append(Implies(v == u + d, b == a + 2 * d * u + d * d))
    return axioms


def square_monotonicity(formula, functions):
    """Valid facts about the squares hidden by abstract_nonlinear_mul.

    For n-bit a <= b < 2^(n/2), a*a <= b*b without wrap-around, so each
    instance holds when the UF is read as bvmul: conjoining them keeps every
    original model. Memory-cost gas checks compare C(w) for different word
    counts and need exactly this ordering.
    """
    decls = {f.get_id() for f in functions.values()}
    squares, seen, work = {}, set(), [formula]
    while work:
        t = work.pop()
        if t.get_id() in seen or not is_app(t):
            continue
        seen.add(t.get_id())
        if t.decl().get_id() in decls and t.num_args() == 2 and t.arg(0).eq(t.arg(1)) and t.size() % 2 == 0:
            squares[t.get_id()] = t
        work.extend(t.children())
    return [Implies(And(ULE(a.arg(0), b.arg(0)), ULT(b.arg(0), 1 << (b.size() // 2))), ULE(a, b))
            for a in squares.values() for b in squares.values() if a.size() == b.size() and not a.eq(b)]


def _summands(t):
    return t.children() if t.decl().kind() == Z3_OP_BADD else [t]


def _top_bit_zero(x):
    return simplify(Extract(x.size() - 1, x.size() - 1, x)).eq(BitVecVal(0, 1))


def _carry_flag(e):
    """e = top bit of zext(a) + zext(b) / zext(a) - zext(b) -> ULT(a + b, a) / ULT(a, b); else None."""
    if not (is_app(e) and e.decl().kind() == Z3_OP_EXTRACT and e.arg(0).decl().kind() == Z3_OP_BADD):
        return None
    s = e.arg(0)
    n = s.size()
    if e.params() != [n - 1, n - 1] or n < 2 or s.num_args() != 2:
        return None
    pos, neg = [], []
    for x in s.children():
        if (x.decl().kind() == Z3_OP_BMUL and x.num_args() == 2 and is_bv_value(x.arg(0))
                and x.arg(0).as_long() == (1 << n) - 1 and _top_bit_zero(x.arg(1))):
            neg.append(Extract(n - 2, 0, x.arg(1)))
        elif _top_bit_zero(x):
            pos.append(Extract(n - 2, 0, x))
    if len(pos) + len(neg) != 2 or len(neg) > 1:
        return None
    return ULT(pos[0], neg[0]) if neg else ULT(pos[0] + pos[1], pos[0])


def _offset_view_select(t):
    """Select(A, b + c) -> Select(A', c) for a Store chain A over the view Lambda(a, M[a - b]).

    x86 reads EVM memory at absolute R15 + offset, EVM at the offset itself;
    A' is A with every address unshifted (unshift_store_chain, fail-closed).
    """
    root = t.arg(0)
    while is_store(root):
        root = root.arg(0)
    if not (is_quantifier(root) and root.is_lambda() and root.num_vars() == 1 and is_select(root.body())):
        return None
    base = simplify(-substitute_vars(root.body().arg(1), BitVecVal(0, root.var_sort(0).size())))
    offset = _subtract_base_term(t.arg(1), base)
    view = unshift_store_chain(t.arg(0), base, root.body().arg(0)) if offset is not None else None
    return None if view is None else Select(view, offset)


def _word_rewrite(t):
    """Candidate normal form of one term; `normalize_word_arith` proves it.

    - Extract(n-1, k, c + 2^k·m·x + r) -> Extract(n-1, k, (c mod 2^k) + r) + (c >> k) + m·x[n-k-1:0]
      (shifting out the low k bits commutes with adding multiples of 2^k), so
      the word counts (s + 31) >> 5 of the same base agree up to a constant.
    - Top bit of zext(a) + zext(b) / zext(a) - zext(b): the carry / borrow,
      i.e. ULT(a + b, a) / ULT(a, b) (rewritten at its == 0/1 test, adding no ite).
    - Concat(Extract(n-1, j, s), b) -> s when b is s's low part.
    - x86 absolute-address memory reads -> EVM offset view (_offset_view_select).
    """
    kind = t.decl().kind()
    if kind == Z3_OP_SELECT:
        return _offset_view_select(t)
    if kind == Z3_OP_BMUL and t.num_args() == 2:
        # 2^k * Concat(0^k, x) -> Concat(x, 0^k): x86 rounds sizes as 32*words,
        # EVM as words << 5; the same word count then feeds both squares.
        for c, x in ((t.arg(0), t.arg(1)), (t.arg(1), t.arg(0))):
            if is_bv_value(c) and is_app(x) and x.decl().kind() == Z3_OP_CONCAT:
                k = c.as_long().bit_length() - 1
                zeros = x.arg(0)
                if (0 < k < t.size() and c.as_long() == 1 << k and is_bv_value(zeros)
                        and zeros.as_long() == 0 and zeros.size() == k):
                    rest = x.children()[1:]
                    body = rest[0] if len(rest) == 1 else Concat(*rest)
                    return Concat(body, BitVecVal(0, k))
            # 2^k * x[hi:lo] -> Concat(x[lo+n-k-1:lo], 0^k): simplify pushes a low Extract into
            # a product on the x86 side ((32*w)[6:0] -> 32*w[6:0]) but into a Concat on the EVM
            # side ((w<<5)[6:0] -> Concat(w[1:0], 0^5)) (Safe 8915 H2 gas_0).
            if (is_bv_value(c) and c.as_long() > 1 and c.as_long() & (c.as_long() - 1) == 0
                    and is_app(x) and x.decl().kind() == Z3_OP_EXTRACT):
                k = c.as_long().bit_length() - 1
                if k < t.size():
                    return Concat(Extract(t.size() - k - 1, 0, x), BitVecVal(0, k))
        return None
    if kind == Z3_OP_EQ and is_bv(t.arg(0)) and t.arg(0).size() == 1:
        for e, v in ((t.arg(0), t.arg(1)), (t.arg(1), t.arg(0))):
            flag = _carry_flag(e) if is_bv_value(v) else None
            if flag is not None:
                return flag if v.as_long() == 1 else Not(flag)
        return None
    if kind == Z3_OP_CONCAT:
        args = t.children()
        for i, e in enumerate(args[:-1]):
            if is_app(e) and e.decl().kind() == Z3_OP_EXTRACT:
                s, (hi, lo) = e.arg(0), e.params()
                if hi == s.size() - 1 and lo == args[i + 1].size():
                    parts = [*args[:i], s, *args[i + 2:]]
                    return parts[0] if len(parts) == 1 else Concat(*parts)
        return None
    if kind != Z3_OP_EXTRACT or t.arg(0).decl().kind() != Z3_OP_BADD:
        return None
    s = t.arg(0)
    n, (hi, k) = s.size(), t.params()
    if hi != n - 1 or k == 0:
        return None
    if k == n - 1:
        return None  # carry bits are rewritten at their comparison (_carry_flag): no new ite guards
    c, rest, shifted = 0, [], []
    for x in _summands(s):
        if is_bv_value(x):
            c += x.as_long()
        elif (x.decl().kind() == Z3_OP_BMUL and x.num_args() == 2 and is_bv_value(x.arg(0))
              and x.arg(0).as_long() % (1 << k) == 0):
            shifted.append((x.arg(0).as_long() >> k) * Extract(n - k - 1, 0, x.arg(1)))
        else:
            rest.append(x)
    c %= 1 << n
    if c < (1 << k) and not shifted:
        return None
    low = BitVecVal(c % (1 << k), n)
    for x in rest:
        low = low + x
    out = Extract(n - 1, k, low) + (c >> k)
    for x in shifted:
        out = out + x
    return out


def _concat_matches(old, new):
    """Concat(p_1..p_k) == new, decided slice by slice by the simplifier.

    Each p_i must simplify to the same AST as new's matching Extract; the
    simplifier preserves equivalence, so this is a proof. Catches recombined
    byte stores ((a*b)[7:0] became a[7:0]*b[7:0]) that product abstraction loses.
    """
    if not (is_app(old) and old.decl().kind() == Z3_OP_CONCAT and is_bv(new) and new.size() == old.size()):
        return False
    hi = new.size()
    for part in old.children():
        lo = hi - part.size()
        if not simplify(Extract(hi - 1, lo, new), bv_sort_ac=True).eq(simplify(part, bv_sort_ac=True)):
            return False
        hi = lo
    return True


def _offset_view_identity(old, new, timeout_ms):
    """old == new for an offset-view rewrite (_offset_view_select), by generalisation.

    The direct query drowns in the concrete offset terms (CErc20 12930: >10s
    per read). Instead: (1) every address really is base + offset; (2) with
    offsets, values and the read offset generalised to fresh constants the
    shifted chain reads what the unshifted one does (for ALL values, so for
    these); (3) new is that instance up to the simplifier.
    """
    root, stores = old.arg(0), []
    while is_store(root):
        stores.append((root.arg(1), root.arg(2)))
        root = root.arg(0)
    if not (is_quantifier(root) and root.is_lambda() and root.num_vars() == 1 and is_select(root.body())):
        return False
    base = simplify(-substitute_vars(root.body().arg(1), BitVecVal(0, root.var_sort(0).size())))
    offsets = [_subtract_base_term(address, base) for address, _ in stores]
    read = _subtract_base_term(old.arg(1), base)
    if read is None or any(o is None for o in offsets):
        return False
    shifted = Or(old.arg(1) != base + read, *(a != base + o for (a, _), o in zip(stores, offsets)))
    if solve_query(shifted, timeout_ms) != "unsat":
        return False
    generic_old, generic_new, instance = root, root.body().arg(0), root.body().arg(0)
    for (_, value), offset in reversed(list(zip(stores, offsets))):
        x, y = FreshConst(offset.sort(), "ov_x"), FreshConst(value.sort(), "ov_y")
        generic_old, generic_new = Store(generic_old, base + x, y), Store(generic_new, x, y)
        instance = Store(instance, offset, value)
    z = FreshConst(read.sort(), "ov_z")
    if not simplify(Select(instance, read), bv_sort_ac=True).eq(simplify(new, bv_sort_ac=True)):
        return False
    return solve_query(Select(generic_old, base + z) != Select(generic_new, z), timeout_ms) == "unsat"


_OFFSET_VIEW_STEP = {}  # (index sort, value sort) -> refuted step lemma (Obligation), per process


def _offset_view_step_lemma(index_sort, value_sort, timeout_ms=10_000):
    """Refuted  Store(λa.Y[a-b], b+o, v)[i] != Store(Y, o, v)[i-b]  (Y, b, o, v, i fresh), or None.

    One store on a shifted view is the shifted view of the store; all
    constants are free, so the refutation covers every instance. Proved once
    per sort pair; only a successful proof is cached.
    """
    key = (index_sort.sexpr(), value_sort.sexpr())
    if key not in _OFFSET_VIEW_STEP:
        y = Const("ov_step_Y", ArraySort(index_sort, value_sort))
        a, b, o, i = (Const(f"ov_step_{n}", index_sort) for n in "aboi")
        v = Const("ov_step_v", value_sort)
        goal = Select(Store(Lambda([a], Select(y, a - b)), b + o, v), i) != Select(Store(y, o, v), i - b)
        started = monotonic()
        answer = solve_query(goal, timeout_ms)
        if answer != "unsat":
            return None
        _OFFSET_VIEW_STEP[key] = Obligation("offset_view_step_lemma", goal.sexpr(), answer,
                                            elapsed_seconds=monotonic() - started)
    return _OFFSET_VIEW_STEP[key]


def _unshifted_chain(array, root, base):
    """D with array[i] == D[i - base] for all i, by the step lemma; None unless every store is syntactic.

    array is a Store chain over root = λa. M[a - base]. Each store address
    must simplify to base + offset (_subtract_base_term, re-checked by
    simplify) so the step lemma instantiates with o = offset. Memoized per
    store node: selects on one chain share its prefix.
    """
    pending, node = [], array
    while not node.eq(root):
        if not (is_store(node) and node.num_args() == 3):
            return None
        pending.append(node)
        node = node.arg(0)
    below = root.body().arg(0)
    for node in reversed(pending):  # the result for a node is fixed by (node, root, base)
        below = _memoized("ov_unshift", (node, root, base), lambda node=node, below=below: _unshift_step(node, below, base))
        if below is None:
            return None
    return below


def _unshift_step(node, below, base):
    offset = _subtract_base_term(node.arg(1), base)
    if offset is None or not is_true(simplify(node.arg(1) == base + offset)):
        return None
    return Store(below, offset, node.arg(2))


def _offset_view_by_step_lemma(old, new):
    """(step lemma,) when old == new follows from the step lemma; None -> caller falls back.

    old = C_n[base + r], C_0 = λa. M[a - base], C_{k+1} = Store(C_k, base + o_k, v_k).
    Induction on k with the step lemma: C_k[i] == D_k[i - base] for
    D_0 = M, D_{k+1} = Store(D_k, o_k, v_k); so old == D_n[r], and new must
    simplify to that very term. Any non-syntactic step returns None.
    """
    root = old.arg(0)
    while is_store(root):
        root = root.arg(0)
    if not (is_quantifier(root) and root.is_lambda() and root.num_vars() == 1 and is_select(root.body())
            and _no_binder(root.body().arg(0))):
        return None
    index_sort = root.var_sort(0)
    if index_sort.kind() != Z3_BV_SORT:
        return None
    base = simplify(-substitute_vars(root.body().arg(1), BitVecVal(0, index_sort.size())))
    probe = FreshConst(index_sort, "ov_probe")  # root is λa. M[a - base] for every a
    if not is_true(simplify(substitute_vars(root.body().arg(1), base + probe) == probe)):
        return None
    read = _subtract_base_term(old.arg(1), base)
    if read is None or not is_true(simplify(old.arg(1) == base + read)):
        return None
    shifted = _unshifted_chain(old.arg(0), root, base)
    if shifted is None or not simplify(Select(shifted, read), bv_sort_ac=True).eq(simplify(new, bv_sort_ac=True)):
        return None
    lemma = _offset_view_step_lemma(index_sort, old.sort())
    return None if lemma is None else (lemma,)


def _identity_proof(old, new, timeout_ms=1000):
    """Lemmas proving old == new for every value of the UF applications / products inside
    (() when a direct query or the simplifier proves it); None when unproved.

    Proofs are memoized per (old, new): whether old == new is valid depends on the two
    terms only, never on the obligation they occur in, so a proof found once proves the
    identity everywhere. Failures are not cached (a 1s timeout under load can succeed on
    a retry; caching it lost one rewrite on Permit2 1327 x86_maps_0_20). Sibling
    obligations of a node share premise and path terms, so normalize_word_arith meets the
    same rewrites again: Permit2 1327 x86_maps_0_10 / 0_20 repeat 191-192 of their 199
    identity proofs (~23 of 24s), and one obligation repeats 81 of them across rounds.
    """
    if not (is_expr(old) and is_expr(new)):  # e.g. a rewrite that produced nothing: not memoized
        return _identity_proof_uncached(old, new, timeout_ms)
    return _memoized("identity_proof", (old, new), lambda: _identity_proof_uncached(old, new, timeout_ms),
                     keep=lambda proof: proof is not None)


def _identity_proof_uncached(old, new, timeout_ms):
    if _concat_matches(old, new):
        return ()
    if is_select(old) and is_select(new):
        lemmas = _offset_view_by_step_lemma(old, new)
        if lemmas is not None:
            return lemmas
        if _offset_view_identity(old, new, timeout_ms):
            return ()
    goal = Not(old == new)
    opaque = _uf_app_constants(goal)
    if opaque:
        goal = substitute(goal, *opaque)
    products = _nonlinear_mul_terms(goal)
    if products:
        goal = substitute(goal, *[(p, FreshConst(p.sort(), "mul")) for p in products])
    return () if solve_query(goal, timeout_ms) == "unsat" else None


def _identity_holds(old, new, timeout_ms=1000):
    """old == new for every value of the UF applications / products inside."""
    return _identity_proof(old, new, timeout_ms) is not None


def _high_zero_words(e):
    """e is OR_t Extract(n-1, k, s_t) == 0 (one k > 0 for all t) -> ([s_t], k), else None."""
    if not (is_eq(e) and is_bv(e.arg(0))):
        return None
    for x, z in ((e.arg(0), e.arg(1)), (e.arg(1), e.arg(0))):
        if not (is_bv_value(z) and z.as_long() == 0):
            continue
        words, ks = [], set()
        for o in (x.children() if is_app(x) and x.decl().kind() == Z3_OP_BOR else [x]):
            if not (is_app(o) and o.decl().kind() == Z3_OP_EXTRACT):
                return None
            top, k = o.params()
            if top != o.arg(0).size() - 1 or k == 0:
                return None
            words.append(o.arg(0))
            ks.add(k)
        if len(ks) == 1:
            return words, ks.pop()
    return None


def _bvor_all(xs):
    result = xs[0]
    for x in xs[1:]:
        result = result | x
    return result


def _settled_word(word):
    """No byte-split Concat left for _word_rewrite: a joined test is then simplified in the
    same form as the EVM side's word test."""
    seen, work = set(), [word]
    while work:
        t = work.pop()
        if t.get_id() in seen or not is_app(t):
            continue
        seen.add(t.get_id())
        if t.decl().kind() == Z3_OP_CONCAT and _word_rewrite(t) is not None:
            return False
        work.extend(t.children())
    return True


def _or_zero_instance(high, words, k):
    """Proof that high ∧ OR_t s_t[k-1:0] == 0 ⇔ ∧_t s_t == 0 for this instance, checked by the
    solver on its generalisation (each word s_t replaced by a fresh x_t): valid for all x_t, it
    is valid for x_t := s_t, and substituting back gives exactly this instance."""
    xs = [FreshConst(w.sort(), "zj") for w in words]
    pairs = list(zip(words, xs))
    low = _bvor_all([Extract(k - 1, 0, s) for s in words]) == 0
    goal = Not(substitute(And(high, low), *pairs) == substitute(And(*[s == 0 for s in words]), *pairs))
    started = monotonic()
    answer = solve_query(goal, 10_000)
    return Obligation("or_zero_join", goal.sexpr(), answer, elapsed_seconds=monotonic() - started)


def _zero_test_joins(kids):
    """[(i, j, s == 0)] for kids[i] = (s[n-1:k] == 0) and kids[j] simplifying to s[k-1:0] == 0:
    one word test s == 0 that the simplifier distributed over a Concat. x86 tests a
    difference byte-split (len = z - fmp), EVM tests z == fmp as a word, so the EVM ite
    guard on it stays undecided by the x86 path condition (CErc20 10233, Safe 4626)."""
    simplified = {}
    for j, c in enumerate(kids):
        if is_eq(c):
            simplified.setdefault(simplify(c).get_id(), j)
    out, used = [], set()
    for i, hi in enumerate(kids):
        found = _high_zero_words(hi) if i not in used else None
        if found is None:
            continue
        words, k = found
        if len(words) > 1 and not all(_settled_word(s) for s in words):
            continue  # join once the Concat rule has merged the byte splits (a later round)
        j = simplified.get(simplify(_bvor_all([Extract(k - 1, 0, s) for s in words]) == 0).get_id())
        if j is not None and j != i and j not in used:
            # One word: proved per instance (_identity_proof). Several (Safe 2011): proved per
            # instance on its generalisation; kids[j] simplifies to that instance's low test.
            lemma = _or_zero_instance(hi, words, k) if len(words) > 1 else None
            out.append((i, j, simplify(And(*[s == 0 for s in words]), bv_sort_ac=True), lemma))
            used |= {i, j}
    return out


def _join_and_decide(formula, lemmas):
    """(F', changed) with F' ≡ F:
    - And(.., s[n-1:k] == 0, s[k-1:0] == 0, ..) -> And(.., s == 0, ..) (proved, lemma added);
      at the top level s == 0 is conjoined instead (F implies it);
    - F = L ∧ G ≡ L ∧ G[a := v] for a top-level literal L (atom a, polarity v) that is
      an ite guard elsewhere: every model of F gives a the value v."""
    top = _conjuncts(formula)
    joins, added = [], []
    for i, j, eq, lemma in _zero_test_joins(top):
        joins.append((And(top[i], top[j]), eq, lemma))
        added.append(eq)
    pairs, seen, work = [], set(), list(top)
    while work:
        t = work.pop()
        if t.get_id() in seen or not is_app(t):
            continue
        seen.add(t.get_id())
        work.extend(t.children())
        if is_and(t):
            kids = t.children()
            found = _zero_test_joins(kids)
            if found:
                gone = {n for i, j, _, _ in found for n in (i, j)}
                joins += [(And(kids[i], kids[j]), eq, lemma) for i, j, eq, lemma in found]
                pairs.append((t, And(*[eq for _, _, eq, _ in found], *[c for n, c in enumerate(kids) if n not in gone])))
    for old, new, lemma in joins:
        started = monotonic()
        proof = _identity_proof(old, new) if lemma is None else ((lemma,) if lemma.proved else None)
        if proof is None:  # never expected (a bit-vector identity); fail closed
            return formula, False
        lemmas.append(Obligation(f"normalize_{len(lemmas)}", Not(old == new).sexpr(), "unsat",
                                 elapsed_seconds=monotonic() - started, lemmas=proof))
    if joins:
        top = _conjuncts(simplify(And(substitute(And(*top), *pairs) if pairs else And(*top), *added),
                                  bv_sort_ac=True))
    literals = {}
    for p in top:
        atom, value = (p.arg(0), False) if is_not(p) else (p, True)
        literals.setdefault(atom.get_id(), (atom, BoolVal(value)))
    guards = [literals[c.get_id()] for c in _ite_conditions(And(*top)) if c.get_id() in literals]
    if guards:
        keep = {a.get_id() for a, _ in guards}
        top = [p if (p.arg(0) if is_not(p) else p).get_id() in keep else substitute(p, *guards) for p in top]
    if not joins and not guards:
        return formula, False
    return simplify(And(*top), bv_sort_ac=True), True


def _normalized_lambda(t, lemmas, deadline):
    """λk. b' for t = λi. b, b' = normalize_word_arith of b[i := k] (k fresh), or None.

    The rewrites of b[i := k] are proved for every value of k (a free constant
    there), so b[i := k] = b' is valid and λi. b = λk. b' by extensionality. The
    body sits under an uninterpreted Bool `hold` so that normalising it rewrites
    terms only (hold(b) is no ite guard and nothing else decides it)."""
    k = FreshConst(t.var_sort(0), "lam_k")
    body = substitute_vars(t.body(), k)
    hold = FreshFunction(body.sort(), BoolSort())
    started = monotonic()
    out, inner = normalize_word_arith(hold(body), deadline=deadline)
    if not (is_app(out) and out.decl().eq(hold)) or out.arg(0).eq(body):
        return None
    new = Lambda([k], out.arg(0))
    lemmas.append(Obligation(f"normalize_{len(lemmas)}_lambda", Not(t == new).sexpr(), "unsat",
                             elapsed_seconds=monotonic() - started, lemmas=inner))
    return new


def _normalize_lambdas(formula, lemmas, deadline=None):
    """F with every outermost one-variable lambda replaced by _normalized_lambda
    (inner ones are normalised with their body), binders renamed canonically, F' ≡ F.

    The rounds below never enter binders, but x86 memory reaches its hashes
    inside lambdas: sha3_slice(λi. If(len <= i, 0, A[R15 + o + i])) reads the
    R15 offset view where EVM reads M[o + i], so the two sides' hash arguments
    never met (Permit2 1327 x86_maps_0_46: three nested sha3_slice levels per
    side; every route unknown for 1800s, here the blasted normal form is
    refuted in 0.4s). canon_binders: the rebuilt lambdas of both sides are
    then alpha-equal terms, so equal ones hash-cons."""
    pairs, seen, work = [], set(), [formula]
    while work:
        t = work.pop()
        if t.get_id() in seen:
            continue
        seen.add(t.get_id())
        if is_quantifier(t):
            if t.is_lambda() and t.num_vars() == 1 and (deadline is None or monotonic() < deadline):
                new = _normalized_lambda(t, lemmas, deadline)
                if new is not None:
                    pairs.append((t, new))
            continue
        if is_app(t):
            work.extend(t.children())
    if not pairs:
        return formula
    return simplify(canon_binders(substitute(formula, *pairs)), bv_sort_ac=True)


def normalize_word_arith(formula, rounds=32, deadline=None):
    """Rewrite F into an equivalent F' whose word counts / gas sums are syntactic.

    Both sides compute memory words as (s + 31) >> 5 of differently built
    offsets and compare gas with different idioms (EVM ULE vs x86 65-bit
    borrow); bit-blasting cannot see the equalities. Each rewrite is a
    candidate from `_word_rewrite`, kept only if old == new is proved with
    its UF applications and products generalised, so F' ≡ F; the proofs are
    returned as lemmas. bv_sort_ac orders sums so equal sums hash-cons.
    A replacement is built from the old children, so each nesting level of
    rewrites costs a round: run to a fixpoint (rounds is only a cap; Safe 8915
    H2 gas_0 needs 10, the old cap 6 left x86 byte splits and R15 views).
    Lambda bodies are normalised first, each on its own (_normalize_lambdas).
    """
    formula, lemmas = simplify(formula, bv_sort_ac=True), []
    formula = _normalize_lambdas(formula, lemmas, deadline)
    # A rewrite whose identity failed is not retried in later rounds of this call (the same
    # query again); other calls retry it. Proved identities are memoized (_identity_proof).
    unproved = {}
    for _ in range(rounds):
        # Joined zero tests and decided guards expose word arithmetic for this round.
        formula, _ = _join_and_decide(formula, lemmas)
        pairs, seen, work = [], set(), [formula]
        while work:
            t = work.pop()
            if t.get_id() in seen or not is_app(t):
                continue
            seen.add(t.get_id())
            work.extend(t.children())
            new = _word_rewrite(t)
            if new is None or (deadline is not None and monotonic() > deadline):
                continue
            new = simplify(new, bv_sort_ac=True)
            started = monotonic()
            key = (t.get_id(), new.get_id())
            proof = None if new.eq(t) or key in unproved else _identity_proof(t, new)
            if proof is None:
                unproved[key] = (t, new)  # kept alive: their ids are not recycled during the call
            if proof is not None:
                # proof: the refuted lemmas this rewrite rests on (offset-view step lemma), else ().
                pairs.append((t, new))
                lemmas.append(Obligation(f"normalize_{len(lemmas)}", Not(t == new).sexpr(), "unsat",
                                         elapsed_seconds=monotonic() - started, lemmas=proof))
        if not pairs:
            break
        before, formula = formula, simplify(substitute(formula, *pairs), bv_sort_ac=True)
        if formula.eq(before):
            break  # rewrites that change nothing after simplification: fixpoint
    return formula, tuple(lemmas)


# --- memory-cost potential: telescoping memory-expansion charges -------------
#
# Each expansion charges If(new <= msize, 0, C(new) - C(msize)), C(w) = 3w + w*w/512.
# EVM and x86 expand in different steps (MCOPY: EVM once to max(src, dst) + len,
# x86 to src + len, the destination by the next store; LOG / MSTORE runs), so only
# the totals C(final) - C(msize0) agree, and the bit-blaster cannot see that through
# the squares (Safe 9733 / 11803 x86_maps, CErc20 4571 / 12342 OOG pairs: every
# other route unknown). With C an uninterpreted P the sums cancel syntactically.

_POTENTIAL = {}  # bit width -> fresh UF standing for C


def _potential(n):
    if n not in _POTENTIAL:
        _POTENTIAL[n] = FreshFunction(BitVecSort(n), BitVecSort(n))
    return _POTENTIAL[n]


def _memory_cost(w):
    return 3 * w + Concat(BitVecVal(0, 9), Extract(w.size() - 1, 9, w * w))


def _quadratic_cost_word(t):
    """w when t = Concat(0^9, Extract(n-1, 9, w*w)), the square part of C(w); else None."""
    if not (is_app(t) and t.decl().kind() == Z3_OP_CONCAT and t.num_args() == 2):
        return None
    zero, e = t.children()
    if not (is_bv_value(zero) and zero.as_long() == 0 and zero.size() == 9 and is_app(e)
            and e.decl().kind() == Z3_OP_EXTRACT and e.params() == [e.arg(0).size() - 1, 9]):
        return None
    s = e.arg(0)
    return s.arg(0) if s.decl().kind() == Z3_OP_BMUL and s.num_args() == 2 and s.arg(0).eq(s.arg(1)) else None


def abstract_memory_potential(formula):
    """(F', changed): every square part E(w) of a memory cost replaced by P(w) - 3w, P fresh.

    Every model of F extends (read P as λw. 3w + E(w)), so only UNSAT
    transfers back; C(w) = 3w + E(w) becomes the single atom P(w).
    """
    pairs, seen, work = {}, set(), [formula]
    while work:
        t = work.pop()
        if t.get_id() in seen or not is_app(t):
            continue
        seen.add(t.get_id())
        w = _quadratic_cost_word(t)
        if w is not None:
            pairs[t.get_id()] = (t, _potential(w.size())(w) - 3 * w)
            continue
        work.extend(t.children())
    if not pairs:
        return formula, False
    return simplify(substitute(formula, *pairs.values()), bv_sort_ac=True), True


def _negated(x):
    """k*y for x = -(k*y) written as (2^n - k)*y; else None."""
    if (x.decl().kind() == Z3_OP_BMUL and x.num_args() == 2 and is_bv_value(x.arg(0))
            and x.arg(0).as_long() >> (x.size() - 1)):
        k = (1 << x.size()) - x.arg(0).as_long()
        return x.arg(1) if k == 1 else k * x.arg(1)
    return None


def _telescope_step(t):
    """If(c, 0, P - B) -> If(c, B, P) - B (either branch order); else None.

    An identity for all c, P, B. Read on a charge If(new <= m, 0, C(new) - C(m)),
    If(c, C(m), C(new)) is C of the next msize, the very term the next charge
    subtracts, so consecutive charges cancel under simplification.
    """
    if not (is_app(t) and t.decl().kind() == Z3_OP_ITE and is_bv(t)):
        return None
    c, x, y = t.children()
    for zero, d, first in ((x, y, True), (y, x, False)):
        if is_bv_value(zero) and zero.as_long() == 0 and not is_bv_value(d):
            summands = d.children() if d.decl().kind() == Z3_OP_BADD else [d]
            neg = [n for n in map(_negated, summands) if n is not None]
            pos = [s for s in summands if _negated(s) is None]
            if not neg or not pos:
                return None
            b, p = sum(neg[1:], neg[0]), sum(pos[1:], pos[0])
            return (If(c, b, p) if first else If(c, p, b)) - b
    return None


def _cost_inverse(k):
    """w0 < 2^32 with C(w0) == k (k a literal; C strictly increases there), else None."""
    n, lo, hi = k.size(), 0, (1 << 32) - 1
    while lo <= hi:
        w = (lo + hi) // 2
        c = (3 * w + ((w * w) % (1 << n) >> 9)) % (1 << n)
        if c == k.as_long():
            w0 = BitVecVal(w, n)
            return w0 if is_true(simplify(_memory_cost(w0) == k)) else None
        lo, hi = (w + 1, hi) if c < k.as_long() else (lo, w - 1)
    return None


def _lift_potential(t, axioms):
    """If(c, P(a), P(b)) -> P(If(c, a, b)) (congruence); a literal branch k = C(w0) is
    read as P(w0), and the axiom P(w0) == k (true of the reading) goes to `axioms`."""
    if not (is_app(t) and t.decl().kind() == Z3_OP_ITE and is_bv(t)):
        return None
    decls = {f.get_id(): f for f in _POTENTIAL.values()}
    c, x, y = t.children()
    f = next((decls[v.decl().get_id()] for v in (x, y) if is_app(v) and v.decl().get_id() in decls), None)
    if f is None:
        return None
    args = []
    for v in (x, y):
        if is_app(v) and v.decl().eq(f):
            args.append(v.arg(0))
            continue
        w0 = _cost_inverse(v) if is_bv_value(v) and v.size() == f.range().size() else None
        if w0 is None:
            return None
        axioms[w0.as_long()] = f(w0) == v
        args.append(w0)
    return f(If(c, *args))


def telescope_potential(formula, rounds=32):
    """(F', lemmas, axioms, steps) over abstract_memory_potential's P.

    _telescope_step rewrites are each proved old == new (_identity_proof,
    UF applications opaque); _lift_potential rewrites are congruence instances
    (valid for every P) or rest on `axioms`, each valid for P read as C. So
    F' ∧ axioms ≡ F ∧ axioms, and UNSAT of it transfers to F (with the reading).
    A rewrite is built from the old children, so each ite nesting level costs a
    round: run to a fixpoint (rounds is only a cap). Safe 5377 H2 memory_gas_0
    (EVM: ite of 12 expansions with C at the leaves; x86: C of the ite of word
    counts) needs 12; the old cap 4 left P(..) beside literals, abstract SAT.
    """
    formula, lemmas, axioms, steps = simplify(formula, bv_sort_ac=True), [], {}, 0
    for rule in ("step", "lift"):
        for _ in range(rounds):
            pairs, seen, work = [], set(), [formula]
            while work:
                t = work.pop()
                if t.get_id() in seen or not is_app(t):
                    continue
                seen.add(t.get_id())
                work.extend(t.children())
                new = _telescope_step(t) if rule == "step" else _lift_potential(t, axioms)
                if new is None:
                    continue
                if rule == "step":
                    started = monotonic()
                    proof = _identity_proof(t, new)
                    if proof is None:
                        continue
                    lemmas.append(Obligation(f"telescope_{len(lemmas)}", Not(t == new).sexpr(), "unsat",
                                             elapsed_seconds=monotonic() - started, lemmas=proof))
                    steps += 1
                pairs.append((t, new))
            if not pairs:
                break
            formula = simplify(substitute(formula, *pairs), bv_sort_ac=True)
    return formula, tuple(lemmas), tuple(axioms[k] for k in sorted(axioms)), steps


_POTENTIAL_WORDS = (1 << 32) - 1  # C(w) for w <= this fits 64 bits without wrap-around
_POTENTIAL_MONOTONE_APPS = 32  # ponytail: pairwise monotonicity only up to this many P(w) (O(k^2) axioms)


def potential_range_axioms(formula):
    """Valid facts about the memory potential P (abstract_memory_potential) read as C.

    For n >= 64 bits and w <= 2^32 - 1: w*w < 2^64 and 3w + (w*w >> 9) < 2^n,
    so C(w) = 3w + E(w) never wraps there and is non-decreasing. Hence, for every
    P(a), P(b) of F:  a <= W ⇒ P(a) <= C(W)  and  a <= b <= W ⇒ P(a) <= P(b)
    (W = 2^32 - 1). Each instance holds when P is read as C, so conjoining keeps
    every model of F. A charge C(new) - C(old) that the x86 side checks for 64-bit
    overflow (Permit2 1327 x86 paths 6/7: LOG2 cost 8*len + 1125 + expansion) is
    bounded only with these: P alone is any function, so the overflow is
    abstract-SAT, and the squares stall the exact solver.
    """
    decls = {f.get_id() for f in _POTENTIAL.values()}
    apps, seen, work = {}, set(), [formula]
    while work:
        t = work.pop()
        if t.get_id() in seen or not is_app(t):
            continue
        seen.add(t.get_id())
        if t.decl().get_id() in decls and t.size() >= 64:
            apps[t.get_id()] = t
        work.extend(t.children())
    apps = list(apps.values())
    axioms = []
    for a in apps:
        top = BitVecVal(_POTENTIAL_WORDS, a.size())
        axioms.append(Implies(ULE(a.arg(0), top), ULE(a, simplify(_memory_cost(top)))))
    if len(apps) <= _POTENTIAL_MONOTONE_APPS:
        axioms += [Implies(And(ULE(a.arg(0), b.arg(0)), ULE(b.arg(0), BitVecVal(_POTENTIAL_WORDS, b.size()))),
                           ULE(a, b))
                   for a in apps for b in apps if not a.eq(b) and a.size() == b.size()]
    return axioms


def refute_over_bounded_potential(formula, timeout_ms):
    """(query, answer, lemmas): F over the telescoped potential P with
    potential_range_axioms, refuted by refute_over_bv_abstraction.

    Every step only adds models (abstract_memory_potential, the bv abstraction)
    or is an equivalence under axioms true of P read as C (telescope_potential,
    whose identity proofs are `lemmas`; potential_range_axioms). So only "unsat"
    means anything, and then F is UNSAT. Not applicable (no memory-cost sum, or
    nothing to bound): (F, "unknown", ()) at once.
    """
    abstract, changed = abstract_memory_potential(formula)
    if not changed or timeout_ms <= 0:
        return formula, "unknown", ()
    target, lemmas, axioms, _ = telescope_potential(abstract)
    bounds = potential_range_axioms(target)
    if not bounds:
        return formula, "unknown", ()
    query, answer = refute_over_bv_abstraction(And(target, *axioms, *bounds), timeout_ms)
    return (query, "unsat", lemmas) if answer == "unsat" else (formula, "unknown", ())


def _random_leaf_values(terms, seeds):
    """Fingerprints of `terms` under `seeds` random small leaf assignments (UF
    applications and memory reads opaque); None where a value is not a literal."""
    opaque = _uf_app_constants(*terms)
    hidden = [substitute(t, *opaque) if opaque else t for t in terms]
    reads, leaves, seen, work = {}, {}, set(), list(hidden)
    while work:
        t = work.pop()
        if t.get_id() in seen or not is_app(t):
            continue
        seen.add(t.get_id())
        if is_select(t) and is_bv(t):
            reads[t.get_id()] = (t, FreshConst(t.sort(), "fp_read"))
            continue
        if is_bv(t) and t.num_args() == 0 and t.decl().kind() == Z3_OP_UNINTERPRETED:
            leaves[t.get_id()] = t
        work.extend(t.children())
    if reads:
        hidden = [substitute(h, *reads.values()) for h in hidden]
        leaves.update({c.get_id(): c for _, c in reads.values()})
    prints = [[] for _ in terms]
    for seed in range(seeds):
        rng = Random(seed)
        values = [(c, BitVecVal(rng.choice((rng.getrandbits(7), rng.getrandbits(12) * 32, rng.getrandbits(20))),
                                c.size())) for c in leaves.values()]
        for k, h in enumerate(hidden):
            v = simplify(substitute(h, *values))
            prints[k].append(v.as_long() if is_bv_value(v) else None)
    return [tuple(p) for p in prints]


def unify_potential_arguments(formula, timeout_ms, deadline=None, cache=None, seeds=3):
    """Merge P arguments (final msize word counts built differently per side)
    proved equal under F's binder-free conjuncts (_prove_equal). Candidates
    agree on some fingerprint sample; as unify_uf_arguments, every model of F is a model of
    the rewrite, so only UNSAT transfers back."""
    decls = {f.get_id() for f in _POTENTIAL.values()}
    args, seen, work = {}, set(), [formula]
    while work:
        t = work.pop()
        if t.get_id() in seen or not is_app(t):
            continue
        seen.add(t.get_id())
        # Literal arguments (the lift axioms' P(w0)) are no merge candidates: a full lift
        # adds ~20 of them, and their candidate proofs cost Safe 5377 H2 memory_0 +45s.
        if t.decl().get_id() in decls and not is_bv_value(t.arg(0)):
            args[t.arg(0).get_id()] = t.arg(0)
        work.extend(t.children())
    args = sorted(args.values(), key=_text_size)
    # Equal only under the premise (no wrap-around, msize >= 96) is common, and
    # random values violate it: any agreeing sample makes a candidate, most first.
    prints = _random_leaf_values(args, seeds)
    candidates = sorted(((sum(u == v is not None for u, v in zip(prints[i], prints[j])), i, j)
                         for i in range(len(args)) for j in range(i + 1, len(args))
                         if args[i].size() == args[j].size()), key=lambda c: (-c[0], c[1], c[2]))
    # ponytail: candidates agree on all but one sample, at most 2 per argument, 5s each;
    # widen if true merges get missed (CErc20 12342: any-sample agreement cost +45s, merged nothing more).
    candidates = [(i, j) for agree, i, j in candidates if agree >= max(1, seeds - 1)][:2 * len(args)]
    premise = And(*(c for c in _conjuncts(formula) if _no_binder(c)))
    pairs, lemmas, merged = [], [], set()
    for i, j in candidates:  # args[i] is the smaller (sorted by size)
        if i in merged or j in merged:
            continue
        budget = min(timeout_ms, 5_000)
        if deadline is not None:
            budget = min(budget, int((deadline - monotonic()) * 1000))
        if budget <= 0:
            break
        proofs = _prove_equal(premise, args[i], args[j], budget, deadline, cache)
        if proofs is not None:
            pairs.append((args[j], args[i]))
            merged.add(j)
            lemmas.extend(Obligation(f"potential_unify_{len(lemmas)}_case_{n}", q.sexpr(), "unsat",
                                     elapsed_seconds=s) for n, (q, s) in enumerate(proofs))
    if pairs:
        formula = simplify(substitute(formula, *pairs), bv_sort_ac=True)
    return formula, tuple(lemmas)


_ALIAS_MAX_CASES = 128
_ALIAS_SERIAL = count()


def _base_offset(a, b, pair=None):
    """(x, y, d) with a == b <=> x == y + d, when the linear forms of a and b
    differ in exactly one base term each (x, y ordered by id); None otherwise.
    With `pair` given, the bases must be that pair."""
    if not (is_bv(a) and is_bv(b) and a.size() == b.size()):
        return None
    found = _memoized("base_offset", (a, b), lambda: _base_offset_uncached(a, b))
    if found is None or (pair is not None and (found[0].get_id(), found[1].get_id())
                         != (pair[0].get_id(), pair[1].get_id())):
        return None
    return found


def _base_offset_uncached(a, b):
    la, lb = linearize_address(a), linearize_address(b)
    if la is None or lb is None:
        return None
    (ka, ca), (kb, cb) = la, lb
    ka, kb = Counter(dict(ka)), Counter(dict(kb))
    da, db = ka - kb, kb - ka
    if len(da) != 1 or len(db) != 1 or set(da.values()) != {1} or set(db.values()) != {1}:
        return None
    (ia,), (ib,) = da, db
    ta, tb = _base_term(a, ia), _base_term(b, ib)
    if ta is None or tb is None:
        return None
    mask = (1 << a.size()) - 1
    # a == b  <=>  ta + ca == tb + cb  <=>  ta == tb + (cb - ca)
    return (ta, tb, (cb - ca) & mask) if ta.get_id() < tb.get_id() else (tb, ta, (ca - cb) & mask)


def _base_term(address, term_id):
    work = [simplify(address)]
    while work:
        t = work.pop()
        if t.get_id() == term_id:
            return t
        if is_app(t) and t.decl().kind() == Z3_OP_BADD:
            work.extend(t.children())
    return None


def _store_chain_selects(formula):
    """Select(Store-chain, a) terms outside binders."""
    found, seen, work = [], set(), [formula]
    while work:
        t = work.pop()
        if t.get_id() in seen or not is_app(t):
            continue
        seen.add(t.get_id())
        if is_select(t) and is_store(t.arg(0)) and is_bv(t.arg(1)):
            found.append(t)
        work.extend(t.children())
    return found


def _substitutable(t):
    return t.num_args() == 0 and t.decl().kind() == Z3_OP_UNINTERPRETED


def _mentions(term, const):
    seen, work = set(), [term]
    while work:
        t = work.pop()
        if t.get_id() in seen:
            continue
        seen.add(t.get_id())
        if t.eq(const):
            return True
        if is_app(t):
            work.extend(t.children())
    return False


def _alias_offsets(formula, extras=None):
    """(x, y, D): the one pair of base terms whose Store/Select addresses may
    alias in F, and every offset d (x = y + d) at which some pair meets.
    None when there is no such question, or more than one base pair.

    With `extras` (a dict) given, a store address p that is no constant off
    a read at a free constant r (p free of r) is collected as (r, p) instead
    of giving up: `_alias_split` then splits on r == p as one more case."""
    pair, offsets = None, set()
    for select in _store_chain_selects(formula):
        node = select.arg(0)
        while is_store(node):
            found = _base_offset(node.arg(1), select.arg(1), pair)
            if found is None:
                lin_s, lin_r = linearize_address(node.arg(1)), linearize_address(select.arg(1))
                if lin_s is None or lin_r is None or lin_s[0] != lin_r[0]:
                    read = select.arg(1)
                    if extras is None or not _substitutable(read) or _mentions(node.arg(1), read):
                        return None  # an alias question outside the pair
                    extras[(read.get_id(), node.arg(1).get_id())] = (read, node.arg(1))
                    if len(extras) > _ALIAS_MAX_CASES:
                        return None
            else:
                pair = found[:2]
                offsets.add(found[2])
                if len(offsets) > _ALIAS_MAX_CASES:
                    return None
            node = node.arg(0)
    return None if pair is None else (*pair, sorted(offsets))


def _forward_apart(formula, x, y, offsets, extras=()):
    """Rewrite F assuming x != y + d for every d in `offsets` (and r != p for
    each (r, p) in `extras`): Selects skip the
    Stores that assumption separates them from, and x == y + d atoms become
    false. Returns (F', facts): every fact is an address equality the rewrite
    took to be false (a skipped Store's address == the read, or the atom).
    Once the assumption refutes each fact (`_alias_split` does), F' ≡ F under
    it by read-over-write and substitution of equals."""
    apart, cache, facts = set(offsets), {}, {}
    apart_terms = {(p.get_id(), r.get_id()) for r, p in extras}

    def separated(a, b):
        if (a.get_id(), b.get_id()) in apart_terms:
            return True
        lin_a, lin_b = linearize_address(a), linearize_address(b)
        if lin_a is not None and lin_b is not None and lin_a[0] == lin_b[0]:
            return lin_a[1] != lin_b[1]
        found = _base_offset(a, b, (x, y))
        return found is not None and found[2] in apart

    stack = [(formula, False)]
    while stack:
        t, built = stack.pop()
        if t.get_id() in cache:
            continue
        if not is_app(t) or t.num_args() == 0:
            cache[t.get_id()] = t
            continue
        if not built:
            stack.append((t, True))
            stack.extend((c, False) for c in t.children() if c.get_id() not in cache)
            continue
        kids = [cache[c.get_id()] for c in t.children()]
        out = t.decl()(*kids) if any(not k.eq(c) for k, c in zip(kids, t.children())) else t
        if is_select(out) and is_store(out.arg(0)) and is_bv(out.arg(1)):
            node, skipped = out.arg(0), []
            while is_store(node) and separated(node.arg(1), out.arg(1)):
                skipped.append(node.arg(1))
                node = node.arg(0)
            if skipped:
                for address in skipped:
                    fact = address == out.arg(1)
                    facts[fact.get_id()] = fact
                out = Select(node, out.arg(1))
        elif (out.decl().kind() == Z3_OP_EQ and is_bv(out.arg(0))
              and _base_offset(out.arg(0), out.arg(1), (x, y)) is not None
              and separated(out.arg(0), out.arg(1))):
            facts[out.get_id()] = out
            out = BoolVal(False)
        cache[t.get_id()] = out
    return cache[formula.get_id()], list(facts.values())


def _alias_split(formula, timeout_ms, deadline=None, fallback=None, parallel=False):
    """Refute F by cases on how two symbolic address bases x, y alias.

    Byte stores at x + j and reads at y + i leave every Select-over-Store
    guarded by "x == y + d?" — the solver drowns in that (CErc20 12930:
    abi_encode's mstore(pos, 32) then mload(value)). The cases are
    x == y + d for each offset d where a store meets a read, and the
    residual ∧_d x != y + d; together they cover everything. Case d refutes
    F[x := y + d] (a substitution instance, so F ∧ x = y + d is UNSAT too),
    where every alias question has a constant answer. The residual refutes
    F' ∧ R, F' the `_forward_apart` rewrite, after R ∧ (f_1 ∨ … ∨ f_n) is
    refuted for its facts, so F ∧ R ≡ F' ∧ R. That lemma is refuted over
    x := y + δ (δ fresh): a bijective reparametrisation, UNSAT for all
    (δ, y) is UNSAT for all (x, y), and it lets the simplifier cancel y
    (bit-blasting the 64-bit adders instead took ~4s per read on 12930).
    A query the solver leaves unknown goes to `fallback(query)` -> (refuted
    formula, lemmas) or None: with aliasing gone, the other routes can do
    the gas arithmetic (CErc20 12930 pair_22_0's residual: unification).
    A store no constant off the pair (Safe 4524: the x86 copy loop's one raw
    byte store at fmp + 63 + RETURNDATASIZE, left under the summary's Lambda
    when the first summary attempt was refused) read at a free constant r
    adds the case r == p (F[r := p], a substitution instance as above) and
    r != p to the residual.
    With `parallel` the hard queries run in the pair pool (see
    _refute_alias_queries); `fallback` must then be a prover's _refute_further.
    Returns the proofs as Obligations, or None if any query is not UNSAT
    (never a partial result).
    """
    extras = {}
    found = _alias_offsets(formula, extras)
    if found is None:
        return None
    x, y, offsets = found
    extras = list(extras.values())
    if _substitutable(x):
        shift = lambda q, d: substitute(q, (x, y + d))
    elif _substitutable(y):
        shift = lambda q, d: substitute(q, (y, x - d))
    else:
        return None
    if len(offsets) + len(extras) > _ALIAS_MAX_CASES:
        return None
    end = deadline if deadline is not None else monotonic() + (len(offsets) + len(extras) + 2) * timeout_ms / 1000
    residual = And(*(x != y + d for d in offsets), *(r != p for r, p in extras))
    queries = [("alias_cover", Not(Or(residual, *(x == y + d for d in offsets), *(r == p for r, p in extras))))]
    for d in offsets:
        signed = d - (1 << x.size()) if d >> (x.size() - 1) else d
        queries.append((f"alias_case_{signed}", simplify(shift(formula, d), bv_sort_ac=True)))
    # r == p: F[r := p] is a substitution instance (p is free of r), as for d.
    for k, (r, p) in enumerate(extras):
        queries.append((f"alias_term_{k}", simplify(substitute(formula, (r, p)), bv_sort_ac=True)))
    rewritten, facts = _forward_apart(formula, x, y, offsets, extras)
    delta = FreshConst(x.sort(), "alias_delta")
    if facts:
        queries.append(("alias_apart", simplify(shift(And(residual, Or(*facts)), delta), bv_sort_ac=True)))
    queries.append(("alias_residual", simplify(And(residual, rewritten), bv_sort_ac=True)))
    return _refute_alias_queries(queries, timeout_ms, end, fallback, parallel)


def _refute_alias_case(name, query, timeout_ms, end, fallback):
    """One `_alias_split` query: its Obligation if refuted directly or by
    `fallback(query)` -> (refuted formula, lemmas) | None; else None."""
    left = int((end - monotonic()) * 1000)
    started = monotonic()
    answer = solve_query(query, min(timeout_ms, left)) if left > 0 else "unknown"
    refuted, lemmas = query, ()
    if answer == "unknown" and fallback is not None and left > 0:
        found = fallback(query)
        if found is not None:
            answer, (refuted, lemmas) = "unsat", found
    if _TRACE_OBLIGATIONS:
        import os
        print(f"[alias {os.getpid()}] {name} {answer} {monotonic() - started:.1f}s", flush=True)
        if monotonic() - started > 10:  # diagnostic: keep hard cases for offline analysis
            with open(f"/tmp/alias_{os.getpid()}_{name}.smt2", "w") as handle:
                handle.write(_to_smt2(query))
    if answer != "unsat":
        return None
    return Obligation(name, refuted.sexpr(), "unsat", elapsed_seconds=monotonic() - started, lemmas=tuple(lemmas))


def _alias_case_serialized(smt2, name, timeout_ms, remaining_seconds, node):
    """Worker side of `_refute_alias_queries`: `_refute_alias_case` on the
    parsed query, falling back to a worker prover's `_refute_further`."""
    from z3 import parse_smt2_string
    prover = _worker_prover(node, timeout_ms, remaining_seconds)
    return _refute_alias_case(name, And(*parse_smt2_string(smt2)), timeout_ms, prover.deadline,
                              prover._refute_further)


def _refute_alias_queries(queries, timeout_ms, end, fallback, parallel):
    """Obligations for every (name, query) in order, or None unless all are UNSAT.

    Sequentially, the first failure stops. With `parallel` (fallback is then a
    prover's `_refute_further`) each query first gets a short local probe;
    two or more left over (the hard cases, CErc20 12930: ~170s each through
    unification) run `_refute_alias_case` in the pair pool on an SMT2 round
    trip, as `_check_all` does. The cases are independent and all must be refuted,
    so solving them concurrently proves exactly what the sequential loop does.
    """
    proofs, hard = [None] * len(queries), list(range(len(queries)))
    if parallel:
        hard = []
        for n, (name, query) in enumerate(queries):
            left = int((end - monotonic()) * 1000)
            started = monotonic()
            answer = solve_query(query, min(_QUICK_EXACT_MS, timeout_ms, left)) if left > 0 else "unknown"
            if answer == "sat" or left <= 0:
                return None
            if answer == "unsat":
                proofs[n] = Obligation(name, query.sexpr(), "unsat", elapsed_seconds=monotonic() - started)
            else:
                hard.append(n)
    # Only several hard cases pay for the pool (a nested one inside a pair worker).
    pool = _pair_pool() if parallel and len(hard) > 1 else None
    if pool is None:
        for n in hard:
            proofs[n] = _refute_alias_case(*queries[n], timeout_ms, end, fallback)
            if proofs[n] is None:
                return None
        return tuple(proofs)
    import os
    node = ("alias", os.getpid(), next(_ALIAS_SERIAL))  # fresh worker prover per split
    remaining = end - monotonic()
    futures = {n: pool.submit(_alias_case_serialized, _to_smt2(queries[n][1]), queries[n][0], timeout_ms,
                              remaining, node) for n in hard}
    try:
        for n, future in futures.items():
            try:
                proofs[n] = future.result(timeout=max(0.0, end + 30 - monotonic()))
            except (FutureTimeout, BrokenExecutor):
                return None
            if proofs[n] is None:
                return None
        return tuple(proofs)
    finally:
        if not all(f.done() for f in futures.values()):
            _reset_pair_pool()  # free workers still solving abandoned cases


# --- pinned memory words: one concrete case per value an ITE tests -----------
#
# A store at p + k read back at a constant c simplifies to If(p + k == c, v, old);
# with p an initial-memory word (fmp = mem0[0x40..0x5f], free_memory_pointer
# unspecialised) the condition is a conjunction of byte pins mem0[i] == b. Every
# later fmp read nests them (CErc20 12342 pair_29_1: 179 such conditions under
# 4116 of its 4121 ITEs, unknown on every route in 400s), yet each pinned value
# is a small concrete case and, with none of them, every ITE takes its else branch.
# ponytail: at most 256 cases, quick budget each, 2x the per-query budget in all.
_PIN_MAX_CASES = 256


def _pins(atom):
    """[(Select(A, i), b)] when `atom` is a conjunction of mem[i] == b (A an array
    constant, i and b literals), else None."""
    out = []
    for e in (atom.children() if is_and(atom) else [atom]):
        if not is_eq(e):
            return None
        a, b = e.children()
        if is_bv_value(a):
            a, b = b, a
        if not (is_bv_value(b) and is_select(a) and is_bv_value(a.arg(1)) and _substitutable(a.arg(0))):
            return None
        out.append((a, b))
    return out


def _pin_atoms(formula):
    """Distinct ITE conditions of F (outside binders) that pin memory bytes (_pins)."""
    atoms, seen, work = {}, set(), [formula]
    while work:
        t = work.pop()
        if t.get_id() in seen or not is_app(t):
            continue
        seen.add(t.get_id())
        if t.decl().kind() == Z3_OP_ITE and t.arg(0).get_id() not in atoms and _pins(t.arg(0)):
            atoms[t.arg(0).get_id()] = t.arg(0)
        work.extend(t.children())
    return list(atoms.values())


def pin_split(formula, timeout_ms, deadline=None):
    """Split F on its pin atoms A_1..A_n (_pin_atoms): "sat", (residual, lemmas) or None.

    F ≡ ∨_K (F ∧ A_K) ∨ (F ∧ ∧_K ¬A_K). Case K is queried as F[pins of A_K] ∧ A_K,
    which has exactly the models of F ∧ A_K (substitution of equals), so a SAT case
    is a model of F; the residual F[A_K := false] ∧ ∧_K ¬A_K has exactly the models of
    F ∧ ∧_K ¬A_K. With every case refuted (the lemmas), F is UNSAT iff the residual is.
    No atoms, too many, a case unknown, or out of time: None (nothing proved).
    """
    atoms = _pin_atoms(formula)
    if not atoms or len(atoms) > _PIN_MAX_CASES:
        return None
    end = monotonic() + 2 * timeout_ms / 1000
    if deadline is not None:
        end = min(end, deadline)
    lemmas = []
    for n, atom in enumerate(atoms):
        left = int((end - monotonic()) * 1000)
        if left <= 0:
            return None
        started, query = monotonic(), And(simplify(substitute(formula, *_pins(atom))), atom)
        answer = solve_query(query, min(_QUICK_EXACT_MS, timeout_ms, left))
        if answer == "sat":
            return "sat"
        if answer != "unsat":
            return None
        lemmas.append(Obligation(f"pin_case_{n}", query.sexpr(), "unsat", elapsed_seconds=monotonic() - started))
    residual = simplify(And(substitute(formula, *[(a, BoolVal(False)) for a in atoms]), *[Not(a) for a in atoms]))
    return residual, tuple(lemmas)


# ponytail: one limb's worth of shift amounts (x86 splits a 256-bit shift at multiples of 64).
_SHIFT_MAX_CASES = 64
_SHIFT_KINDS = (Z3_OP_BSHL, Z3_OP_BLSHR, Z3_OP_BASHR)


def _scalar_constants(term):
    """Uninterpreted bit-vector constants of `term` outside binders, by id."""
    found, seen, work = {}, set(), [term]
    while work:
        t = work.pop()
        if t.get_id() in seen or not is_app(t):
            continue
        seen.add(t.get_id())
        if _substitutable(t) and is_bv(t):
            found[t.get_id()] = t
        work.extend(t.children())
    return found


def _shift_amount_constants(formula):
    """Constants in the non-literal amount of a shift outside binders, sorted by name."""
    found, seen, work = {}, set(), [formula]
    while work:
        t = work.pop()
        if t.get_id() in seen or not is_app(t):
            continue
        seen.add(t.get_id())
        if t.decl().kind() in _SHIFT_KINDS and not is_bv_value(t.arg(1)):
            found.update(_scalar_constants(t.arg(1)))
        work.extend(t.children())
    return sorted(found.values(), key=lambda c: (str(c), c.get_id()))


def _small_conjuncts(conjuncts, v, max_size=4096):
    """Top-level conjuncts mentioning v that are small pure bit-vector formulas."""
    return [c for c in conjuncts if v.get_id() in _scalar_constants(c) and _pure_bv(c)
            and _text_size(c) <= max_size]


def _refuted(query, timeout_ms, name):
    started = monotonic()
    if solve_query(query, timeout_ms) != "unsat":
        return None
    return Obligation(name, query.sexpr(), "unsat", elapsed_seconds=monotonic() - started)


def _shift_bounds(premise, v, timeout_ms):
    """(lo, hi, lemmas): premise ⊨ lo <= v <= hi (unsigned), the lemmas refuting
    premise ∧ v < lo and premise ∧ v > hi; binary search, any non-UNSAT answer
    counted as "not a bound" (bounds only widen, never wrongly narrow). Only
    the two final refutations are proof; the search steps merely pick them."""
    n = v.size()
    solver = _solver(timeout_ms, premise)
    solver.add(premise)

    def refuted(bound):
        solver.push()
        solver.add(bound)
        answer = solver.check()
        solver.pop()
        return answer == unsat
    good, bad = 0, 1 << n  # premise ∧ v < good is UNSAT (trivially for 0)
    while bad - good > 1:
        mid = (good + bad) // 2
        good, bad = (mid, bad) if refuted(ULT(v, mid)) else (good, mid)
    lo = good
    good, bad = (1 << n) - 1, -1  # premise ∧ v > good is UNSAT (trivially for the maximum)
    while good - bad > 1:
        mid = (good + bad) // 2
        good, bad = (mid, bad) if refuted(UGT(v, mid)) else (good, mid)
    hi = good
    lemmas = []
    for name, query, trivial in (("shift_lower", And(premise, ULT(v, lo)), lo == 0),
                                 ("shift_upper", And(premise, UGT(v, hi)), hi == (1 << n) - 1)):
        if not trivial:
            lemma = _refuted(query, timeout_ms, name)
            if lemma is None:
                return None
            lemmas.append(lemma)
    return lo, hi, lemmas


def shift_split(formula, timeout_ms, deadline=None):
    """Refute F by one case per value of a shift-amount constant: "sat", lemmas or None.

    x86 shifts a 256-bit word limb by limb (amount v mod 64, the limb offset
    from range compares on v), EVM shifts the whole word: bit-blasting the
    256-bit barrel shifter against the 64-bit ones stalls (Permit2 4837
    x86_maps_12_0 / 14_0: every route unknown for 2400s), while with v a
    literal (and the amount's high limbs fixed) both sides become constant
    shifts (63 cases, 6s in all).

    Each constant v of a symbolic shift amount gets bounds lo <= v <= hi from
    F's small pure bit-vector top-level conjuncts (the two bound refutations
    are lemmas, so F ⊨ lo <= v <= hi). A constant with one value is fixed
    (F ≡ F ∧ v = lo; the high limbs of EVM's 256-bit amount). Of the others,
    the one with the fewest values is split: F ≡ ∨_{lo<=c<=hi} (F ∧ v = c ∧
    fixed), and the models of that case are exactly the models of
    F[v := c, fixed] extended by those values (substitution of equals; none
    of them occurs in it). So F is UNSAT iff every case query is (the case
    lemmas), and a SAT case is a model of F. Empty bounds (lo > hi) refute F
    by the bound lemmas alone. Nothing fixed or split, more than
    _SHIFT_MAX_CASES values, a case unknown, or out of time: None.
    """
    candidates = _shift_amount_constants(formula)
    if not candidates:
        return None
    end = monotonic() + 1e9 if deadline is None else deadline
    conjuncts = _conjuncts(formula)
    fixed, lemmas, best = [], [], None
    for v in candidates:
        premise = _small_conjuncts(conjuncts, v)
        if not premise or monotonic() >= end:
            continue
        bounds = _shift_bounds(And(*premise), v, min(_QUICK_EXACT_MS, timeout_ms))
        if bounds is None:
            continue
        lo, hi, found = bounds
        if lo > hi:
            return tuple(found)  # the small conjuncts alone are UNSAT
        if lo == hi:
            fixed.append((v, BitVecVal(lo, v.size())))
            lemmas += found
        elif hi - lo < _SHIFT_MAX_CASES and (best is None or hi - lo < best[2] - best[1]):
            best = (v, lo, hi, found)
    if best is None and not fixed:
        return None
    values = [None]
    if best is not None:
        v, lo, hi, found = best
        lemmas += found
        values = [BitVecVal(c, v.size()) for c in range(lo, hi + 1)]
    for c in values:
        left = int((end - monotonic()) * 1000)
        if left <= 0:
            return None
        started = monotonic()
        query = simplify(substitute(formula, *fixed, *(() if c is None else ((best[0], c),))), bv_sort_ac=True)
        answer = "unsat" if is_false(query) else solve_query(query, min(timeout_ms, left))
        if answer == "sat":
            return "sat"
        if answer != "unsat":
            return None
        lemmas.append(Obligation(f"shift_case_{len(lemmas)}", query.sexpr(), "unsat", elapsed_seconds=monotonic() - started))
    return tuple(lemmas)


def _conjuncts(formula):
    work, out = [formula], []
    while work:
        term = work.pop()
        if is_and(term):
            work.extend(term.children())
        else:
            out.append(term)
    return out


def _goal_split(formula):
    """R ∧ ¬(g_1 ∧ … ∧ g_n) -> [R ∧ ¬g_1, …, R ∧ ¬g_n], or None.

    F ≡ ∨_k (R ∧ ¬g_k), so F is UNSAT iff every part is (and a SAT part is a
    model of F). The conjunct is the last argument of the top-level And, where
    prove() puts a terminal pair's ¬goal (unary Ands from the SMT2 round trip
    are unwrapped). Any ¬(∧) conjunct would be sound; this one is the goal.
    """
    while is_and(formula) and formula.num_args() == 1:
        formula = formula.arg(0)
    if not (is_and(formula) and formula.num_args() >= 2):
        return None
    *rest, last = formula.children()
    if not (is_not(last) and is_and(last.arg(0)) and last.arg(0).num_args() >= 2):
        return None
    return [And(*rest, Not(g)) for g in last.arg(0).children()]


_GOAL_NAME = re.compile(r"_goal_(\d+)_of_(\d+)$")
# Diagnostic / A-B switch: BLOCK_ROUTE_ORDER=static keeps the fixed route table.
_ROUTE_ORDER_STATIC = __import__("os").environ.get("BLOCK_ROUTE_ORDER") == "static"


def _route_class(name):
    """Obligations whose routes behave alike: the name without its path
    indices, goal-split parts kept apart (pair_67_9_goal_2_of_7 ->
    pair_goal_2_of_7, x86_maps_3_5 -> x86_maps). Siblings of one node share
    the relation goals, so part k of every pair has the same shape.
    H2/H0 edge parts lose their context / edge / target indices too
    (H2_c0_0_5_t1_memory_0 -> H2_memory): one goal behaves alike on every
    edge, and with the indices each edge was a class of its own, so what
    refuted it on the first edge never went first on the next."""
    m = _GOAL_NAME.search(name)
    base = name[:m.start()] if m else name
    return re.sub(r"_[ct]?\d+(?=_|$)", "", base) + (m.group(0) if m else "")


def _winners_first(routes, stats):
    """`routes` with those that refuted an obligation of this class before
    first (most refutations per second spent on the route, wins and misses,
    first); the rest keep their order. `stats`: route -> (wins, seconds).

    Only the order changes: every route is still tried until one refutes F.
    Safe 5377 d30 pairs: the memory goal part is refuted only by normalised
    unification, after ~400-470s of routes that never refute it.
    """
    won = sorted((r for r in routes if stats.get(r, (0, 0.0))[0]),
                 key=lambda r: -stats[r][0] / max(stats[r][1], 1e-3))
    return won + [r for r in routes if r not in won]


def _array_disequality(term):
    """(A, B) for a top-level ¬(A = B) / distinct(A, B) over 1-dim arrays, else None."""
    if is_not(term) and is_eq(term.arg(0)):
        term = term.arg(0)
    elif not (is_distinct(term) and term.num_args() == 2):
        return None
    a, b = term.children()
    if a.sort().kind() != Z3_ARRAY_SORT or Z3_get_array_arity(a.ctx_ref(), a.sort().ast) != 1:
        return None
    return a, b


def skolemize_array_disequalities(formula, timeout_ms=1000):
    """F = R ∧ ¬(A = B) -> R ∧ A[w] ≠ B[w], w fresh; returns (F', lemmas).

    Only for ¬(A = B) as a TOP-LEVEL conjunct of the refuted formula. There
    F' is equisatisfiable with F: a model of F has, by extensionality, an
    index i with A[i] ≠ B[i], and w := i extends it to a model of F'; a model
    of F' is one of F. So UNSAT(F') gives UNSAT(F). Each occurrence gets its
    own w: one shared witness for two disequalities can be unsatisfiable when
    each alone is not. Under a binder (w would depend on the bound variable)
    or as the goal of an obligation (¬¬(A = B)) this reading is wrong, so
    nothing but top-level conjuncts is touched. Select over a Lambda then
    beta-reduces (simplify), so the memory views become plain reads at w.
    The lemma refutes a generic extensionality instance (fresh arrays of the
    same sort), valid for all arrays, hence for A and B.
    """
    parts, out, lemmas = _conjuncts(formula), [], []
    for term in parts:
        pair = _array_disequality(term)
        if pair is None:
            out.append(term)
            continue
        a, b = pair
        w = FreshConst(a.sort().domain(), "ext_w")
        out.append(simplify(Select(a, w) != Select(b, w)))
        x, y, i = FreshConst(a.sort(), "ext_a"), FreshConst(a.sort(), "ext_b"), FreshConst(a.sort().domain(), "ext_i")
        generic = And(x != y, ForAll([i], Select(x, i) == Select(y, i)))
        started = monotonic()
        lemmas.append(Obligation(f"extensionality_{len(lemmas)}", generic.sexpr(), solve_query(generic, timeout_ms),
                                 elapsed_seconds=monotonic() - started))
    if not lemmas:
        return formula, ()
    return And(*out), tuple(lemmas)


def _read_disequality(term):
    """(A, i, B, j) for a top-level ¬(A[i] = B[j]) / distinct(A[i], B[j]), else None."""
    if is_not(term) and is_eq(term.arg(0)):
        term = term.arg(0)
    elif not (is_distinct(term) and term.num_args() == 2):
        return None
    x, y = term.children()
    if not (is_select(x) and is_select(y) and x.num_args() == 2 and y.num_args() == 2):
        return None
    return x.arg(0), x.arg(1), y.arg(0), y.arg(1)


def _same_offset(kb, ka, d):
    gap = simplify(kb - ka - d)
    return is_bv_value(gap) and gap.as_long() == 0


def peel_matching_stores(formula, timeout_ms=1000):
    """F with each top-level ¬(A[i] = B[j]) whose arrays end in pairwise
    matching stores replaced by the read of what lies below them; (F', lemmas)
    or None when nothing peels.

    A = store(X, a, v), B = store(Y, b, u) match when b - a ≡ j - i (=: d)
    and v ≡ u (word-level simplifier). Then A[i] ≠ B[j] implies X[i] ≠ Y[j]:
    i = a would read v on both sides (j = a + d = b), and otherwise
    j = i + d ≠ a + d = b too, so both reads fall through. Repeated from the
    top of both chains while they match. F ⊨ F' (each replaced conjunct is
    implied by its original), so only UNSAT of F' transfers back; the facts
    i ≠ a are dropped, which only weakens F' further. The lemma refutes the
    generic step (fresh arrays and words of the same sorts), valid for all
    instances. Safe 5377 d30 pair_68_58: both memories write the same 320
    bytes (EVM at fmp + k, x86 at R15 + fmp + k) over a CALLDATACOPY lambda;
    the opaque UF query needs 113-126s, the peeled one 5s.
    """
    out, lemmas, sorts, peeled = [], [], [], 0
    for term in _conjuncts(formula):
        found = _read_disequality(term)
        if found is None:
            out.append(term)
            continue
        a, i, b, j = found
        d, n = simplify(j - i), 0
        while is_store(a) and is_store(b) and a.num_args() == 3 and b.num_args() == 3:
            (x, ka, va), (y, kb, vb) = a.children(), b.children()
            if not (_same_offset(kb, ka, d) and (va.eq(vb) or is_true(simplify(va == vb, bv_sort_ac=True)))):
                break
            a, b, n = x, y, n + 1
        if not n:
            out.append(term)
            continue
        if not any(s.eq(a.sort()) for s in sorts):
            gx, gy = FreshConst(a.sort(), "peel_x"), FreshConst(a.sort(), "peel_y")
            gi, ga, gd = (FreshConst(a.sort().domain(), f"peel_{s}") for s in "iad")
            gv = FreshConst(a.sort().range(), "peel_v")
            generic = And(Select(Store(gx, ga, gv), gi) != Select(Store(gy, ga + gd, gv), gi + gd),
                          Select(gx, gi) == Select(gy, gi + gd))
            started = monotonic()
            answer = solve_query(generic, timeout_ms)
            if answer != "unsat":
                return None
            sorts.append(a.sort())
            lemmas.append(Obligation(f"store_peel_{len(lemmas)}", generic.sexpr(), answer,
                                     elapsed_seconds=monotonic() - started))
        out.append(simplify(Select(a, i) != Select(b, j)))
        peeled += n
    if not peeled:
        return None
    return And(*out), tuple(lemmas)


def generalize_array_terms(formula, max_rounds=8):
    """F with every closed read Select(A, i) replaced by h_A(i) and every UF
    application f(x, A) with array arguments by g_{f,A}(x): one fresh UF per
    (declaration, syntactic array arguments), so congruence in the other
    arguments survives, array semantics (read-over-write, extensionality) not.
    All-literal other arguments get one constant per (declaration, arrays,
    literals) instead: equal literals are one AST, distinct ones never meet,
    and the bit-blaster is spared the Ackermann pairs.

    Only adds models: a model M of F extends to F' by h_A(i) := M(A)[i] and
    g_{f,A}(x) := M(f)(x, M(A)) (A is one term, so one value), and F' then
    evaluates as F; UNSAT(F') gives UNSAT(F). Binders are not entered (a term
    there may be open); outermost terms per round, nested ones next round.
    Returns F unchanged if terms remain after `max_rounds`.
    """
    original, fresh = formula, {}
    for _ in range(max_rounds):
        found, seen, work = {}, set(), [formula]
        while work:
            t = work.pop()
            if t.get_id() in seen or not is_app(t):
                continue
            seen.add(t.get_id())
            if (is_select(t) and not is_array(t)) or (
                    t.decl().kind() == Z3_OP_UNINTERPRETED and any(_is_array_term(a) for a in t.children())):
                found[t.get_id()] = t
                continue
            work.extend(t.children())
        if not found:
            return formula
        pairs = []
        for t in found.values():
            arrays = [a for a in t.children() if _is_array_term(a)]
            rest = [a for a in t.children() if not _is_array_term(a)]
            if all(is_bv_value(a) for a in rest):
                arrays, rest = t.children(), []  # literal arguments: one constant, no Ackermann pairs
            key = (t.decl().get_id(), *(a.get_id() for a in arrays))
            if key not in fresh:
                fresh[key] = FreshFunction(*(a.sort() for a in rest), t.sort()) if rest else FreshConst(t.sort(), "gen_arr")
            pairs.append((t, fresh[key](*rest) if rest else fresh[key]))
        formula = substitute(formula, *pairs)
    return original


def _pure_bv(formula):
    seen, work = set(), [formula]
    while work:
        t = work.pop()
        if t.get_id() in seen:
            continue
        seen.add(t.get_id())
        if not is_app(t) or t.sort().kind() not in (Z3_BOOL_SORT, Z3_BV_SORT):
            return False
        if t.decl().kind() == Z3_OP_UNINTERPRETED and any(
                d.kind() not in (Z3_BOOL_SORT, Z3_BV_SORT) for d in (t.decl().domain(i) for i in range(t.num_args()))):
            return False
        work.extend(t.children())
    return True


def refute_over_bv_abstraction(formula, timeout_ms):
    """(query, answer) for a pure-BV over-approximation Q of F, bit-blasted
    after Ackermannization. Only "unsat" means anything (then F is UNSAT).

    Q = generalize_array_terms(abstract_nonlinear_mul(F) ∧ square_monotonicity
    ∧ mul_truncation_axioms): the abstraction and the generalisation only add
    models, the axioms hold for bvmul. Memory-cost carries over several
    squared word counts (Safe 4524's RETURNDATACOPY word gas + expansion
    cost) stall QF_AUFBV's core for minutes; Ackermannized bit-blasting of
    the abstraction refutes them in seconds. A formula whose refutation needs
    the arrays (memory views) is left to the other routes ("unknown").
    """
    functions = {}
    abstraction, _ = abstract_nonlinear_mul(formula, functions=functions)
    query = simplify(generalize_array_terms(And(
        abstraction, *square_monotonicity(abstraction, functions), *mul_truncation_axioms(abstraction, functions))))
    if not _pure_bv(query) or timeout_ms <= 0:
        return query, "unknown"
    return query, solve_pure_bv(query, timeout_ms)


def solve_pure_bv(query, timeout_ms):
    """Ackermannize + bit-blast a pure-BV query; proof_cache as in solve_query."""
    key = proof_cache.query_key("bv_abstraction", query) if proof_cache.enabled() else None
    cached = proof_cache.cached_answer(key, timeout_ms) if key is not None else None
    if cached is not None:
        return cached
    solver = Then("simplify", "ackermannize_bv", "bit-blast", "sat").solver()
    solver.set("timeout", timeout_ms)
    solver.add(query)
    answer = str(solver.check())
    if key is not None:
        proof_cache.record_answer(key, answer, timeout_ms)
    return answer


def _uf_applications(formula):
    """Closed UF applications (arity > 0) outside binders, keyed by declaration."""
    groups, seen, work = {}, set(), [formula]
    while work:
        term = work.pop()
        if term.get_id() in seen or not is_app(term):  # never enter lambda bodies
            continue
        seen.add(term.get_id())
        if term.decl().kind() == Z3_OP_UNINTERPRETED and term.num_args() > 0:
            groups.setdefault(term.decl().get_id(), {})[term.get_id()] = term
        work.extend(term.children())
    return [list(g.values()) for g in groups.values() if len(g) > 1]


def unify_across(formulas, timeout_ms, deadline=None, cache=None, max_lemmas=64):
    """unify_uf_arguments over a node's pair formulas, one lemma per term pair.

    Sibling pairs share the host-call argument terms, so each (x, y) is proved
    once under Q = the binder-free conjuncts common to every formula holding
    both applications, then rewritten (big := small) only in formulas whose
    own conjuncts include Q: each such F ⊨ Q ⊨ x = y, so F[big := small] is
    UNSAT only if F is. Returns (formulas, lemmas); nothing is ever assumed.
    """
    formulas, lemmas, failed = list(formulas), [], set()
    while len(lemmas) < max_lemmas:
        conj = [{c.get_id(): c for c in _conjuncts(f)} for f in formulas]
        occurs, pairs = {}, {}
        for k, f in enumerate(formulas):
            for apps in _uf_applications(f):
                for i, first in enumerate(apps):
                    for other in apps[i + 1:]:
                        for x, y in zip(first.children(), other.children()):
                            key = (x.get_id(), y.get_id())
                            if not x.eq(y) and key not in failed:
                                pairs[key] = (x, y)
                                occurs.setdefault(key, set()).add(k)
        merged = False
        for key, (x, y) in sorted(pairs.items(), key=lambda kv: _text_size(kv[1][0]) + _text_size(kv[1][1])):
            budget = timeout_ms if deadline is None else min(timeout_ms, int((deadline - monotonic()) * 1000))
            if budget <= 0:
                return formulas, tuple(lemmas)
            common = set.intersection(*(set(conj[k]) for k in occurs[key]))
            parts = [conj[next(iter(occurs[key]))][i] for i in common]
            parts = [c for c in parts if _no_binder(c)]
            cases = _prove_equal(And(*parts), x, y, budget, deadline, cache)
            if cases is None:
                failed.add(key)
                continue
            used = {c.get_id() for c in parts}
            lemmas.extend(Obligation(f"node_unify_{len(lemmas)}_case_{n}", q.sexpr(), "unsat", elapsed_seconds=t)
                          for n, (q, t) in enumerate(cases))
            small, big = sorted((x, y), key=_text_size)
            formulas = [substitute(f, (big, small)) if used <= set(conj[k]) else f
                        for k, f in enumerate(formulas)]
            merged = True
            break
        if not merged:
            break
    return formulas, tuple(lemmas)


def _text_size(term):
    """len(term.sexpr()), memoized per term (pure; _memoized keeps the term alive).

    The merge loops order candidate pairs by this size and re-sort every round:
    unmemoized, printing the same large arguments again each round was 73% of
    unify_uf_arguments on PoolManager 16670 pair_2_74 goal 2 (175s of 240s).
    The value is the same, so the order and every merge are unchanged."""
    return _memoized("text_size", (term,), lambda: len(term.sexpr()))


def _no_binder(term):
    # Memoized per term (pure; _memoized keeps the term alive, so its id stays its own):
    # unify_uf_arguments and the light-premise probe ask it of every premise conjunct per
    # candidate pair (Safe 5377 d30: ~195 conjuncts, 0.25s per pass, ~100 passes per pair).
    return _memoized("no_binder", (term,), lambda: _no_binder_uncached(term))


def _no_binder_uncached(term):
    seen, work = set(), [term]
    while work:
        t = work.pop()
        if t.get_id() in seen:
            continue
        seen.add(t.get_id())
        if not is_app(t):
            return False
        work.extend(t.children())
    return True


def _uf_app_constants(*terms):
    """Fresh constants for the outermost closed UF applications.

    Replacing each by its constant only adds models (interpret the constant as
    the application's value), so UNSAT transfers back. It keeps path atoms
    about host results (e.g. RETURNDATASIZE != 0) in lemma premises while
    dropping the memory arrays those applications take as arguments.
    """
    found, seen, work = {}, set(), list(terms)
    while work:
        t = work.pop()
        if t.get_id() in seen or not is_app(t):
            continue
        seen.add(t.get_id())
        if t.decl().kind() == Z3_OP_UNINTERPRETED and t.num_args() > 0:
            found[t.get_id()] = t
        else:
            work.extend(t.children())
    return [(t, FreshConst(t.sort(), "uf_app")) for t in found.values()]


def _ite_conditions(term):
    found, seen, work = {}, set(), [term]
    while work:
        t = work.pop()
        if t.get_id() in seen or not is_app(t):  # conditions under binders may be open
            continue
        seen.add(t.get_id())
        if t.decl().kind() == Z3_OP_ITE:
            found[t.arg(0).get_id()] = t.arg(0)
        work.extend(t.children())
    return list(found.values())


def _refute_by_cases(premise, goal, budget_ms, deadline=None, probe_ms=2000, max_nodes=128):
    """Refute `premise ∧ goal`, lazily splitting on the ite guards of `goal`.

    A node q splits into c ∧ q[c:=true] and ¬c ∧ q[c:=false]; the two cover
    q and each substitution is an equivalence under its literal, so all leaves
    UNSAT is exactly q UNSAT. Splitting lets the word-level simplifier cancel
    telescoping gas sums that bit-blasting cannot. Returns the refuted queries
    with times, or None (never a partial result) if any node is SAT, a leaf
    is not UNSAT, or the node/time budget runs out.
    """
    end = monotonic() + budget_ms / 1000
    if deadline is not None:
        end = min(end, deadline)
    proofs, work, nodes = [], [(premise, simplify(goal, som=True, bv_sort_ac=True))], 0
    while work:
        premise, goal = work.pop()
        query = simplify(And(premise, goal), bv_sort_ac=True)
        if is_false(query):
            continue
        conditions = _ite_conditions(goal)  # premise guards are rarely what blocks the goal
        nodes += 1
        left = int((end - monotonic()) * 1000)
        if nodes > max_nodes or left <= 0:
            return None
        started = monotonic()
        answer = solve_query(query, min(probe_ms, left) if conditions else left)
        if answer == "unsat":
            proofs.append((query, monotonic() - started))
            continue
        if answer == "sat" or not conditions:
            return None
        c = conditions[0]
        for literal, value in ((c, True), (Not(c), False)):
            work.append((And(literal, substitute(premise, (c, BoolVal(value)))),
                         simplify(substitute(goal, (c, BoolVal(value))), som=True, bv_sort_ac=True)))
    return proofs


def uf_guards(formula):
    """Guards to split on before UF argument unification, smallest first.

    A guard is the condition of an ite (outside binders, itself binder-free)
    with an application of a multiply-applied UF in a branch. Returns
    [[raw condition terms]], grouped by their simplified form (equivalent
    spellings), ordered by that form's size.

    Branch-wise argument spellings agree only under their guard: x86 SDIV is a
    sign-branch tree, one holiman_udiv(a, b) / (-a, b) / (a, -b) / (|a|, |b|)
    per branch, against EVM's single holiman_udiv(|a|, |b|) (PoolManager 16670
    pair_2_74 / pair_4_84 goal 2). Unconditionally the arguments differ, so
    unify_uf_arguments cannot merge them (each such pair ~20s unknown); under
    the sign guard the dead branches simplify away and the rest merge."""
    multi = {apps[0].decl().get_id() for apps in _uf_applications(formula)}
    if not multi:
        return []
    has, work = {}, [(formula, False)]
    while work:  # has[id]: an application of a multiply-applied UF below (binders not entered)
        t, ready = work.pop()
        if t.get_id() in has:
            continue
        if not is_app(t):
            has[t.get_id()] = False
            continue
        if not ready:
            work.append((t, True))
            work.extend((c, False) for c in t.children() if c.get_id() not in has)
            continue
        has[t.get_id()] = ((t.decl().kind() == Z3_OP_UNINTERPRETED and t.decl().get_id() in multi)
                           or any(has[c.get_id()] for c in t.children()))
    groups, seen, work = {}, set(), [formula]
    while work:
        t = work.pop()
        if t.get_id() in seen or not is_app(t):
            continue
        seen.add(t.get_id())
        if (t.decl().kind() == Z3_OP_ITE and (has[t.arg(1).get_id()] or has[t.arg(2).get_id()])
                and _no_binder(t.arg(0))):
            c = simplify(t.arg(0))
            if not (is_true(c) or is_false(c)):
                groups.setdefault(c.get_id(), (c, {}))[1].setdefault(t.arg(0).get_id(), t.arg(0))
        work.extend(t.children())
    return [list(raws.values()) for c, raws in sorted(groups.values(), key=lambda g: _text_size(g[0]))]


def assume_guard(formula, raws, value):
    """F under one guard literal: L ∧ simplify(F[r := value for each r]),
    L = raws[0] (value True) or its negation. The raws simplify to one form,
    so they are equivalent: under L each r has the value `value` and the
    substitution is an equivalence; simplify is one too. The two cases
    (value True / False) cover every model of F, so F is UNSAT iff both are."""
    literal = raws[0] if value else Not(raws[0])
    return And(literal, simplify(substitute(formula, *[(r, BoolVal(value)) for r in raws])))


def _is_array_term(t):
    # z3py is_array() is False for Lambda terms (QuantifierRef), which are arrays too.
    return t.sort().kind() == Z3_ARRAY_SORT


def _differ(x, y):
    if _is_array_term(x):
        index = FreshConst(x.sort().domain(), "unify_idx")
        return Select(x, index) != Select(y, index)
    return x != y


def _heavy(term):
    """True if `term` has a product of non-literals or a UF application (the
    multiplication abstraction's products, host results): the gas sums over
    symbolic memory sizes, which dominate bit-blasting. Memoized as _no_binder
    (0.5s per pass over a Safe 5377 d30 premise, once per candidate pair)."""
    return _memoized("heavy", (term,), lambda: _heavy_uncached(term))


def _heavy_uncached(term):
    if _nonlinear_mul_terms(term):
        return True
    seen, work = set(), [term]
    while work:
        t = work.pop()
        if t.get_id() in seen or not is_app(t):
            continue
        seen.add(t.get_id())
        if t.decl().kind() == Z3_OP_UNINTERPRETED and t.num_args() > 0:
            return True
        work.extend(t.children())
    return False


# ponytail: fixed 2s cap (the unsat_core probe's); the light queries measured 0.3-0.5s.
_LIGHT_MS = 2000


def _refute_over_light_premise(parts, goal, budget_ms, retry_ms=0):
    """([(query, seconds)], kept conjunct ids) refuting `parts` without their
    binder-free _heavy conjuncts, ∧ goal; or None.

    `retry_ms` > budget_ms: an "unknown" (timed out, not SAT) query is solved
    once more with that budget. Misses are SAT in ~0.2s (Safe 5377 d30), so
    only queries near the cap pay; Safe 5377 d30 pair_68_58's sha3 memory
    arguments refute in 0.9-2.1s against the 2s cap.

    Dropping conjuncts only weakens a conjunction (every model of all parts is
    one of the kept ones), so UNSAT of kept ∧ goal is UNSAT of parts ∧ goal;
    SAT/unknown proves nothing and the caller goes on with every conjunct.
    Only tried when something is dropped. Conjuncts under a binder (memory
    goals) stay. Safe 5377 d30 pair_58_13: the two sha3 memory arguments are
    equal under 8 linear conjuncts (0.3s); with all ~200 (gas sums of symbolic
    msize) the query needs ~47s and the 2s-probe case tree gives up.
    """
    light = [c for c in parts if not (_no_binder(c) and _heavy(c))]
    if len(light) == len(parts) or budget_ms <= 0:
        return None
    started = monotonic()
    query = simplify(And(*light, goal))
    answer = solve_query(query, budget_ms)
    if answer == "unknown" and retry_ms > budget_ms:
        answer = solve_query(query, retry_ms)
    if answer != "unsat":
        return None
    return [(query, monotonic() - started)], frozenset(c.get_id() for c in light)


def _prove_equal(premise, x, y, budget_ms, deadline, cache=None):
    """Refuted queries showing premise ⊨ x = y, or None. UF applications are
    made opaque (only adds models), which keeps memory arrays out.

    `cache` (optional dict) reuses a refutation found under conjuncts Q ⊆ the
    current premise's conjuncts: P ⊇ Q, so P ∧ x≠y is UNSAT too. Failures are
    only reused for premises no stronger than the failed one (time saving).

    Keys and conjunct sets are AST ids, and the cache outlives the formulas
    they came from: a proof entry keeps x, y and its conjuncts alive (third
    field, flat: x, y, *conjuncts), so none of its ids can be recycled for
    another term while cached (a recycled one could match a premise that does
    not imply x = y). A failure entry holds nothing: a false match there only
    costs a miss."""
    parts = _conjuncts(premise)
    conjuncts = frozenset(c.get_id() for c in parts)
    key = tuple(sorted((x.get_id(), y.get_id())))
    if cache is not None:
        for used, proofs, _alive in cache.get(key, ()):
            if proofs is not None and used <= conjuncts:
                return proofs
            if proofs is None and conjuncts <= used:
                return None
    differ = _differ(x, y)
    opaque = _uf_app_constants(premise, differ)
    hide = (lambda t: substitute(t, *opaque)) if opaque else (lambda t: t)
    light_ms, retry_ms = min(budget_ms, _LIGHT_MS), budget_ms
    if deadline is not None:
        left = int((deadline - monotonic()) * 1000)
        light_ms, retry_ms = min(light_ms, left), min(retry_ms, left)
    proofs = _refute_over_light_premise(parts, hide(differ), light_ms, retry_ms)
    if proofs is not None:
        if cache is not None:
            kept = [c for c in parts if c.get_id() in proofs[1]]
            cache.setdefault(key, []).append((proofs[1], proofs[0], (x, y, *kept)))
        return proofs[0]
    if cache is not None:
        # Cache only the conjuncts the refutation used (unsat core), so the
        # lemma transfers to sibling pairs whose path conditions differ.
        started, outcome = monotonic(), {}
        used = unsat_core([hide(c) for c in parts], hide(differ), min(budget_ms, 2000), outcome)
        if used is not None:
            used = [parts[i] for i in used]
            proofs = [(And(*(hide(c) for c in used), hide(differ)), monotonic() - started)]
            cache.setdefault(key, []).append((frozenset(c.get_id() for c in used), proofs, (x, y, *used)))
            return proofs
        if outcome.get("answer") == "sat":
            # hide(premise) ∧ hide(differ) has a model: the case tree below refutes
            # exactly that formula, so it cannot succeed (Safe 5377 d30 pairs: ~100
            # such candidates per pair, 1.5-2.3s of case tree each). A failure
            # entry, recorded under the full premise as a case-tree failure is.
            cache.setdefault(key, []).append((conjuncts, None, ()))
            return None
    proofs = _refute_by_cases(hide(premise), hide(differ), budget_ms, deadline)
    if cache is not None:
        cache.setdefault(key, []).append((conjuncts, proofs, () if proofs is None else (x, y, *parts)))
    return proofs


def _bv_value_terms(formula, limit):
    """Closed, non-literal BV applications outside binders (for sweeping)."""
    found, seen, work = {}, set(), [formula]
    while work and len(found) < limit:
        t = work.pop()
        if t.get_id() in seen or not is_app(t):
            continue
        seen.add(t.get_id())
        if is_bv(t) and t.num_args() > 0 and t.decl().kind() != Z3_OP_UNINTERPRETED:
            found[t.get_id()] = t
        work.extend(t.children())
    return list(found.values())


def _prove_equal_lia(premise, x, y, budget_ms, deadline, cache=None):
    """sweep_equalities prover: x = y as an identity refuted over lia_query (premise unused)."""
    started, query = monotonic(), lia_query(_differ(x, y))
    if query is None or solve_query(query, budget_ms) != "unsat":
        return None
    return [(query, monotonic() - started)]


def sweep_equalities(formula, timeout_ms, deadline=None, seeds=3, max_terms=1000, lemma_ms=2000, cache=None,
                     prove=_prove_equal):
    """SAT sweeping: merge BV subterms proved equal under F's premise.

    Candidates share values under random small assignments (UF applications
    opaque); each merge still needs a refuted `P ∧ t ≠ rep` (_prove_equal),
    so fingerprints only choose what to try. Same soundness as
    unify_uf_arguments: every model of F is a model of the rewrite.
    """
    premise = And(*(c for c in _conjuncts(formula) if _no_binder(c)))
    opaque = _uf_app_constants(formula)
    terms = _bv_value_terms(formula, max_terms)
    leaves, seen, work = {}, set(), [formula, *(k for _, k in opaque)]
    while work:
        t = work.pop()
        if t.get_id() in seen or not is_app(t):
            continue
        seen.add(t.get_id())
        if is_bv(t) and t.num_args() == 0 and t.decl().kind() == Z3_OP_UNINTERPRETED:
            leaves[t.get_id()] = t
        work.extend(t.children())
    prints = {t.get_id(): [] for t in terms}
    for seed in range(seeds):
        rng = Random(seed)
        # ponytail: small values keep premise-bounded sizes (CDS < 2^37) equal; misses only cost merges.
        values = [(c, BitVecVal(rng.choice((rng.getrandbits(7), rng.getrandbits(12) * 32, rng.getrandbits(20))),
                                c.size())) for c in leaves.values()]
        for t in terms:
            v = simplify(substitute(substitute(t, *opaque) if opaque else t, *values))
            prints[t.get_id()].append(v.as_long() if is_bv_value(v) else None)
    groups = {}
    for t in terms:
        if None not in prints[t.get_id()]:
            groups.setdefault((t.size(), tuple(prints[t.get_id()])), []).append(t)
    lemmas = []
    for group in groups.values():
        group.sort(key=_text_size)
        for t in group[1:]:
            if deadline is not None and monotonic() >= deadline:
                return formula, tuple(lemmas)
            proofs = prove(premise, group[0], t, min(lemma_ms, timeout_ms), deadline, cache)
            if proofs is None:
                continue
            lemmas.extend(Obligation(f"sweep_{len(lemmas)}_case_{n}", q.sexpr(), "unsat", elapsed_seconds=s)
                          for n, (q, s) in enumerate(proofs))
            formula = substitute(formula, (t, group[0]))  # group[0] is smaller: terminates
    return formula, tuple(lemmas)


def restore_rewritten_conjuncts(before, after):
    """after ∧ the ite-free, binder-free conjuncts of `before` the rewrite changed.

    A premise-justified merge (sweep_equalities) also rewrites the conjunct
    that justified it, which can erase that fact (Safe 9733: the x86 256-bit
    borrow chain `pos + 32 >= 160` became `z3[0] == 0`, so EVM's
    max(pos + 32, 160) no longer collapsed and the UF abstraction went SAT).
    Every model of `before` satisfies `after` and each of its own conjuncts,
    so only UNSAT of the result transfers back, as before. Conjuncts with ite
    guards stay out: they would only widen the case tree.
    """
    kept = {c.get_id() for c in _conjuncts(after)}
    lost = [c for c in _conjuncts(before)
            if c.get_id() not in kept and _no_binder(c) and not _ite_conditions(c)]
    return And(after, *lost) if lost else after


def _uf_nesting(term, decl, memo):
    """How deep applications of `decl` nest in `term` (binder bodies included)."""
    work = [(term, False)]
    while work:
        t, ready = work.pop()
        if t.get_id() in memo:
            continue
        kids = [t.body()] if is_quantifier(t) else (t.children() if is_app(t) else [])
        if not ready:
            work.append((t, True))
            work.extend((c, False) for c in kids if c.get_id() not in memo)
            continue
        own = int(is_app(t) and t.decl().eq(decl))
        memo[t.get_id()] = own + max((memo[c.get_id()] for c in kids), default=0)
    return memo[term.get_id()]


def unify_uf_arguments(formula, timeout_ms, deadline=None, max_lemmas=64, cache=None, on_merge=None):
    """Merge differing arguments of same-declaration UF applications.

    For a pair (x, y) of closed arguments, `P ∧ x ≠ y` (array: at a fresh
    index) is refuted where P is the binder-free top-level conjuncts of the
    formula F (UF applications made opaque, see _uf_app_constants), so
    F ⊨ x = y. Every model of F then satisfies F[big := small]: only
    UNSAT of the result transfers back. Unproved pairs are left untouched.
    Smallest pairs first, so inner merges (e.g. squared word counts under the
    multiplication UF) make outer arguments syntactically closer. Pairs whose
    applications nest the function equally deep come before all others
    (only the order changes): a chain h_k = f(..h_{k-1}..) built by each side
    pairs level by level, while a cross-level pair is rarely equal and costs
    its full budget to fail (Permit2 1327 x86_maps_0_0: three sha3_slice
    levels per side, each level pair proved in <1s, but the 30s failures of
    the smaller cross-level pairs ran the route out before level 3).
    `on_merge(F', lemmas, merged)`, if given, is called after each merge (merged:
    the term both arguments now are); a true result stops merging (the caller
    has what it needs from F').
    """
    lemmas, failed = [], set()
    while len(lemmas) < max_lemmas:
        premise = And(*(c for c in _conjuncts(formula) if _no_binder(c)))
        pairs, owners = {}, {}  # arg key -> (x, y, depth gap); arg key -> key lists of the app pairs needing it
        for apps in _uf_applications(formula):
            memo = {}
            for i, first in enumerate(apps):
                for other in apps[i + 1:]:
                    diff = [(x, y) for x, y in zip(first.children(), other.children()) if not x.eq(y)]
                    keys = [(x.get_id(), y.get_id()) for x, y in diff]
                    gap = abs(_uf_nesting(first, first.decl(), memo) - _uf_nesting(other, first.decl(), memo))
                    for (x, y), key in zip(diff, keys):
                        owners.setdefault(key, []).append(keys)
                        if key not in failed:
                            pairs[key] = (x, y, min(gap, pairs.get(key, (0, 0, gap))[2]))
        if not pairs:
            break
        merged = False
        for key, (x, y, _) in sorted(pairs.items(), key=lambda kv: (
                kv[1][2] > 0, _text_size(kv[1][0]) + _text_size(kv[1][1]))):
            if all(any(k in failed for k in keys) for keys in owners[key]):
                continue  # these applications can no longer become one term (Safe 5377 hash1 vs hash2)
            budget = timeout_ms
            if deadline is not None:
                budget = min(budget, int((deadline - monotonic()) * 1000))
            if budget <= 0:
                return formula, tuple(lemmas)
            cases = _prove_equal(premise, x, y, budget, deadline, cache)
            if cases is None:
                failed.add(key)
                continue
            lemmas.extend(Obligation(f"unify_{len(lemmas)}_case_{n}", q.sexpr(), "unsat", elapsed_seconds=t)
                          for n, (q, t) in enumerate(cases))
            # Replace the larger term by the smaller: the smaller cannot contain
            # it, so the rewrite terminates (w := f(w) would grow forever).
            small, big = sorted((x, y), key=_text_size)
            formula = substitute(formula, (big, small))
            merged = True
            break
        if not merged or (on_merge is not None and on_merge(formula, tuple(lemmas), small)):
            break
    return formula, tuple(lemmas)


def _constant_names(term):
    """Names of the 0-ary uninterpreted constants in `term` (binder bodies included)."""
    names, seen, work = set(), set(), [term]
    while work:
        t = work.pop()
        if t.get_id() in seen:
            continue
        seen.add(t.get_id())
        if is_quantifier(t):
            work.append(t.body())
        elif is_app(t):
            if t.num_args() == 0 and t.decl().kind() == Z3_OP_UNINTERPRETED:
                names.add(t.decl().name())
            work.extend(t.children())
    return names


def unify_identities(formulas, deadline=None):
    """(formulas', lemmas): same-declaration UF applications whose differing
    arguments are identities (x = y for every value of the leaves, no premise)
    merged into one term, in every formula.

    Both sides often build a host-call argument from the same values in
    different spellings (x86 byte-split sums Concat(s[63:8], s[7:0]' ) and
    R15 offset views against EVM words and offsets), so the argument pair is
    an identity that normalize_word_arith proves rewrite by rewrite, while the
    whole formula's normalisation (its guards decided by the path conditions)
    leaves the two spellings apart and every premise query on x ≠ y stays
    unknown (Aave Pool 8248 pair_0_1: DELEGATECALL gas / in-offset / in-size /
    memory, 4 pairs, 68s here; whole-formula normalisation 140s left the gas
    apart; _prove_equal 128s unknown for each).

    One normalisation over G = ∧_k (m_k ⇒ x_k = y_k), m_k fresh Booleans: it
    returns N ≡ G (each rewrite proved, the lemmas). If m_k does not occur in
    N, then x_k = y_k ≡ G[m_k := ⊤, m_j := ⊥] ≡ N[m_j := ⊥] ≡ G[all := ⊥] ≡ ⊤:
    a valid identity, so F ≡ F[big := small] for every formula F. A deadline
    only stops rewriting (N is still ≡ G; fewer markers vanish)."""
    pairs = {}
    for f in formulas:
        for apps in _uf_applications(f):
            for i, first in enumerate(apps):
                for other in apps[i + 1:]:
                    for x, y in zip(first.children(), other.children()):
                        if not x.eq(y):
                            pairs.setdefault((x.get_id(), y.get_id()), (x, y))
    if not pairs or (deadline is not None and monotonic() >= deadline):
        return list(formulas), ()
    started = monotonic()
    marks = [FreshConst(BoolSort(), "ident") for _ in pairs]
    joint, rewrites = normalize_word_arith(
        And(*(Implies(m, x == y) for m, (x, y) in zip(marks, pairs.values()))), deadline=deadline)
    live = _constant_names(joint)
    merges = [(x, y) for m, (x, y) in zip(marks, pairs.values()) if m.decl().name() not in live]
    if not merges:
        return list(formulas), ()
    lemma = Obligation(f"unify_identities_{len(merges)}", Not(And(*(x == y for x, y in merges))).sexpr(), "unsat",
                       elapsed_seconds=monotonic() - started, lemmas=rewrites)
    # Larger term := smaller, as unify_uf_arguments; the largest first, so a pair nested in
    # another is not rewritten inside it before the outer one matches (each swap is valid alone).
    swaps = sorted((tuple(sorted((x, y), key=lambda t: -_text_size(t))) for x, y in merges),
                   key=lambda s: -_text_size(s[0]))
    out = list(formulas)
    for big, small in swaps:
        out = [substitute(f, (big, small)) for f in out]
    return out, (lemma,)


# ponytail: fixed 3s probe before the rewrite routes; tune if easy queries start missing it.
_QUICK_EXACT_MS = 3000
# ponytail: fixed 300s cap for the last-resort direct query; raise it if a node fails only on these.
_LAST_RESORT_MS = 300_000
# A stuck prefix group pays for itself only if it replaces several member proofs.
_STUCK_MIN_MEMBERS = 3
# ponytail: fixed 10s cap for the LIA route (runs before the SAT routes on every hard pair); raise if LIA wins start timing out.
_LIA_MS = 10_000
# ponytail: two guard levels (<= 4 cases); PoolManager 16670 needs one, 4 guards (16 cases) cost 100-500s each.
_GUARD_MAX_DEPTH = 2
_PAIR_POOL = None
# Diagnostic: print each pair-phase obligation as it completes (main thread).
_TRACE_OBLIGATIONS = bool(__import__("os").environ.get("BLOCK_TRACE_OBLIGATIONS"))


def _pair_pool():
    """Process pool for independent pair obligations (env BLOCK_PAIR_WORKERS)."""
    global _PAIR_POOL
    if _PAIR_POOL is not None and getattr(_PAIR_POOL, "_broken", False):
        _reset_pair_pool()  # a worker died (OOM, external kill): never reuse a broken pool
    if _PAIR_POOL is None:
        import os
        workers = int(os.environ.get("BLOCK_PAIR_WORKERS", "1"))
        if workers <= 1:
            return None
        import multiprocessing
        from concurrent.futures import ProcessPoolExecutor
        _PAIR_POOL = ProcessPoolExecutor(workers, mp_context=multiprocessing.get_context("spawn"),
                                         initializer=_exit_with_parent, initargs=(os.getpid(),))
    return _PAIR_POOL


def _exit_with_parent(parent):
    # A killed runner (hard wall) must not leave workers solving for hours.
    import os
    import threading
    import time

    def watch():
        while os.getppid() == parent:
            time.sleep(2)
        os._exit(1)
    threading.Thread(target=watch, daemon=True).start()


def _reset_pair_pool():
    global _PAIR_POOL
    pool, _PAIR_POOL = _PAIR_POOL, None
    if pool is not None:
        for process in list(getattr(pool, "_processes", {}).values()):
            process.kill()  # SIGTERM mid-z3 segfaults during exit teardown
        pool.shutdown(wait=False, cancel_futures=True)


def _to_smt2(formula):
    if binder_capture_risk(formula):
        formula = canon_binders(formula)
        if binder_capture_risk(formula):
            raise ValueError("SMT2 round trip would capture a bound variable")
    solver = Solver()
    solver.add(formula)
    return solver.to_smt2()


_WORKER_PROVER = {}


def _check_serialized(smt2, name, timeout_ms, remaining_seconds, node):
    """Worker side of _check_all: the unchanged _check on the parsed formula.

    One prover per node and worker keeps what _check learns across sibling
    pairs (route order, multiplication UFs, lemma cache), as in the parent.
    """
    from z3 import parse_smt2_string
    formula = And(*parse_smt2_string(smt2))
    prover = _worker_prover(node, timeout_ms, remaining_seconds)
    records = []
    prover._check(name, formula, records)
    return records[-1]


def _worker_prover(node, timeout_ms, remaining_seconds):
    if _WORKER_PROVER.get("node") != node:
        from common.store_forwarding import clear_memo
        clear_memo()  # a new node: the previous node's memoized terms are dead weight
        _WORKER_PROVER.update(node=node, prover=BlockEquivalenceProver([], [], {}, timeout_ms=timeout_ms))
    prover = _WORKER_PROVER["prover"]
    prover.timeout_ms = timeout_ms
    prover.deadline = None if remaining_seconds is None else monotonic() + remaining_seconds
    return prover


class ProofBudgetExceeded(TimeoutError):
    """Abort this proof attempt; never turn expiry into a summary fallback."""


@dataclass(frozen=True)
class Obligation:
    name: str
    formula: str
    answer: str
    expected: str = "unsat"
    elapsed_seconds: float = 0.0
    # Refuted side conditions justifying the rewrite from the original
    # obligation to `formula` (see unify_uf_arguments); all must be UNSAT.
    lemmas: tuple = ()

    @property
    def proved(self):
        if self.answer != self.expected or not all(l.answer == "unsat" and l.proved for l in self.lemmas):
            return False
        # Goal-split parts (_check) are named *_goal_k_of_n: all n must be here.
        goals = {m.groups() for m in (_GOAL_NAME.search(l.name) for l in self.lemmas) if m}
        return not goals or len({n for _, n in goals}) == 1 and goals == {
            (str(k), n) for n in {n for _, n in goals} for k in range(int(n))}


def discharge_maps_by_prefix(premise, x86_conditions, jobs, timeout_ms, deadline=None, stuck=None):
    """{(j, k): Obligation} for the x86_maps_j_k refuted over a shared path prefix.

    jobs: [(c, [(j, k), ...])], c an EVM conjunct that x86 paths j must imply.
    x86 path conditions are And(constraints in execution order) (as_bool), so
    for the group's longest common prefix P, premise ∧ P ∧ ¬c is a weakening of
    every premise ∧ x_j ∧ ¬c: its UNSAT discharges the whole group with one
    query. SAT means P is too weak: split at the next differing constraint and
    go deeper. Unknown stops there; those (j, k) stay with the per-obligation
    routes (Safe 5377: 14489 maps from 175 conjuncts; descending on unknown
    spent 3000s of 3400s in 2s timeouts). Each unknown (query, entries) is
    appended to `stuck` if given: one full-route proof of it covers the group.
    """
    ordered = {j: list(c.children()) if is_and(c) else [c] for j, c in x86_conditions.items()}
    done = {}

    def lcp(js):
        first, n = ordered[js[0]], 0
        while all(len(ordered[j]) > n for j in js) and all(ordered[j][n].eq(first[n]) for j in js[1:]):
            n += 1
        return n

    def discharge(c, entries):
        js = sorted({j for j, _ in entries})
        size = lcp(js)
        started = monotonic()
        budget = timeout_ms if deadline is None else min(timeout_ms, int((deadline - started) * 1000))
        if budget <= 0:
            return
        query = And(premise, *ordered[js[0]][:size], Not(c))
        answer = solve_query(query, budget)
        if answer == "unsat":
            text, elapsed = query.sexpr(), monotonic() - started
            for j, k in entries:
                done[(j, k)] = Obligation(f"x86_maps_{j}_{k}", text, "unsat", elapsed_seconds=elapsed)
        elif answer == "sat":
            groups = {}
            for j, k in entries:
                if len(ordered[j]) > size:  # else the query was x_j itself: a real counterexample
                    groups.setdefault(ordered[j][size].get_id(), []).append((j, k))
            for group in groups.values():
                discharge(c, group)
        elif stuck is not None:
            stuck.append((query, entries))

    for c, entries in sorted(jobs, key=lambda job: -len(job[1])):  # widest groups first
        discharge(c, entries)
    return done


def _ordered_conjuncts(condition):
    """Top-level conjuncts of a path condition in execution order (as_bool)."""
    return list(condition.children()) if is_and(condition) else [condition]


def disjoint_groups(premise, conditions):
    """[(pairs, formula)]: every (i, k), i < k, in exactly one group.

    Path conditions are And(conjuncts in execution order). If those of i and
    k first differ at position L, with edges a and b, then
    premise ∧ prefix_L ∧ a ∧ b is a sub-conjunction of premise ∧ e_i ∧ e_k,
    so its UNSAT refutes the pair, and every pair diverging at the same
    (prefix, a, b) shares it (Safe 5377: 3655 pairs, 322 groups). Executor
    paths diverge at the two edges of one branch; complementary ones
    (x and Not(x), or simplify(a ∧ b) false) need only a ∧ b. A pair where
    one condition is a prefix of the other keeps its own full query. A group
    may fail where its pairs hold (edges that exclude each other only with
    later conjuncts): the caller then checks those pairs' full queries.
    """
    paths = [_ordered_conjuncts(c) for c in conditions]
    out, shared = [], {}
    for i in range(len(paths)):
        for k in range(i + 1, len(paths)):
            a, b, size = paths[i], paths[k], 0
            while size < min(len(a), len(b)) and a[size].eq(b[size]):
                size += 1
            if size == len(a) or size == len(b):
                out.append(([(i, k)], And(premise, conditions[i], conditions[k])))
                continue
            key = (tuple(c.get_id() for c in a[:size]), a[size].get_id(), b[size].get_id())
            if key not in shared:
                x, y = a[size], b[size]
                complementary = ((is_not(x) and x.arg(0).eq(y)) or (is_not(y) and y.arg(0).eq(x))
                                 or is_false(simplify(And(x, y))))
                shared[key] = ([], And(x, y) if complementary else And(premise, *a[:size], x, y))
                out.append(shared[key])
            shared[key][0].append((i, k))
    return out


def propose_from_siblings(correspondence, x86):
    """Replace "all" by the EVM index every mapped sibling (same kind and
    location) agrees on. Only a proposal: if any of its obligations fails,
    _pair_phase degrades that row alone back to "all" (or None)."""
    agreed = {}
    for s, x in zip(correspondence, x86):
        if type(s) is int:
            agreed.setdefault((x.kind, x.location), set()).add(s)
    out = []
    for s, x in zip(correspondence, x86):
        choice = agreed.get((x.kind, x.location), set())
        out.append(next(iter(choice)) if s == "all" and len(choice) == 1 else s)
    return out


def map_arity(evm, correspondence):
    """Conjunct count of each mapped EVM path condition, from the outcomes
    themselves (never from the prover): x86_maps_j is split per conjunct."""
    return tuple(len(_conjuncts(evm[s].condition)) if type(s) is int else 0 for s in correspondence)


def pair_obligation_names(evm_count, x86_count, correspondence=(), arity=()):
    """Pair-phase obligations: the full product, or the path correspondence.

    correspondence[j] is the EVM index mapped to x86 path j, None if that x86
    path is empty under the premise, or "all" for a full row. A mapping to s
    needs x86_maps_j_k (x_j implies conjunct k of e_s) for every k < arity[j],
    pair_s_j, and pairwise disjoint EVM paths (see BlockTheorem.complete).
    """
    if not correspondence:
        return [f"pair_{i}_{j}" for i in range(evm_count) for j in range(x86_count)]
    names = []
    if any(type(s) is int for s in correspondence):
        names += [f"evm_disjoint_{i}_{k}" for i in range(evm_count) for k in range(i + 1, evm_count)]
    for j, s in enumerate(correspondence):
        if s is None:
            names.append(f"x86_empty_{j}")
        elif s == "all":
            names += [f"pair_{i}_{j}" for i in range(evm_count)]
        else:
            names += [f"x86_maps_{j}_{k}" for k in range(arity[j])] + [f"pair_{s}_{j}"]
    return names


def obligation_manifest(evm, x86, initial, *, block=True, correspondence=()):
    """Expected obligations derived from outcomes, never from query records."""
    names = ["entry_nonempty", "havoc_relation", "model_domain_nonempty"] if block else [
        "init_nonempty", "model_domain_nonempty"]
    allowed = {a.get_id() for a in initial.assumptions or []}
    for label, paths in (("evm", evm), ("x86", x86)):
        justified = set(allowed)
        for path in paths:
            for assumption in path.state.assumptions or []:
                if assumption.get_id() not in justified:
                    names.append(f"{label}_assumption_{len(justified)}")
                    justified.add(assumption.get_id())
        names.append(f"{label}_coverage")
    names.extend(pair_obligation_names(len(evm), len(x86), correspondence, map_arity(evm, correspondence)))
    return tuple(names)


@dataclass(frozen=True)
class BlockTheorem:
    identity: str
    spec: BlockSpecialization
    obligations: Tuple[Obligation, ...]
    required: Tuple[str, ...]
    outcome_digest: str
    evm_count: int
    x86_count: int
    finite_execution: bool
    summary_hits: tuple = ()
    summary_hit_count: int = 0
    correspondence: tuple = ()
    arity: tuple = ()

    def _pairs_covered(self, names):
        """Every (i, j) pair is discharged, directly or via the correspondence:
        for i != s = correspondence[j], premise ∧ e_i ∧ x_j implies e_i ∧ e_s
        (x86_maps_j), which evm_disjoint_{i,s} refutes; x86_empty_j refutes x_j."""
        n, m, corr = self.evm_count, self.x86_count, self.correspondence
        if not corr:
            return all(f"pair_{i}_{j}" in names for i in range(n) for j in range(m))
        if len(corr) != m:
            return False
        if any(type(s) is int for s in corr) and not all(
                f"evm_disjoint_{i}_{k}" in names for i in range(n) for k in range(i + 1, n)):
            return False
        for j, s in enumerate(corr):
            if s is None:
                ok = f"x86_empty_{j}" in names
            elif s == "all":
                ok = all(f"pair_{i}_{j}" in names for i in range(n))
            elif type(s) is int and 0 <= s < n and len(self.arity) == m and self.arity[j] >= 1:
                # names == required pins arity to the outcomes (map_arity).
                ok = (all(f"x86_maps_{j}_{k}" in names for k in range(self.arity[j]))
                      and f"pair_{s}_{j}" in names)
            else:
                ok = False
            if not ok:
                return False
        return True

    @property
    def complete(self):
        names = tuple(o.name for o in self.obligations)
        name_set = set(names)
        return (self.finite_execution and self.evm_count > 0 and self.x86_count > 0
                and len(set(names)) == len(names) and names == self.required
                and {"entry_nonempty", "model_domain_nonempty", "havoc_relation", "evm_coverage", "x86_coverage"} <= name_set
                and self._pairs_covered(name_set)
                and all(o.proved for o in self.obligations)
                and len(self.summary_hits) == self.summary_hit_count
                and all(c.complete for c in self.summary_hits))


def state_digest(state, expression_cache=None):
    """Run-local identity; includes every field, expression and model option."""
    expressions = {} if expression_cache is None else expression_cache
    def encode(obj):
        if isinstance(obj, Enum):
            return (type(obj).__qualname__, obj.value)
        if hasattr(obj, "sexpr"):
            key = (id(obj.ctx), obj.get_id())
            if key not in expressions:
                expressions[key] = obj.sexpr()
            return expressions[key]
        if isinstance(obj, dict):
            return tuple(sorted((str(k), encode(v)) for k, v in obj.items()))
        if isinstance(obj, (list, tuple)):
            return tuple(encode(v) for v in obj)
        if hasattr(obj, "__dict__"):
            return (type(obj).__qualname__, encode(vars(obj)))
        slots = getattr(type(obj), "__slots__", ())
        if slots:
            return tuple((k, encode(getattr(obj, k))) for k in slots)
        return repr(obj)
    return digest(encode(state))


def paths_digest(evm, x86):
    # Z3 terms are immutable; reuse rendering only during this fresh traversal.
    expressions = {}
    return digest(tuple((p.kind, p.location, p.condition.sexpr(), state_digest(p.state, expressions))
                        for p in (*evm, *x86)))


@dataclass
class BlockProofResult:
    spec: BlockSpecialization
    status: str = "inconclusive"
    reasons: Tuple[str, ...] = ()
    queries: int = 0
    evm_paths: int = 0
    x86_paths: int = 0
    paired_transitions: int = 0
    terminals_proved: int = 0
    control_flow_defects: Tuple[str, ...] = ()
    theorem: BlockTheorem | None = None
    obligations: tuple[Obligation, ...] = ()
    # Execution products are used only inside this run and rehashed on consume.
    evm_outcomes: tuple = field(default=(), repr=False)
    x86_outcomes: tuple = field(default=(), repr=False)
    context: object = field(default=None, repr=False)
    premise: object = field(default=None, repr=False)
    elapsed_seconds: float = 0.0
    # keep_going only (diagnostics): every pair-phase failure that did not stop the node.
    kept_failures: tuple = ()
    _issuer: object = field(default=None, repr=False)

    def _proved_for_identity(self, current_identity):
        """Batch consumer supplies one freshly checked program identity."""
        try:
            t = self.theorem
            return (self.status == "proved" and not self.reasons and not self.control_flow_defects
                    and t is not None and t.complete and t.spec == self.spec
                    and self._issuer is not None and t.identity == current_identity
                    and any(t is issued for issued in self._issuer._issued_theorems)
                    and t.outcome_digest == paths_digest(self.evm_outcomes, self.x86_outcomes))
        except Exception:
            return False

    @property
    def proved(self):
        try:
            return self._proved_for_identity(self._issuer.identity)
        except Exception:
            return False

    @classmethod
    def inconclusive(cls, spec, reason, **kw):
        return cls(spec=spec, reasons=(reason,), **kw)


class BlockEquivalenceProver:
    def __init__(self, evm_blocks, x86_blocks, pc_to_addr, schema=None, *,
                 timeout_ms=30_000, max_depth=400, aot_profile=None,
                 compare_gas=True, host_gas_uf_enabled=True, summary_config=None,
                 deadline=None, max_path_pairs=100_000, node_timeout_seconds=None, keep_going=False):
        self.evm_blocks = list(evm_blocks)
        self.x86_blocks = list(x86_blocks)
        self.pc_to_addr = dict(pc_to_addr)
        self.schema = schema or BlockRelationSchema()
        self.timeout_ms = timeout_ms
        self.max_depth = max_depth
        self.aot_profile = aot_profile or GO_HPC_EVM_PROFILE
        self.compare_gas = compare_gas
        self.host_gas_uf_enabled = host_gas_uf_enabled
        self.summary_config = summary_config
        self.deadline = deadline
        # Shared across obligations (each query is independent, so one set of
        # multiplication UFs and proved equalities stays sound) so that the
        # same terms keep the same ids and _prove_equal's cache hits.
        self._mul_functions, self._lemma_cache = {}, {}
        self._node_needed_unification = False
        self._route_stats = {}  # _route_class -> {route: (wins, seconds)}, see _winners_first
        self._potential_pending = None  # (input, target, lemmas): a capped potential solve that ran out
        self.node_timeout_seconds = node_timeout_seconds
        self.max_path_pairs = max_path_pairs
        # Diagnostics only (tools/probe_block_obligations --keep-going): a failing
        # pair-phase obligation is recorded in _kept_failures and the remaining rows
        # are still checked; prove() then fails the node. Production never sets it.
        self.keep_going = keep_going
        self._kept_failures = []
        self._issued_theorems = []
        self._summary_templates = None
        self.call_site_mapping = None
        # Keep references alive: these identities are run-local, never persisted.
        self._model_functions = (run_evm_segment, run_x86_segment, terminal_observable_conditions,
                                 type(self.schema).relation_goals, type(self.schema).build_havoc)

    @property
    def portable_identity(self):
        """`identity` without the run-local function ids: equal in every
        process that loads the same program, model sources and options (the
        discover-first parallel schedule compares its workers by it)."""
        return digest((tuple(b.to_json() for b in self.evm_blocks),
                       tuple((b.start_addr, b.end_addr, tuple(
                           (i.addr, i.size, bytes(i.bytes), i.mnemonic, i.op_str)
                           for i in b.instructions)) for b in self.x86_blocks),
                       sorted(self.pc_to_addr.items()), self.schema.fingerprint,
                       repr(self.aot_profile), self.compare_gas, self.host_gas_uf_enabled,
                       sorted(HOST_GAS_UPPER_BOUNDS.items()),
                       _SEMANTIC_SOURCES,
                       repr(self.summary_config), repr(self.call_site_mapping),
                       "checked-summaries:no-nooverflow:pre-tag:v1"))

    @property
    def identity(self):
        return digest((self.portable_identity,
                       tuple(id(f) for f in (run_evm_segment, run_x86_segment, terminal_observable_conditions,
                                             type(self.schema).relation_goals, type(self.schema).build_havoc))))

    def validate(self):
        if not isinstance(self.schema, BlockRelationSchema):
            raise ValueError("block proof requires the pre-TAG BlockRelationSchema")
        if self.aot_profile != GO_HPC_EVM_PROFILE:
            raise ValueError("unsupported ABI profile for block relation")
        if len(set(self.pc_to_addr.values())) != len(self.pc_to_addr):
            raise ValueError("mapping is not one-to-one")
        if len({b.pc for b in self.evm_blocks}) != len(self.evm_blocks):
            raise ValueError("duplicate EVM block PC")
        if set(self.pc_to_addr) != {b.pc for b in self.evm_blocks}:
            raise ValueError("mapping must contain every EVM block; analysis cannot erase blocks")
        starts = {b.start_addr for b in self.x86_blocks}
        if len(starts) != len(self.x86_blocks):
            raise ValueError("duplicate x86 block address")
        if not set(self.pc_to_addr.values()) <= starts:
            raise ValueError("TAG is not a split instruction/block boundary")
        if self.node_timeout_seconds is not None and self.node_timeout_seconds <= 0:
            raise ValueError("node timeout must be positive")
        if self.max_depth <= 0 or self.timeout_ms <= 0:
            raise ValueError("proof budgets must be positive")
        if self.call_site_mapping is None:
            from verification.call_site_mapping import build_call_site_mapping_from_blocks
            self.call_site_mapping = build_call_site_mapping_from_blocks(
                self.evm_blocks, self.x86_blocks, aot_profile=self.aot_profile)

    def _check(self, name, formula, records, *, expected="unsat", split=True):
        started = monotonic()
        timeout = self.timeout_ms
        if self.deadline is not None:
            timeout = min(timeout, int((self.deadline - started) * 1000))
            if timeout <= 0:
                raise ProofBudgetExceeded("proof wall budget exhausted")
        if not is_bool(formula):
            raise ValueError(f"{name}: missing/non-Boolean proof predicate")
        proved, answer, lemmas, witnesses = formula, "unknown", (), ()
        if expected == "unsat":
            # Equisatisfiable (see skolemize_array_disequalities): every route
            # below refutes the witness form; its lemma joins any proof.
            formula, witnesses = skolemize_array_disequalities(formula)
            proved = formula
            # Cheap exact attempt first: most obligations are easy, and the
            # rewrite routes below cost seconds even when they find nothing.
            answer = solve_query(simplify(formula), min(timeout, _QUICK_EXACT_MS))
        parts = _goal_split(formula) if split and expected == "unsat" and answer == "unknown" else None
        if parts is not None:
            # A terminal pair's goal conjunction, one observable at a time:
            # each part is refuted by the full routing below (split=False),
            # and the record is proved only with all n parts (Obligation.proved).
            sub = []
            for k, part in enumerate(parts):
                if not self._check(f"{name}_goal_{k}_of_{len(parts)}", part, sub, split=False):
                    break
            answer = "unsat" if len(sub) == len(parts) and all(r.proved for r in sub) else sub[-1].answer
            record = Obligation(name, proved.sexpr(), answer, expected, monotonic() - started, witnesses + tuple(sub))
            records.append(record)
            return record.proved
        pinned = ()
        if expected == "unsat" and answer == "unknown":
            # Pinned memory words first (pin_split): its cases are concrete and
            # quick; every route below then works on the residual, and the case
            # proofs join whatever proves it (CErc20 12342 pair_29_1: ~12s, where
            # every route on F was unknown or 60s+). A SAT case is a model of F.
            split = pin_split(formula, self.timeout_ms, self.deadline)
            if split == "sat":
                answer = "sat"
            elif split is not None:
                formula, pinned = split
                proved = formula
                left = timeout if self.deadline is None else int((self.deadline - monotonic()) * 1000)
                answer = solve_query(simplify(formula), min(left, _QUICK_EXACT_MS)) if left > 0 else "unknown"
        if expected == "unsat" and answer == "unknown":
            # Same routes either way; once a sibling pair needed unification
            # it goes first, sparing the abstraction attempt that rarely yields.
            # "norm" routes run on normalize_word_arith(F), an equivalent formula
            # (each rewrite proved; the proofs join the lemmas). They come after
            # the plain route that usually wins, since normalising can also make
            # the unification route's case tree slower.
            # Normalised unification before plain: on CErc20 4236 / Safe 588 it
            # won in 40-100s where the plain case tree ran out any budget.
            # "exact" solves the normalised formula directly: once memory views
            # agree syntactically (CErc20 12930) that alone refutes it in ~20s.
            # "alias" first: it gives up at once unless two address bases alias,
            # and then its cases are tiny (CErc20 12930: 65 queries, ~1s).
            # "bvabs" (refute_over_bv_abstraction) answers "unknown" at once when
            # the refutation needs array semantics, so it costs nothing there.
            # Normalised "bvabs" right after normalising: once both sides' word
            # counts and memory views agree syntactically, generalising the arrays
            # gives the host-call arguments one constant, so UF congruence is
            # syntactic (Safe 2493 / CErc20 4236 host-call pairs: <1s, where the
            # plain bvabs times out or is abstract-SAT and "exact" stalls on the
            # store chains). One per-query budget only: it wins fast or not at all.
            # "potential" (telescoped memory charges, _retry_over_potential) next:
            # it returns at once unless memory-cost sums are present.
            # "lia" (_retry_over_lia, own caps, no share) first: the LIA reading of
            # product limbs, before the SAT routes.
            routes = ([("lia", False), ("quick", True), ("shift", False), ("blast", True), ("alias", True), ("potential", True), ("bvabs", True), ("bvabs", False), ("exact", True),
                       ("mul", False), ("mul", True), ("guards", False), ("unify", True), ("unify", False)]
                      if not self._node_needed_unification else
                      [("lia", False), ("quick", True), ("shift", False), ("blast", True), ("alias", True), ("potential", True), ("bvabs", True), ("bvabs", False), ("guards", False),
                       ("unify", True), ("exact", True), ("unify", False), ("mul", True), ("mul", False)])
            # Routes that refuted this class of obligation before go first (_winners_first);
            # with no history the table above is unchanged.
            stats = self._route_stats.setdefault(_route_class(name), {})
            promoted = 0
            if not _ROUTE_ORDER_STATIC:
                routes = _winners_first(routes, stats)
                promoted = sum(1 for r in routes if stats.get(r, (0, 0.0))[0])
            normalized = None
            node_deadline = self.deadline
            pending, self._potential_pending = None, None
            for index, (route, norm) in enumerate(routes):
                target, rewrites = formula, ()
                if norm:
                    if normalized is None:
                        normalized = normalize_word_arith(formula, deadline=self.deadline)
                    target, rewrites = normalized
                    if target.eq(simplify(formula, bv_sort_ac=True)) and route not in ("alias", "potential", "blast"):
                        continue  # nothing rewritten: the plain route covers it
                # Each route gets an equal share of what is left (the direct
                # query below keeps one share), so no route starves the rest.
                # A promoted route (it refuted this class before) gets half: it is
                # expected to need what it needed there (Safe 5377 unify: 190-320s).
                if node_deadline is not None and route != "lia":
                    shares = 1 if index < promoted else sum(1 for r, _ in routes[index:] if r != "lia")
                    self.deadline = monotonic() + (node_deadline - monotonic()) / (shares + 1)
                route_started = monotonic()
                try:
                    if route == "lia":
                        proved, answer, lemmas = self._retry_over_lia(target)
                    elif route == "quick":
                        # Quick exact on F' first: once guards are decided both sides often
                        # agree syntactically (CErc20 10233 x86_maps_1_19: 0.5s; potential 127s).
                        budget = min(_QUICK_EXACT_MS, int((self.deadline - monotonic()) * 1000)
                                     if self.deadline is not None else _QUICK_EXACT_MS)
                        answer = solve_query(target, budget) if budget > 0 else "unknown"
                        proved, lemmas = target, ()
                    elif route == "exact":
                        budget = min(2 * self.timeout_ms, int((self.deadline - monotonic()) * 1000)
                                     if self.deadline is not None else 2 * self.timeout_ms)
                        answer = solve_query(target, budget) if budget > 0 else "unknown"
                        proved, lemmas = target, ()
                    elif route == "bvabs":
                        # ponytail: 4x the per-query budget (Safe 4524 pair_24_2 needs ~45s); the share still bounds it.
                        cap = self.timeout_ms if norm else 4 * self.timeout_ms
                        budget = min(cap, int((self.deadline - monotonic()) * 1000)
                                     if self.deadline is not None else cap)
                        proved, answer = refute_over_bv_abstraction(target, budget)
                        answer, lemmas = ("unsat" if answer == "unsat" else "unknown"), ()  # abstract SAT proves nothing
                    elif route == "alias":
                        # Half of what is left, not one share: when the split applies, its
                        # fallback already runs unify/mul on every case, and the routes
                        # below face the unsplit aliasing (CErc20 12930 pair_27_0: its
                        # residual needs ~500s; the 1/8 share gave 283s, then the other
                        # routes spent 1600s for nothing). No split: returns at once.
                        if node_deadline is not None:
                            self.deadline = monotonic() + (node_deadline - monotonic()) / 2
                        cases = _alias_split(target, self.timeout_ms, self.deadline, self._refute_further,
                                             parallel=True)
                        proved, answer, lemmas = (target, "unsat", cases) if cases else (formula, "unknown", ())
                    elif route == "potential":
                        # ponytail: 1/3 of what is left when it applies (CErc20 4571 needs ~95s); not applicable: returns at once.
                        if node_deadline is not None:
                            self.deadline = monotonic() + (node_deadline - monotonic()) / 3
                        proved, answer, lemmas = self._retry_over_potential(target)
                    elif route == "blast":
                        # Reads through x86 store chains (symbolic addresses over the R15
                        # offset view) blasted into ites, as EVM memory already is when
                        # built: CErc20 4571 pair 600s unknown -> 0.1-3.9s. Exact for one
                        # per-query budget, then potential on the blasted form when memory
                        # charges remain (CErc20 10727 x86_maps 14.8s, 10233 48.6s).
                        target = simplify(target, blast_select_store=True)
                        budget = min(self.timeout_ms, int((self.deadline - monotonic()) * 1000)
                                     if self.deadline is not None else self.timeout_ms)
                        answer = solve_query(target, budget) if budget > 0 else "unknown"
                        proved, lemmas = target, ()
                        if answer != "unsat":
                            if node_deadline is not None:
                                self.deadline = monotonic() + (node_deadline - monotonic()) / 3
                            proved, answer, lemmas = self._retry_over_potential(target)
                    elif route == "shift":
                        # Half of what is left when it applies (Permit2 4837 x86_maps_12_0: 63
                        # cases, 6s; a case can need ~2s when the amount is not fully fixed); no
                        # symbolic shift amount with few values: returns at once. A SAT case is a
                        # model of F (shift_split).
                        if node_deadline is not None:
                            self.deadline = monotonic() + (node_deadline - monotonic()) / 2
                        cases = shift_split(target, self.timeout_ms, self.deadline)
                        proved, answer, lemmas = ((target, "sat", ()) if cases == "sat" else
                                                  (target, "unsat", cases) if cases is not None else
                                                  (formula, "unknown", ()))
                    elif route == "mul":
                        proved, answer, lemmas = self._retry_over_nonlinear_mul(target, "unknown", split=norm)
                    elif route == "guards":
                        proved, answer, lemmas = self._retry_over_guard_cases(target)
                    else:
                        proved, answer, lemmas = self._retry_with_uf_unification(target, "unknown")
                        self._node_needed_unification |= answer == "unsat"
                except ProofBudgetExceeded:
                    if node_deadline is None or monotonic() >= node_deadline:
                        raise
                    proved, answer, lemmas = formula, "unknown", ()
                finally:
                    self.deadline = node_deadline
                wins, seconds = stats.get((route, norm), (0, 0.0))
                stats[(route, norm)] = (wins + (answer == "unsat"), seconds + monotonic() - route_started)
                ours = self._potential_pending
                if pending is None and ours is not None and ours[0].eq(target):
                    pending = (ours[1], ours[2], rewrites)
                if answer == "unsat":
                    lemmas = rewrites + lemmas
                    break
                if route == "shift" and answer == "sat":
                    break  # a model of F: no route can refute it (other routes' "sat" may be abstract)
            if answer != "unsat" and pending is not None and node_deadline is not None:
                # Every route failed: resume the capped potential solve with what they left,
                # keeping one per-query share for the direct query below.
                budget = int((node_deadline - monotonic()) * 1000) - self.timeout_ms
                if budget > 4 * self.timeout_ms and solve_query(pending[0], budget) == "unsat":
                    proved, answer, lemmas = pending[0], "unsat", pending[2] + pending[1]
            if answer != "unsat":
                proved, lemmas = formula, ()
        if expected == "sat" and answer == "unknown":
            # UFs over lambda arrays (sha3_slice in host-gas oracle arguments)
            # leave every direct query unknown; a checked constant-function
            # witness proves satisfiability (sat_by_constant_array_ufs). Up to three
            # tiers share the budget, so each keeps the quick budget one tier had.
            answer = sat_by_constant_array_ufs(formula, min(timeout, 3 * _QUICK_EXACT_MS))
        if answer not in ("unsat", "sat"):
            if self.deadline is not None:
                timeout = min(timeout, int((self.deadline - monotonic()) * 1000))
                if timeout <= 0:
                    raise ProofBudgetExceeded("proof wall budget exhausted")
            query = simplify(formula)
            answer = (solve_query(query, timeout, trust_unknown=False) if expected == "sat"
                      else solve_query(query, timeout))
        record = Obligation(name, proved.sexpr(), answer, expected, monotonic() - started,
                            witnesses + pinned + lemmas)
        records.append(record)
        return record.proved

    def _refute_further(self, query):
        """(refuted formula, lemmas) from the unification / split abstraction
        routes, or None; for an alias case whose direct query is unknown."""
        for attempt in (lambda: self._retry_with_uf_unification(query, "unknown"),
                        lambda: self._retry_over_nonlinear_mul(query, "unknown", split=True)):
            proved, answer, lemmas = attempt()
            if answer == "unsat":
                return proved, lemmas
        return None

    def _proved_trials(self, obligations, until):
        """{name: record} of the obligations `_check` proves before `until`.
        Failed and unfinished ones are dropped: a trial proves nothing else."""
        trial, proved, deadline = [], {}, self.deadline
        self.deadline = until if deadline is None else min(deadline, until)
        checks = self._check_all(obligations, trial)
        try:
            for ok in checks:
                if ok:
                    proved[trial[-1].name] = trial[-1]
        except ProofBudgetExceeded:
            pass
        finally:
            checks.close()
            self.deadline = deadline
        return proved

    def _prove_stuck_groups(self, stuck, done, until, per_group):
        """Full routes once per prefix group discharge_maps_by_prefix left
        unknown. The group query weakens each member's x86_maps query, so its
        proved record, renamed, proves each member; anything else proves
        nothing and leaves the members to their own routes. Widest groups
        first, one pool-width at a time, each capped at `per_group` seconds;
        the phase stops at `until`."""
        stuck = sorted(stuck, key=lambda group: -len(group[1]))
        pool = _pair_pool()
        width = getattr(pool, "_max_workers", 1) if pool is not None else 1
        for first in range(0, len(stuck), width):
            now = monotonic()
            if now >= until:
                break
            chunk = list(enumerate(stuck[first:first + width], first))
            proved = self._proved_trials([(f"x86_maps_group_{n}", q, "") for n, (q, _) in chunk],
                                         min(until, now + per_group))
            for n, (_, entries) in chunk:
                if f"x86_maps_group_{n}" in proved:
                    record = proved[f"x86_maps_group_{n}"]
                    done.update({(j, k): replace(record, name=f"x86_maps_{j}_{k}") for j, k in entries})

    def _discharge_all_rows(self, premise, evm, x86, rows, until):
        """{(i, j): record} proving pair_i_j of the "all" rows j, one proof
        per shared x86 path prefix.

        pair_i_j is premise ∧ e_i ∧ x_j (∧ ¬goal) and x_j is And(constraints
        in execution order), so premise ∧ e_i ∧ P for a prefix P of x_j is a
        weakening: its UNSAT proves the pair of every row sharing P (Safe
        2493: two rows share 130 of 134 constraints, differing only in the
        STATICCALL outcome; Safe 5377 has 36 such rows). Per EVM path the
        rows' common prefix gets a quick query: UNSAT proves the group, SAT
        splits it at the next differing constraint, unknown sends a group of
        two or more rows to the full routes in the pool. Anything unproved is
        left to its own pair.
        """
        ordered = {j: list(x86[j].condition.children()) if is_and(x86[j].condition) else [x86[j].condition]
                   for j in rows}
        quick = min(_QUICK_EXACT_MS, self.timeout_ms)
        done, hard = {}, []

        def lcp(js):
            first, n = ordered[js[0]], 0
            while all(len(ordered[j]) > n for j in js) and all(ordered[j][n].eq(first[n]) for j in js[1:]):
                n += 1
            return n

        def query(i, js, size):
            return And(premise, evm[i].condition, *ordered[js[0]][:size])

        def answer(q):
            left = int((until - monotonic()) * 1000)
            return solve_query(q, min(quick, left)) if left > 0 else None

        for i in range(len(evm)):
            stack = [tuple(rows)]
            while stack:
                js = stack.pop()
                size = lcp(js)
                started = monotonic()
                q = query(i, js, size)
                result = answer(q)
                if result is None:
                    stack = []
                    break
                if result == "unsat":
                    text = q.sexpr()
                    done.update({(i, j): Obligation(f"pair_{i}_{j}", text, "unsat",
                                                    elapsed_seconds=monotonic() - started) for j in js})
                elif result == "sat":
                    groups = {}
                    for j in js:
                        if len(ordered[j]) > size:  # else the query was the whole joint: a real pair
                            groups.setdefault(ordered[j][size].get_id(), []).append(j)
                    stack.extend(tuple(g) for g in groups.values())
                elif len(js) > 1:
                    # One full-route proof of the common prefix for the whole group. A shorter
                    # prefix is not easier in general (Safe 2493: bisected prefixes went unknown
                    # in 314-462s where the full pairs proved in 207-321s); a single row gains
                    # nothing over its own pair.
                    hard.append((i, js, size))
            if monotonic() >= until:
                break
        # One pool width at a time, each group capped at two query timeouts: groups that
        # end SAT/unknown burned 400-900s per node uncapped (Safe 2405, CErc20 10727/12930),
        # the provable ones finish in 14-69s. A capped trial only proves less.
        pool = _pair_pool()
        width = getattr(pool, "_max_workers", 1) if pool is not None else 1
        for first in range(0, len(hard), width):
            now = monotonic()
            if now >= until:
                break
            chunk = list(enumerate(hard[first:first + width], first))
            proved = self._proved_trials([(f"pair_group_{n}", query(i, js, size), "") for n, (i, js, size) in chunk],
                                         min(until, now + 2 * self.timeout_ms / 1000))
            for n, (i, js, _) in chunk:
                if f"pair_group_{n}" in proved:
                    done.update({(i, j): replace(proved[f"pair_group_{n}"], name=f"pair_{i}_{j}") for j in js})
        return done

    def _unify_node(self, pairs, skip=frozenset()):
        """Share host-call argument proofs across sibling pairs (unify_across).

        Runs over the multiplication abstraction (shared UFs) so squared word
        counts unify too, then reads the UFs as bvmul again: every lemma was
        refuted with UF applications opaque, so it holds for bvmul as well
        (see concretize_mul) and each rewritten pair stays exact.
        """
        # Only pair_* carry host-call arguments; x86_maps/x86_empty are path
        # implications and keep their own unify route in _check (Safe 5377:
        # 14489 maps made this 2338s before any obligation ran).
        hosts = [n for n, (name, f, _) in enumerate(pairs)
                 if name.startswith("pair_") and name not in skip and _uf_applications(f)]
        if not hosts:
            return pairs, (), set()
        # Valid argument identities first (unify_identities): no premise, so every sibling is
        # rewritten by one normalisation. ponytail: capped at 4 query timeouts.
        cap = monotonic() + 4 * self.timeout_ms / 1000
        concrete, identities = unify_identities([pairs[n][1] for n in hosts],
                                                cap if self.deadline is None else min(cap, self.deadline))
        functions = self._mul_functions
        abstract = [abstract_nonlinear_mul(f, functions=functions)[0] for f in concrete]
        # ponytail: 1/4 of what is left. Uncapped, PoolManager 16670 (83 host-call pairs) spent
        # over 50 of its 90 minutes here before checking any obligation; an unmerged pair only
        # goes to its own routes (its unify route included), so the cap costs no proof.
        until = None if self.deadline is None else monotonic() + (self.deadline - monotonic()) / 4
        unified, lemmas = unify_across(abstract, self.timeout_ms, until, cache=self._lemma_cache)
        if not lemmas and not identities:
            return pairs, (), set()
        out, rewritten = list(pairs), set()
        for n, c, a, u in zip(hosts, concrete, abstract, unified):
            if not u.eq(a) or not c.eq(pairs[n][1]):
                name, _, where = pairs[n]
                out[n] = (name, concretize_mul(u, functions) if not u.eq(a) else c, where)
                rewritten.add(name)
        return out, identities + lemmas, rewritten

    def _correspondence(self, evm, x86, premise, records):
        """Map each x86 path to its EVM path instead of pairing every (i, j).

        Returns () for the full product (small nodes, or any EVM overlap), else
        one entry per x86 path: an EVM index, None (x86 path empty) or "all".
        A mapping is only a proposal read off one model: a wrong guess makes
        its x86_maps obligation fail, never a proof. Disjointness is proved
        here, before the mapping is used; see BlockTheorem._pairs_covered.
        """
        n, m = len(evm), len(x86)
        if n < 2 or n * m <= n * (n - 1) // 2 + 2 * m:
            return ()
        def full(i, k):
            return And(premise, evm[i].condition, evm[k].condition)
        # One proof per divergence group (disjoint_groups), recorded under
        # every pair name it covers. A group refuted only with more of the
        # path (edges that do not exclude each other on their own) falls back
        # to its pairs' full queries; any failure there is an overlap.
        groups, proofs, trial = disjoint_groups(premise, [e.condition for e in evm]), {}, []
        checks = self._check_all([("evm_disjoint_%d_%d" % pairs[0], formula, "") for pairs, formula in groups], trial)
        try:
            for (pairs, formula), proved in zip(groups, checks):
                if proved:
                    proofs.update((f"evm_disjoint_{i}_{k}", replace(trial[-1], name=f"evm_disjoint_{i}_{k}"))
                                  for i, k in pairs)
                    continue
                if len(pairs) == 1 and formula.eq(full(*pairs[0])):
                    return ()
                sub = []
                inner = self._check_all([(f"evm_disjoint_{i}_{k}", full(i, k), "") for i, k in pairs], sub)
                try:
                    if not all(inner):
                        return ()
                finally:
                    inner.close()
                proofs.update((r.name, r) for r in sub)
        finally:
            checks.close()
        records.extend(proofs[f"evm_disjoint_{i}_{k}"] for i in range(n) for k in range(i + 1, n))  # manifest order
        correspondence, unknown = [], []
        # Mapping proposals. First the executor's last model of the path, if it
        # still satisfies premise ∧ x_j (170 of 171 rows on Safe 5377); else one
        # incremental solver over [premise, conjuncts of x_j]: rows share long
        # prefixes (Safe 5377: 300s, 44 unknown -> 62s, 2 unknown, every decided
        # row the same). Either way only a proposal (see above).
        logic = _bv_array_formula(And(premise, *(x.condition for x in x86)))
        prefix = PrefixSolver(SolverFor("QF_AUFBV") if logic else Solver())
        for j, x in enumerate(x86):
            witness = getattr(x, "witness", None)
            if witness is not None and is_true(witness.eval(And(premise, x.condition), model_completion=True)):
                hits = [i for i, e in enumerate(evm)
                        if is_true(witness.eval(e.condition, model_completion=True))]
                if len(hits) == 1:
                    correspondence.append(hits[0])
                    continue
            budget = min(_QUICK_EXACT_MS, self.timeout_ms)
            if self.deadline is not None:
                budget = min(budget, int((self.deadline - monotonic()) * 1000))
            if budget <= 0:
                raise ProofBudgetExceeded("proof wall budget exhausted")
            # Wall clock = the budget, as the fresh per-row solver had (not the
            # reachability 10x safety net): a row must not overrun the node deadline.
            answer = prefix.check([premise, *_ordered_conjuncts(x.condition)], budget, "correspondence", budget)
            if answer not in (sat, unsat):
                unknown.append(j)
            if answer == unsat:
                correspondence.append(None)
                continue
            target = "all"
            if answer == sat:
                model = prefix.solver.model()
                hits = [i for i, e in enumerate(evm)
                        if is_true(model.eval(e.condition, model_completion=True))]
                if len(hits) == 1:
                    target = hits[0]
            correspondence.append(target)
        # A row sibling-proposed (propose_from_siblings) tries "empty" only if
        # prove() cannot confirm the proposal (Safe 5377: ~300s on 16 rows here).
        proposed = propose_from_siblings(correspondence, x86) if unknown else ()
        for j in unknown:
            if proposed[j] == "all" and self._empty_by_bvabs(premise, x86[j]):
                correspondence[j] = None
        return tuple(correspondence)

    def _empty_by_bvabs(self, premise, x):
        """Propose "empty" (Safe 4524 x86 path 2: a word-gas carry only the
        bvabs route refutes; "all" made 25 pairs of it). A proposal only: the
        x86_empty_j obligation is still proved by _check."""
        left = self.timeout_ms if self.deadline is None else int((self.deadline - monotonic()) * 1000)
        if refute_over_bv_abstraction(And(premise, x.condition), min(self.timeout_ms, left))[1] == "unsat":
            return True
        # A memory charge the x86 path checks for overflow (Permit2 1327 x86 paths 6/7): only
        # bounded through the potential (refute_over_bounded_potential). Returns at once without one.
        left = self.timeout_ms if self.deadline is None else int((self.deadline - monotonic()) * 1000)
        return refute_over_bounded_potential(And(premise, x.condition), min(self.timeout_ms, left))[1] == "unsat"

    def _check_all(self, obligations, records):
        """Yield `_check` answers for (name, formula, _) in order.

        With BLOCK_PAIR_WORKERS > 1 the same `_check` runs in worker processes
        on an SMT2 round-trip of each formula; records keep the input order and
        a failure stops the consumer exactly as in the sequential loop.
        """
        pool = _pair_pool()
        if pool is None or len(obligations) < 2:
            for name, formula, _ in obligations:
                yield self._check(name, formula, records)
            return
        remaining = None if self.deadline is None else self.deadline - monotonic()
        self._node_serial = getattr(self, "_node_serial", 0) + 1
        node = (id(self), self._node_serial)
        futures = [pool.submit(_check_serialized, _to_smt2(formula), name, self.timeout_ms, remaining, node)
                   for name, formula, _ in obligations]
        try:
            for future in futures:
                # A z3 call can outrun its own timeout; workers are processes, so
                # the node deadline is enforced here by killing the pool.
                # One absolute grace window for the whole batch, not 30s per future.
                wait = None if self.deadline is None else max(0.0, self.deadline + 30 - monotonic())
                try:
                    record = future.result(timeout=wait)
                except FutureTimeout:
                    _reset_pair_pool()
                    raise ProofBudgetExceeded("pair workers outran the node deadline")
                records.append(record)
                if _TRACE_OBLIGATIONS:
                    print(f"[obligation] {record.name} {record.answer} {record.elapsed_seconds:.1f}s", flush=True)
                    if not record.proved:  # diagnostic: keep the failed query for offline analysis
                        index = futures.index(future)
                        with open(f"/tmp/failed_{record.name}.smt2", "w") as handle:
                            handle.write(_to_smt2(obligations[index][1]))
                yield record.proved
        finally:
            if not all(f.done() for f in futures):
                _reset_pair_pool()  # free workers still solving abandoned obligations

    def _retry_over_lia(self, formula):
        """Refute F over its linear-integer reading (verification/linear_encoding).

        Byte-split limb concats are first joined (each old == new refuted by
        the solver, so F' ≡ F) and F' is refuted over lia_query(F'), which only
        adds models. Failing that, subterms LIA proves equal as identities are
        merged (sweep_equalities; each x ≠ y refuted over lia_query) and the
        result is refuted exactly or over LIA. Anything else returns
        (F, "unknown", ()), so no timeout becomes a proof.
        """
        budget = min(self.timeout_ms, _LIA_MS)
        if self.deadline is not None:
            budget = min(budget, int((self.deadline - monotonic()) * 1000))
        target, lemmas = simplify(formula, bv_sort_ac=True), []
        if budget <= 0 or not _nonlinear_mul_terms(target):
            return formula, "unknown", ()  # built for product limbs; skip the cost elsewhere
        for _ in range(4):  # a join can expose another inside the new Extract
            proved = []
            for old, new in split_limb_joins(target):
                started, goal = monotonic(), Not(old == new)
                if solve_query(goal, 1000) == "unsat":
                    proved.append((old, new))
                    lemmas.append(Obligation(f"join_{len(lemmas)}", goal.sexpr(), "unsat",
                                             elapsed_seconds=monotonic() - started))
            if not proved:
                break
            target = simplify(substitute(target, *proved), bv_sort_ac=True)
        query, started = lia_query(target), monotonic()
        if query is not None and solve_query(query, budget) == "unsat":
            return target, "unsat", tuple(lemmas) + (
                Obligation("lia", query.sexpr(), "unsat", elapsed_seconds=monotonic() - started),)
        # Differently built product limbs / borrow chains: merge those LIA proves
        # equal (identities, no premise), so the exact solver sees one term.
        # ponytail: fixed 20s sweep wall; per-lemma cap _LIA_MS.
        end = monotonic() + 20 if self.deadline is None else min(monotonic() + 20, self.deadline)
        target, merged = sweep_equalities(target, _LIA_MS, end, lemma_ms=_LIA_MS, prove=_prove_equal_lia)
        if not merged:
            return formula, "unknown", ()
        target = simplify(target, bv_sort_ac=True)
        for name, query in (("exact", target), ("lia", lia_query(target))):
            if self.deadline is not None:
                budget = min(budget, int((self.deadline - monotonic()) * 1000))
            started = monotonic()
            if query is not None and budget > 0 and solve_query(query, budget) == "unsat":
                return target, "unsat", tuple(lemmas) + merged + (
                    Obligation(name, query.sexpr(), "unsat", elapsed_seconds=monotonic() - started),)
        return formula, "unknown", ()

    def _retry_over_potential(self, formula):
        """Refute F with memory costs C(w) read as one uninterpreted P(w).

        abstract_memory_potential only adds models; telescope_potential is an
        equivalence given its axioms (true of P read as C); unify_potential_arguments
        keeps every model. So UNSAT transfers back; anything else is (F, "unknown", ()).
        Not applicable (no memory-cost sum to telescope): returns at once.
        No monotonicity axioms in the main attempts: every case measured refuted without
        them, faster. Only when those fail, one bit-blasted attempt with
        potential_range_axioms (valid for P read as C, so UNSAT still transfers).
        """
        abstract, changed = abstract_memory_potential(formula)
        if not changed:
            return formula, "unknown", ()
        target, lemmas, axioms, steps = telescope_potential(abstract)
        if not steps and not axioms:  # neither telescoped nor lifted a literal branch
            return formula, "unknown", ()
        target = And(target, *axioms)
        # Fully lifted, P(A) != P(B) often needs only A == B (linear): one quick query before
        # the argument merges (Safe 5377 H2 memory_gas_0: 0.1s, unify_potential_arguments 22-28s).
        quick = _QUICK_EXACT_MS if self.deadline is None else min(_QUICK_EXACT_MS, int((self.deadline - monotonic()) * 1000))
        if quick > 0 and solve_query(target, quick) == "unsat":
            return target, "unsat", lemmas
        target, merged = unify_potential_arguments(target, self.timeout_ms, self.deadline, cache=self._lemma_cache)
        # Capped at 4 query timeouts (one dud solve burned 558s of a Safe 5377 node); one that
        # runs out is left pending and _check resumes it once every other route has failed
        # (Safe 8915 pair_25_1 needs 83-153s CPU).
        budget = 4 * self.timeout_ms
        if self.deadline is not None:
            budget = min(budget, int((self.deadline - monotonic()) * 1000))
        if budget > 0:
            answer = solve_query(target, budget)
            if answer == "unsat":
                return target, "unsat", lemmas + merged
            if answer == "unknown" and self._potential_pending is None:
                self._potential_pending = (formula, target, lemmas + merged)  # _check may resume it
        # Last: charges bounded through P's range and monotonicity (potential_range_axioms),
        # bit-blasted over the bv abstraction (Permit2 1327 x86 path 6 cost overflow: 3-10s; the
        # exact solve without the axioms is unknown, the abstraction abstract-SAT). After the
        # attempts above, so what they prove costs nothing more. One per-query budget.
        budget, bounds = self.timeout_ms, potential_range_axioms(target)
        if self.deadline is not None:
            budget = min(budget, int((self.deadline - monotonic()) * 1000))
        if bounds and budget > 0:
            query, answer = refute_over_bv_abstraction(And(target, *bounds), budget)
            if answer == "unsat":
                return query, "unsat", lemmas + merged
        return formula, "unknown", ()

    def _retry_over_nonlinear_mul(self, formula, answer, split=False):
        """Try a cheaper refutation over `abstract_nonlinear_mul` first.

        Sound because the abstraction only adds models (see that function):
        UNSAT there is UNSAT here. Anything else keeps the original unknown, so
        a timeout can never be laundered into a proof. The recorded obligation
        carries the abstracted formula, so the report shows what was refuted.
        """
        budget = self.timeout_ms
        if self.deadline is not None:
            budget = min(budget, int((self.deadline - monotonic()) * 1000))
        if budget <= 0:
            return formula, answer, ()
        if split and is_false(formula):  # normalisation alone refuted it
            return formula, "unsat", ()
        functions = {}
        abstraction, changed = abstract_nonlinear_mul(formula, functions=functions)
        if not changed:
            return formula, answer, ()
        abstraction = And(abstraction, *mul_truncation_axioms(abstraction, functions))
        query = simplify(abstraction)
        if not split:
            return (abstraction, "unsat", ()) if solve_query(query, budget) == "unsat" else (formula, answer, ())
        # split (normalised formulas): gas guards (msize <= old, first expansion)
        # are ite conditions; per-case simplification cancels the sums both
        # sides now share. Cheaper than the unification route when nothing
        # needs merging.
        cases = _refute_by_cases(BoolVal(True), query, self.timeout_ms, self.deadline) if _ite_conditions(query) else None
        if cases is None:
            return formula, answer, ()
        return abstraction, "unsat", tuple(
            Obligation(f"case_{n}", q.sexpr(), "unsat", elapsed_seconds=t) for n, (q, t) in enumerate(cases))

    def _after_unification(self, unified, lemmas, cap):
        """(refuted target, "unsat", lemmas) for F' = unified (F ⊨ F', lemmas: the
        merges), each attempt with at most `cap` ms; or None.

        Merged arguments make both sides' UF applications one term, but memory
        (lambda) arguments keep the array theory incomplete: make those
        applications opaque (only adds models) and try once before the sweep
        (Safe 5377 pair: 1253s unknown -> 171s, the opaque query 4.5s). Last,
        F' with reads through store chains blasted into ites (an equivalent
        formula, as in the "blast" route): with the hashes merged, the memory
        words both sides charge gas for are compared there (Permit2 1327
        x86_maps_0_0, where the opaque queries stay unknown).
        """
        opaque = [(t, c) for t, c in _uf_app_constants(unified) if any(_is_array_term(a) for a in t.children())]
        started = monotonic()
        budget = cap if self.deadline is None else min(cap, int((self.deadline - started) * 1000))
        attempts = ()
        if opaque:
            query = simplify(substitute(unified, *opaque))
            # Both memories' matching top stores peeled off first (a weakening, see
            # peel_matching_stores; Safe 5377 d30 pair_68_58: 113-126s -> 5s). If the
            # weaker query is not refuted, the unpeeled one is tried as before.
            peeled = peel_matching_stores(query)
            attempts = ((("opaque_array_uf_peeled",) + peeled,) if peeled is not None else ()) + (
                ("opaque_array_uf", query, ()),)
        attempts += (("blasted", None, ()),)
        for tag, target, peel_lemmas in attempts:
            if target is None:
                target = simplify(unified, blast_select_store=True)
            else:
                # Gas sums out first (Safe 5377 d30 pair_68_9: 10s here, 60s+ with them).
                light = _refute_over_light_premise(_conjuncts(target), BoolVal(True), budget)
                if light is not None:
                    (light_query, seconds), = light[0]
                    return light_query, "unsat", lemmas + peel_lemmas + (
                        Obligation(f"{tag}_light", light_query.sexpr(), "unsat", elapsed_seconds=seconds),)
            if self.deadline is not None:
                budget = min(budget, int((self.deadline - monotonic()) * 1000))
            if budget > 0 and solve_query(target, budget) == "unsat":
                return target, "unsat", lemmas + peel_lemmas + (
                    Obligation(tag, target.sexpr(), "unsat", elapsed_seconds=monotonic() - started),)
            if self.deadline is not None:
                budget = min(cap, int((self.deadline - monotonic()) * 1000))
        return None

    def _retry_with_uf_unification(self, formula, answer):
        """Rewrite F by entailed equalities, then refute it by case splits.

        Every model of F is a model of each rewrite (unify_uf_arguments,
        sweep_equalities), so only UNSAT transfers back; anything else returns
        F with `answer` untouched. Runs over the multiplication abstraction so
        squared word counts are UF applications whose operands merge too; the
        square_monotonicity axioms (valid for bvmul) are conjoined. The
        record is proved only if every lemma and every leaf case was refuted.
        """
        # Valid argument identities first (unify_identities, F ≡ F'): the applications they
        # merge need no premise query at all; a contradiction between them is then syntactic.
        # ponytail: capped at 4 query timeouts (Aave 8248 pair_0_1 needs ~70s).
        cap = monotonic() + 4 * self.timeout_ms / 1000
        (merged,), identities = unify_identities([formula], cap if self.deadline is None else min(cap, self.deadline))
        if not identities:
            return self._unify_and_split(formula, answer)
        started = monotonic()
        budget = _QUICK_EXACT_MS if self.deadline is None else min(
            _QUICK_EXACT_MS, int((self.deadline - started) * 1000))
        query = simplify(merged)
        if budget > 0 and solve_query(query, budget) == "unsat":
            return merged, "unsat", identities + (
                Obligation("identities_quick", query.sexpr(), "unsat", elapsed_seconds=monotonic() - started),)
        proved, got, lemmas = self._unify_and_split(merged, answer)
        return (proved, got, identities + lemmas) if got == "unsat" else (formula, answer, ())

    def _unify_and_split(self, formula, answer):
        """The unification and case-split attempts of _retry_with_uf_unification on F."""
        functions = self._mul_functions
        base = abstract_nonlinear_mul(formula, functions=functions)[0]
        early = []

        def probe(merged, merged_lemmas, term):
            # After each merge of memory (lambda) arguments, the attempts below with the
            # quick budget: the merges that matter can come long before the pairs that
            # never merge are exhausted (Permit2 1327 x86_maps_0_0: the level-3 sha3_slice
            # merge, then ~35 failing host-gas argument pairs for 900s; the blasted query
            # of the merged formula is refuted at once).
            if _is_array_term(term):
                early.extend(filter(None, [self._after_unification(merged, merged_lemmas, _QUICK_EXACT_MS)]))
            return bool(early)
        unified, lemmas = unify_uf_arguments(base, self.timeout_ms, self.deadline, cache=self._lemma_cache,
                                             on_merge=probe)
        if early:
            return early[0]
        found = self._after_unification(unified, lemmas, self.timeout_ms) if lemmas else None
        if found is not None:
            return found
        before = unified
        unified, swept = sweep_equalities(unified, self.timeout_ms, self.deadline, cache=self._lemma_cache)
        if swept:  # merged subterms can make more UF arguments syntactically equal
            unified = restore_rewritten_conjuncts(before, unified)
            unified, again = unify_uf_arguments(unified, self.timeout_ms, self.deadline, cache=self._lemma_cache)
            lemmas += swept + again
        unified = And(unified, *square_monotonicity(unified, functions), *square_shift_axioms(unified, functions),
                      *mul_truncation_axioms(unified, functions))
        query = simplify(unified)
        if not lemmas and not _ite_conditions(query):
            return formula, answer, ()
        # Gas guards compare telescoped sums; per-case simplification cancels them.
        # ponytail: 4x the per-query budget for the whole case tree; the node deadline still bounds it.
        cases = _refute_by_cases(BoolVal(True), query, 4 * self.timeout_ms, self.deadline)
        if cases is None and lemmas:
            # The UF can be too weak (abstract SAT); read it as bvmul again
            # over the unified formula, see concretize_mul.
            started = monotonic()
            budget = self.timeout_ms
            if self.deadline is not None:
                budget = min(budget, int((self.deadline - started) * 1000))
            exact = simplify(concretize_mul(unified, functions))
            if budget > 0 and solve_query(exact, budget) == "unsat":
                return concretize_mul(unified, functions), "unsat", lemmas + (
                    Obligation("exact", exact.sexpr(), "unsat", elapsed_seconds=monotonic() - started),)
        if cases is None:
            # Last resort for an obligation that otherwise fails its node. Capped
            # (not the whole remaining node budget): in parallel workers one hard
            # obligation must not starve all its siblings.
            if self.deadline is None:
                return formula, answer, ()
            started = monotonic()
            remaining = min(int((self.deadline - started) * 1000), _LAST_RESORT_MS)
            if remaining <= 0 or solve_query(query, remaining) != "unsat":
                return formula, answer, ()
            return unified, "unsat", lemmas + (
                Obligation("direct", query.sexpr(), "unsat", elapsed_seconds=monotonic() - started),)
        return unified, "unsat", lemmas + tuple(
            Obligation(f"case_{n}", q.sexpr(), "unsat", elapsed_seconds=t) for n, (q, t) in enumerate(cases))

    def _retry_over_guard_cases(self, formula, depth=0):
        """Split F on its smallest UF guard (uf_guards), then refute each case
        by the unification route (_unify_and_split), splitting a case that is
        not refuted on its own smallest guard again, _GUARD_MAX_DEPTH levels
        at most. (F, "unsat", lemmas) only if every case is refuted, else
        (F, "unknown", ()); returns at once when F has no such guard.

        Sound by assume_guard: the cases cover F, each is equivalent to F
        under its literal, and within a case unification is the usual
        weakening (only UNSAT transfers back). The lemmas are every case's
        refutations, named guard_<depth>_<case>_*. Each case gets an equal
        share of what is left of the route's deadline."""
        guards = uf_guards(formula)
        if not guards:
            return formula, "unknown", ()
        lemmas, deadline = [], self.deadline
        try:
            for n, value in enumerate((True, False)):
                started = monotonic()
                case = assume_guard(formula, guards[0], value)
                if deadline is not None:
                    self.deadline = started + (deadline - started) / (2 - n)
                budget = _QUICK_EXACT_MS if self.deadline is None else min(
                    _QUICK_EXACT_MS, int((self.deadline - started) * 1000))
                if budget > 0 and solve_query(case, budget) == "unsat":
                    sub = (Obligation("quick", case.sexpr(), "unsat", elapsed_seconds=monotonic() - started),)
                else:
                    _, answer, sub = self._unify_and_split(case, "unknown")
                    if answer != "unsat" and depth + 1 < _GUARD_MAX_DEPTH:
                        _, answer, sub = self._retry_over_guard_cases(case, depth + 1)
                    if answer != "unsat":
                        return formula, "unknown", ()
                lemmas.extend(replace(r, name=f"guard_{depth}_{n}_{r.name}") for r in sub)
        finally:
            self.deadline = deadline
        return formula, "unsat", tuple(lemmas)

    def _pair_phase(self, evm, x86, premise, pair, found, records):
        """Pair-phase obligations for the correspondence `found`
        (_correspondence); appends their records in manifest order and
        returns the final correspondence the manifest must be built from.

        Sibling proposals (propose_from_siblings) stay mapped even when the
        prefix passes leave some of their x86_maps undischarged (Safe 5377 /
        CErc20 12930: 88-95% discharged, 5-28 hard memgas maps left, and
        reverting the whole row to "all" blew the node budget). The rest are
        checked with everything else; a proposed row with a failing
        obligation is degraded alone to "all" (None if _empty_by_bvabs) and
        its full row is checked in a second round.

        Soundness: a proposal is a guess, never a premise. The theorem is
        judged only by BlockTheorem.complete against the manifest of the
        returned correspondence, so each final row is justified by its own
        UNSAT records: x86_maps_j_* + pair_s_j for a kept row, pair_i_j for
        every i (or x86_empty_j) for a degraded one. A wrong proposal fails
        (sat/unknown) and costs time; unknown never counts as proved, and
        the degraded row's failed and discarded records do not enter the
        certificate. Degrading never removes the last int row (a proposal
        needs a mapped sibling from `found`, which is never degraded), so
        the evm_disjoint records stay required.
        """
        correspondence = propose_from_siblings(found, x86)
        proposed = {j for j, (was, now) in enumerate(zip(found, correspondence)) if was != now}
        jobs = {}
        for j, target in enumerate(correspondence):
            if type(target) is int:
                for k, conjunct in enumerate(_conjuncts(evm[target].condition)):
                    jobs.setdefault(conjunct.get_id(), (conjunct, []))[1].append((j, k))
        # ponytail: the prefix pass gets 1/4 of the remaining node budget; leftovers use the full routes.
        share = None if self.deadline is None else monotonic() + (self.deadline - monotonic()) / 4
        stuck = []
        discharged = discharge_maps_by_prefix(
            premise, {j: x86[j].condition for j in {j for _, es in jobs.values() for j, _ in es}},
            list(jobs.values()), min(_QUICK_EXACT_MS, self.timeout_ms), share, stuck)
        # ponytail: groups of >= _STUCK_MIN_MEMBERS maps, <= 2 query timeouts each, the phase
        # min(1/4 of what is left, 10 query timeouts); uncovered members use their own routes.
        cap = 10 * self.timeout_ms / 1000
        if self.deadline is not None:
            cap = min(cap, (self.deadline - monotonic()) / 4)
        self._prove_stuck_groups([g for g in stuck if len(g[1]) >= _STUCK_MIN_MEMBERS], discharged,
                                 monotonic() + cap, 2 * self.timeout_ms / 1000)
        ready = {f"x86_maps_{j}_{k}": r for (j, k), r in discharged.items()}
        start = len(records)
        failed = self._check_rows(evm, x86, premise, pair, correspondence, range(len(x86)), ready, records,
                                  proposed)
        if failed:
            # Round 2: only the failed proposals, as full rows. Proved round-1
            # records (e.g. pair_s_j itself) are reused by name.
            ready.update((r.name, r) for r in records[start:] if r.proved)
            for j in failed:
                correspondence[j] = None if self._empty_by_bvabs(premise, x86[j]) else "all"
            self._check_rows(evm, x86, premise, pair, correspondence, sorted(failed), ready, records)
        correspondence = tuple(correspondence)
        # Manifest order from the final correspondence. Later records win and
        # proved `ready` ones win over any record, so a failed round-1 record
        # never shadows its round-2 proof; a degraded row's x86_maps_j_* are
        # no longer named and drop out.
        by_name = {**{r.name: r for r in records[start:]}, **ready}
        records[start:] = [by_name[name] for name in pair_obligation_names(
            len(evm), len(x86), correspondence, map_arity(evm, correspondence))
                           if not name.startswith("evm_disjoint_")]  # recorded by _correspondence
        return correspondence

    def _check_rows(self, evm, x86, premise, pair, correspondence, rows, ready, records, tolerated=()):
        """Check the obligations of x86 rows `rows` under `correspondence`
        (the full product if it is ()), appending their records. Names in
        `ready` (proved records) are not checked again; "all" rows add their
        shared-prefix proofs to it. A failing obligation of a row in
        `tolerated` marks that row; any other failure fails the node: at once,
        or with keep_going after the remaining items (recorded in
        _kept_failures; prove() turns them into the node's failure).
        Returns the marked rows."""
        n = len(evm)
        alls = [j for j in rows if correspondence and correspondence[j] == "all"]
        if alls:
            # ponytail: the shared-prefix pass for "all" rows gets 1/2 of what is left; leftovers use their own pairs.
            ready.update((f"pair_{i}_{j}", r) for (i, j), r in self._discharge_all_rows(
                premise, evm, x86, alls, monotonic() + (
                    1e9 if self.deadline is None else (self.deadline - monotonic()) / 2)).items())
        items = []  # (row, name, formula, where)
        if not correspondence:
            items = [(None, *pair(i, j)) for i in range(n) for j in range(len(x86))]
        for j in rows if correspondence else ():
            target, x = correspondence[j], x86[j]
            if target is None:
                items.append((j, f"x86_empty_{j}", And(premise, x.condition), f"x86 path {j} empty"))
            elif target == "all":
                items += [(j, *pair(i, j)) for i in range(n) if f"pair_{i}_{j}" not in ready]
            else:
                # x_j => c_1 ∧ … ∧ c_K is proved conjunct by conjunct.
                items += [(j, f"x86_maps_{j}_{k}", And(premise, x.condition, Not(conjunct)),
                           f"x86 path {j} implies conjunct {k} of evm path {target}")
                          for k, conjunct in enumerate(_conjuncts(evm[target].condition))
                          if f"x86_maps_{j}_{k}" not in ready]
                if f"pair_{target}_{j}" not in ready:
                    items.append((j, *pair(target, j)))
        # Exact rewrite (common/store_forwarding): a read through stores at
        # the same base plus distinct / equal constant offsets is resolved.
        # The x86 stack chain holding the callers' return tags drops out,
        # so call sites of one function share alpha-equal obligations
        # (CErc20 4236 pair_7_8: 292KB -> 25KB, equal across call sites).
        forwarded = {}
        canon = {}  # one per call: siblings of these rows share it
        pairs = [(name, canon_binders(forward_selects(f, forwarded), canon), where) for _, name, f, where in items]
        # "all" rows are mostly infeasible cross-path joints: no host-call
        # arguments to share, and unifying them cost Safe 5377 ~1000s.
        pairs, node_lemmas, rewritten = self._unify_node(pairs, skip={
            name for j, name, _, _ in items if correspondence and correspondence[j] == "all"})
        mark, failed = len(records), set()
        checks = self._check_all(pairs, records)
        try:
            for (row, *_), (name, _, where), ok in zip(items, pairs, checks):
                if not ok:
                    if row not in tolerated:
                        if not self.keep_going:
                            raise ValueError(f"outcome mismatch {name}: {where} (solver={records[-1].answer})")
                        self._kept_failures.append(dict(name=name, answer=records[-1].answer,
                                                        seconds=records[-1].elapsed_seconds, where=where))
                        continue
                    failed.add(row)
        finally:
            checks.close()
        # A rewritten pair was refuted only together with the node lemmas.
        records[mark:] = [replace(r, lemmas=r.lemmas + node_lemmas) if r.name in rewritten else r
                          for r in records[mark:]]
        return failed

    def prove(self, spec):
        started = monotonic()
        if spec.pc not in self.pc_to_addr:
            return BlockProofResult.inconclusive(spec, f"block pc={spec.pc} is not in the authoritative mapping")
        records = []
        runtime = None
        result = BlockProofResult(spec)
        self._node_needed_unification = False
        self._route_stats = {}
        self._kept_failures = []
        program_deadline = self.deadline
        if self.node_timeout_seconds is not None:
            node_deadline = started + self.node_timeout_seconds
            self.deadline = min(program_deadline, node_deadline) if program_deadline is not None else node_deadline
        try:
            self.validate()
            context = self.schema.build_havoc(
                prefix=f"blk{spec.pc}_{spec.stack_depth}_{spec.memory_size}_{spec.free_memory_pointer}",
                host_gas_uf_enabled=self.host_gas_uf_enabled,
                assume_calldata_offset_no_overflow=False,
                abstract_calldataload_words=False, **spec.as_havoc_kwargs())
            result.context = context
            state = context.state
            premise = And(*(state.assumptions or []))
            if not self._check("entry_nonempty", premise, records, expected="sat"):
                raise ValueError("entry predicate empty or unknown")
            relation_goals = self.schema.relation_goals(state, state, spec,
                                                        memory_snapshot=context.memory_snapshot)
            self.schema._assert_component_symmetry(context, tuple(
                g for g in relation_goals if g.name in self.schema.component_names))
            relation = And(*(g.condition for g in relation_goals))
            if not self._check("havoc_relation", And(premise, Not(relation)), records):
                raise ValueError("havoc does not establish the declared relation")
            # Initial entry is exempted once by the executors, not by deleting
            # its address from the stop set (which loses self-loop edges).
            evm, ed = run_evm_segment(self.evm_blocks, state.copy(), spec.pc,
                                      set(self.pc_to_addr), max_depth=self.max_depth)
            if self.summary_config is not None:
                from .block_summaries import VerifiedSummaryRuntime
                runtime = VerifiedSummaryRuntime(self.x86_blocks, self.summary_config,
                    cutpoints=self.pc_to_addr.values(), timeout_ms=self.timeout_ms, max_depth=self.max_depth,
                    deadline=self.deadline, runtime=self._summary_templates)
                self._summary_templates = runtime.runtime
            x86, xd, _ = run_x86_segment(
                self.x86_blocks, state.copy(), self.pc_to_addr[spec.pc],
                set(self.pc_to_addr.values()), max_depth=self.max_depth,
                aot_profile=self.aot_profile, use_reachability_check=True, summary_runtime=runtime,
                deadline=self.deadline, call_site_mapping=self.call_site_mapping)
            result.evm_outcomes, result.x86_outcomes = tuple(evm), tuple(x86)
            result.evm_paths, result.x86_paths = len(evm), len(x86)
            if len(evm) * len(x86) > self.max_path_pairs:
                raise ValueError("local path-pair resource budget exhausted")
            if ed or xd:
                raise ValueError("finite segment coverage incomplete: " + "; ".join((*ed, *xd)))
            conditions = [premise, *(p.condition for p in (*evm, *x86))]
            axioms = host_model_axioms(conditions) + div_quotient_axioms(conditions)
            premise = And(premise, *axioms)
            result.premise = premise
            if not self._check("model_domain_nonempty", premise, records, expected="sat"):
                raise ValueError("oracle model and entry domain inconsistent or unknown")
            self.check_paths(evm, x86, premise, state, records)
            def pair(i, j):
                e, x = evm[i], x86[j]
                joint = And(premise, e.condition, x.condition)
                if e.kind == x.kind == "terminal":
                    conditions = terminal_observable_conditions(
                        e.state, x.state, context.memory_snapshot, self.compare_gas)
                    if not all(is_bool(c) for c in conditions):
                        raise ValueError("missing terminal observable")
                    goal = And(*conditions)
                    result.terminals_proved += 1
                elif e.kind != "terminal" and x.kind != "terminal" and e.location is not None and self.pc_to_addr.get(e.location) == x.location:
                    # This is the unspecialized edge postcondition. H2 must
                    # still prove the full successor disjunction in block_program.
                    goal = And(*())
                    result.paired_transitions += 1
                else:
                    goal = Or()  # every cross-kind/different-edge joint must be UNSAT
                return (f"pair_{i}_{j}", And(joint, Not(goal)),
                        f"{e.kind}@{e.location} / {x.kind}@{x.location}")

            correspondence = self._pair_phase(evm, x86, premise, pair,
                                              self._correspondence(evm, x86, premise, records), records)
            if self._kept_failures:
                # keep_going: the same failure, raised after every row was tried.
                raise ValueError(f"outcome mismatch ({len(self._kept_failures)} pair obligations, keep-going): "
                                 + "; ".join(f"{f['name']}: {f['where']} (solver={f['answer']})"
                                             for f in self._kept_failures))
            result.theorem = BlockTheorem(
                self.identity, spec, tuple(records),
                obligation_manifest(evm, x86, state, correspondence=correspondence),
                paths_digest(evm, x86), len(evm), len(x86), True,
                tuple(runtime.certificates) if runtime is not None else (),
                len(runtime.certificates) if runtime is not None else 0,
                correspondence=correspondence, arity=map_arity(evm, correspondence))
            if result.theorem.complete:
                self._issued_theorems.append(result.theorem)
                result._issuer = self
                result.status = "proved"
        except Exception as exc:
            # No exception, solver unknown or missing semantic field can mint a theorem.
            result.reasons += (f"{type(exc).__name__}: {exc}",)
        finally:
            self.deadline = program_deadline
        result.kept_failures = tuple(self._kept_failures)  # also after a later abort (e.g. node budget)
        result.obligations = tuple(records)
        result.queries = len(records) + (runtime.proof_queries if runtime is not None else 0)
        result.elapsed_seconds = monotonic() - started
        return result

    def check_paths(self, evm, x86, premise, initial, records):
        allowed = {a.get_id() for a in initial.assumptions or []}
        for label, paths in (("evm", evm), ("x86", x86)):
            justified = set(allowed)
            if not paths:
                raise ValueError(f"{label}: empty outcome set")
            for path in paths:
                if path.kind not in ("terminal", "exit", "latch") or not is_bool(path.condition):
                    raise ValueError(f"{label}: unclassified outcome")
                for queue in ("pending_errors", "pending_constraints"):
                    if getattr(path.state, queue):
                        raise ValueError(f"{label}: unconsumed {queue}")
                if getattr(path.state, "unrouted_memory_domain", None):
                    raise ValueError(f"{label}: unresolved memory domain")
                # Additional executor assumptions cannot silently become the
                # theorem domain. Explicitly reject until separately justified.
                for assumption in path.state.assumptions or []:
                    if assumption.get_id() in justified:
                        continue
                    # Never use the final path guard here: it already contains
                    # the assumption being audited. A tautological arithmetic
                    # hint can be established from the ORIGINAL premise alone.
                    # The div r64 quotient-fits hint is a tautology instance:
                    # with its axiom it needs no premise (whose 128-bit
                    # dividends, e.g. 1e18 * x, defeat the bit-blaster).
                    # Borrow-chain bridges over products (1e18 * x) are
                    # tautologies about the limbs; generalising every product
                    # to a fresh constant proves them for ALL values, hence for
                    # these (the hint is a substitution instance).
                    # A hint over a whole product word (a 256-bit compare of a limb-wise
                    # product) is a tautology about the word: generalised words prove it
                    # (Aave 11831; tried first: the generalised query is tiny, a miss is quick).
                    hints = div_quotient_axioms([assumption])
                    goal = And(premise, Not(assumption))
                    words = _generalize_product_words(assumption)
                    for candidate in (*(() if words is None else (Not(words),)),
                                      Not(_generalize_products(assumption)), And(*hints, Not(assumption))):
                        if solve_query(candidate, min(self.timeout_ms, 5000)) == "unsat":
                            goal = candidate
                            break
                    if not self._check(f"{label}_assumption_{len(justified)}", goal, records):
                        raise ValueError(f"{label}: unproved execution assumption")
                    justified.add(assumption.get_id())
            name, coverage = f"{label}_coverage", And(premise, Not(Or(*(p.condition for p in paths))))
            # The bvmul->UF route (_retry_over_nonlinear_mul: abstraction UNSAT
            # is exact UNSAT) before _check's cascade: symbolic memory gas makes
            # the exact coverage query slow (Safe 5377 x86: 251s -> 11s). A miss
            # costs at most one query budget and falls through unchanged.
            started = monotonic()
            proved, answer, _ = self._retry_over_nonlinear_mul(coverage, "unknown")
            if answer == "unsat":
                records.append(Obligation(name, proved.sexpr(), "unsat", "unsat", monotonic() - started))
            elif not self._check(name, coverage, records):
                raise ValueError(f"{label}: outcome guards do not cover the entry domain")
