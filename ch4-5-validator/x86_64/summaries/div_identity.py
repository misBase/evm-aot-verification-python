"""Proved self-division facts for the zero-extended operands of DIV r64."""
from time import monotonic

from z3 import (And, BitVecSort, BitVecVal, Extract, Implies, Not, ZeroExt,
                Z3_OP_BUDIV, Z3_OP_BUDIV_I, is_true, simplify, substitute)

from common.fresh_symbols import FreshSymbols


_SELF_DIV_PROOFS = {}  # (context, actual unsigned operator kind) -> (input, theorem, proof)


def _self_division(term, timeout_ms):
    from verification.block_equivalence import Obligation, solve_pure_bv

    key = (term.ctx, term.decl().kind())
    if key in _SELF_DIV_PROOFS:
        result = _SELF_DIV_PROOFS[key]
        return result if result[2].proved else None
    value = FreshSymbols(term).const(BitVecSort(64, ctx=term.ctx), "division_self_input")
    extended = ZeroExt(64, value)
    theorem = Implies(value != 0, term.decl()(extended, extended) == BitVecVal(1, 128, ctx=term.ctx))
    query = Not(theorem)
    started = monotonic()
    answer = solve_pure_bv(query, timeout_ms)
    proof = Obligation(f"division_self_64_128_{term.decl().kind()}", query.sexpr(), answer,
                       elapsed_seconds=monotonic() - started, required_lemmas=(),
                       provenance="generic_division_identity")
    if not proof.proved:
        return None
    result = (value, theorem, proof)
    _SELF_DIV_PROOFS[key] = result
    return result


def with_division_identities(query, *, timeout_ms):
    """Return Q with only independently proved ground facts and their dependencies."""
    from verification.block_equivalence import (Obligation, _builtin_divrem_terms,
                                                abstract_divrem_congruence, solve_pure_bv)

    deadline = monotonic() + max(0, timeout_ms) / 1000
    facts, records = [], []
    for term in _builtin_divrem_terms(query):
        if term.size() != 128 or term.decl().kind() not in (Z3_OP_BUDIV, Z3_OP_BUDIV_I):
            continue
        a, b = term.children()
        if not all(is_true(simplify(Extract(127, 64, operand) == 0)) for operand in (a, b)):
            continue
        remaining = int((deadline - monotonic()) * 1000)
        if remaining <= 0:
            break
        generic = _self_division(term, remaining)
        if generic is None:
            continue
        value, theorem, proof = generic
        instance = Implies(And(a == b, b != 0), term == BitVecVal(1, 128, ctx=term.ctx))
        ground = substitute(theorem, (value, Extract(63, 0, b)))
        lift_query = And(ground, Not(instance))
        abstract, _ = abstract_divrem_congruence(simplify(lift_query, bv_sort_ac=True))
        remaining = int((deadline - monotonic()) * 1000)
        if remaining <= 0:
            break
        started = monotonic()
        answer = solve_pure_bv(abstract, remaining)
        lift = Obligation(f"division_identity_lift_{len(records)}", abstract.sexpr(), answer,
                          elapsed_seconds=monotonic() - started, required_lemmas=(),
                          provenance="division_congruence_lift")
        if not lift.proved:
            continue
        dependencies = (proof, lift)
        record = Obligation(f"division_identity_{len(records)}", Not(instance).sexpr(), "unsat",
                            lemmas=dependencies, required_lemmas=tuple(o.name for o in dependencies),
                            provenance="proved_division_identity")
        if record.proved:
            facts.append(instance)
            records.append(record)
    return (And(query, *facts), tuple(records)) if facts else (query, ())
