"""Persistent, content-addressed cache of decided SMT answers.

Enabled by env ``BLOCK_PROOF_CACHE=<sqlite path>``; off otherwise.

A cached answer is a fact about one query up to alpha-renaming: the primary
key hashes the AST up to renaming of uninterpreted symbols (alpha_digest),
together with the z3 version and transport revision. Earlier caches may
contain incorrect answers from lossy SMT2 serialization and are not read. Decided
answers are stored; ``unknown`` only as the budget it ran
out of, so a later query with more budget still solves it (cached_answer). Trusting a hit is the same as trusting z3 on
that identical query again: node identity, model version and run are
irrelevant — a changed model produces different query text, hence a miss.
"""
import json
import math
import re
import os
import sqlite3
from hashlib import sha256

from z3 import FuncDeclRef, get_version_string
from z3 import z3core as C

_CONNECTIONS = {}
_TRANSPORT_VERSION = "transport-v3"


class _UnsupportedAlpha(ValueError):
    """A query can still be solved, but must not use an ambiguous cache key."""


def _connection():
    path = os.environ.get("BLOCK_PROOF_CACHE")
    if not path:
        return None
    key = (os.getpid(), path)  # spawn/fork workers each open their own handle
    conn = _CONNECTIONS.get(key)
    if conn is None:
        conn = sqlite3.connect(path, timeout=120, isolation_level=None)
        conn.execute("pragma journal_mode=wal")
        conn.execute("create table if not exists answers (key text primary key, value text not null)")
        _CONNECTIONS[key] = conn
    return conn


def enabled():
    return bool(os.environ.get("BLOCK_PROOF_CACHE"))


# z3 names let-bindings after AST ids (?x88302, $x12) and fresh symbols after a
# process counter (k!17): both differ between runs for the same query.
_RUN_LOCAL_NAME = re.compile(r"[?$]x\d+|\b[A-Za-z_][A-Za-z0-9_]*![0-9]+\b")


def canonical_names(text):
    """Renumber run-local names by first appearance (a bijective renaming).

    Consistently renaming bound let-variables and distinct fresh constants is
    alpha-renaming: it changes neither satisfiability nor any other answer.
    New names use a '@' prefix no user symbol has, so nothing can collide.
    """
    names = {}

    def rename(match):
        token = match.group(0)
        if token not in names:
            names[token] = f"{token[0]}@{len(names)}" if token[0] in "?$" else f"@f{len(names)}"
        return names[token]
    return _RUN_LOCAL_NAME.sub(rename, text)


def alpha_digest(assertions):
    """sha256 of the assertions' AST DAG, uninterpreted symbols numbered by
    first visit (deterministic post-order).

    Equal digests mean the queries are equal up to an injective renaming of
    uninterpreted symbols (sorts included): alpha-renamings of each other,
    hence equisatisfiable. Hashing the AST rather than the SMT2 text ignores
    let-sharing, which to_smt2 lays out per query. CErc20 4236 is one
    internal function entered from 13 call sites whose obligations mostly
    differ only in symbol names (havoc prefix blockN_, stack slots numbered
    from the bottom) and let layout. Bound variables are de Bruijn indices;
    quantifier patterns are left out (they steer the solver, not the answer).
    """
    if not assertions:
        return sha256(b"").hexdigest()
    # Raw C API: ~3x faster than the z3py wrappers on 100KB obligations.
    context = assertions[0].ctx
    if any(a.ctx is not context for a in assertions):
        raise _UnsupportedAlpha("mixed contexts")
    ref = context.ref()
    names, heads, sorts, memo, nodes, interned = {}, {}, {}, {}, [], {}
    pending_decls = set()

    def sort(s):
        key = C.Z3_get_sort_id(ref, s)
        if key not in sorts:
            kind = C.Z3_get_sort_kind(ref, s)
            if kind in (C.Z3_BOOL_SORT, C.Z3_INT_SORT, C.Z3_REAL_SORT):
                sorts[key] = ("sort", kind)
            elif kind == C.Z3_BV_SORT:
                sorts[key] = ("bv", C.Z3_get_bv_sort_size(ref, s))
            elif kind == C.Z3_ARRAY_SORT:
                sorts[key] = ("array", tuple(sort(C.Z3_get_array_sort_domain_n(ref, s, i))
                                             for i in range(C.Z3_get_array_arity(ref, s))),
                              sort(C.Z3_get_array_sort_range(ref, s)))
            else:
                # A printed sort name is not a complete signature for e.g.
                # independently declared datatypes with the same name.
                raise _UnsupportedAlpha(f"unsupported sort kind {kind}")
        return sorts[key]

    def parameter(d, i):
        kind = C.Z3_get_decl_parameter_kind(ref, d, i)
        if kind == C.Z3_PARAMETER_FUNC_DECL:
            return ("decl", declaration(C.Z3_get_decl_func_decl_parameter(ref, d, i)))
        if kind == C.Z3_PARAMETER_SORT:
            return ("sort", sort(C.Z3_get_decl_sort_parameter(ref, d, i)))
        if kind == C.Z3_PARAMETER_INT:
            return ("int", C.Z3_get_decl_int_parameter(ref, d, i))
        if kind == C.Z3_PARAMETER_RATIONAL:
            return ("rational", C.Z3_get_decl_rational_parameter(ref, d, i))
        if kind == C.Z3_PARAMETER_DOUBLE:
            value = C.Z3_get_decl_double_parameter(ref, d, i)
            if not math.isfinite(value):
                raise _UnsupportedAlpha("nonfinite declaration parameter")
            return ("double", value.hex())
        if kind == C.Z3_PARAMETER_SYMBOL:
            symbol = C.Z3_get_decl_symbol_parameter(ref, d, i)
            symbol_kind = C.Z3_get_symbol_kind(ref, symbol)
            if symbol_kind == C.Z3_INT_SYMBOL:
                return ("int-symbol", C.Z3_get_symbol_int(ref, symbol))
            if symbol_kind == C.Z3_STRING_SYMBOL:
                return ("string-symbol", C.Z3_get_symbol_string(ref, symbol))
        # AST/internal parameters need their own structural traversal. Never
        # replace them by repr/name text, which can lose cross-position aliasing.
        raise _UnsupportedAlpha(f"unsupported declaration parameter kind {kind}")

    def declaration(d):
        key = C.Z3_get_func_decl_id(ref, d)
        if key in heads:
            return heads[key]
        if key in pending_decls:
            raise _UnsupportedAlpha("cyclic declaration parameters")
        pending_decls.add(key)
        try:
            sig = (tuple(sort(C.Z3_get_domain(ref, d, i)) for i in range(C.Z3_get_domain_size(ref, d))),
                   sort(C.Z3_get_range(ref, d)))
            if C.Z3_get_decl_kind(ref, d) == C.Z3_OP_UNINTERPRETED:
                # A UF referenced only by Map/as-array shares this same table
                # with its ordinary applications, preserving all alias links.
                heads[key] = ("uf", len(names), sig)
                names[key] = True
            else:
                heads[key] = ("op", C.Z3_get_decl_kind(ref, d), FuncDeclRef(d, context).name(),
                              tuple(parameter(d, i) for i in range(C.Z3_get_decl_num_parameters(ref, d))), sig)
            return heads[key]
        finally:
            pending_decls.remove(key)

    def head_of(app, ast, arity, ast_kind):
        d = C.Z3_get_app_decl(ref, app)
        # Numerals are values, not declarations (several values can share a
        # decl). A zero-arity builtin with parameters, notably as-array, is not.
        if (ast_kind == C.Z3_NUMERAL_AST
                or (arity == 0 and C.Z3_get_decl_kind(ref, d) != C.Z3_OP_UNINTERPRETED
                    and C.Z3_get_decl_num_parameters(ref, d) == 0)):
            return ("value", C.Z3_ast_to_string(ref, ast), sort(C.Z3_get_sort(ref, ast)))
        return declaration(d)

    stack = [(a.as_ast(), False) for a in reversed(assertions)]
    while stack:
        ast, ready = stack.pop()
        key = C.Z3_get_ast_id(ref, ast)
        if key in memo:
            continue
        kind = C.Z3_get_ast_kind(ref, ast)
        if kind in (C.Z3_APP_AST, C.Z3_NUMERAL_AST):
            app = C.Z3_to_app(ref, ast)
            arity = C.Z3_get_app_num_args(ref, app)
            if not ready:
                stack.append((ast, True))
                stack += [(C.Z3_get_app_arg(ref, app, i), False) for i in reversed(range(arity))]
                continue
            children = [C.Z3_get_app_arg(ref, app, i) for i in range(arity)]
            head = head_of(app, ast, arity, kind)
        elif kind == C.Z3_VAR_AST:
            children, head = [], ("var", C.Z3_get_index_value(ref, ast), sort(C.Z3_get_sort(ref, ast)))
        elif kind == C.Z3_QUANTIFIER_AST:
            body = C.Z3_get_quantifier_body(ref, ast)
            if not ready:
                stack += [(ast, True), (body, False)]
                continue
            children = [body]
            head = ("quantifier", C.Z3_is_quantifier_forall(ref, ast), C.Z3_is_quantifier_exists(ref, ast),
                    tuple(sort(C.Z3_get_quantifier_bound_sort(ref, ast, i))
                          for i in range(C.Z3_get_quantifier_num_bound(ref, ast))))
        else:
            raise _UnsupportedAlpha(f"alpha_digest: unexpected AST kind {kind}")
        # Structurally equal nodes intern to one number; numbering follows the
        # deterministic traversal, so the node list itself is the digest input.
        node = (head, tuple(memo[C.Z3_get_ast_id(ref, c)] for c in children))
        memo[key] = interned.setdefault(node, len(interned))
        if memo[key] == len(nodes):
            nodes.append(node)
    roots = [memo[C.Z3_get_ast_id(ref, a.as_ast())] for a in assertions]
    return sha256(repr((nodes, roots)).encode()).hexdigest()


def query_key(kind, *assertions):
    """Versioned AST alpha key; never reuse answers from the old transport.

    UF renaming preserves alpha keys, so an incorrect overloaded-name answer
    could also contaminate a currently unambiguous query. Invalidate the whole
    old namespace, including its text fallback, rather than only risky inputs.
    """
    version = f"{get_version_string()}\0{kind}\0{_TRANSPORT_VERSION}\0"
    try:
        body = alpha_digest(assertions)
    except (_UnsupportedAlpha, RecursionError):
        return None
    alpha = sha256(f"{version}alpha\0{body}".encode()).hexdigest()
    return (alpha,)


def lookup(keys):
    if keys is None:
        return None
    conn = _connection()
    if conn is None:
        return None
    for key in (keys,) if isinstance(keys, str) else keys:
        row = conn.execute("select value from answers where key = ?", (key,)).fetchone()
        if row is not None:
            return json.loads(row[0])
    return None


def store(keys, value, replace=False):
    if keys is None:
        return
    conn = _connection()
    if conn is not None:
        key = keys if isinstance(keys, str) else keys[0]
        conn.execute(f"insert or {'replace' if replace else 'ignore'} into answers (key, value) values (?, ?)",
                     (key, json.dumps(value)))


def _key_list(keys):
    return [] if keys is None else [keys] if isinstance(keys, str) else list(keys)


# key -> largest budget this process itself timed out with. A wall-clock timeout depends on the
# machine load of the run that hit it (PoolManager 22747: proved alone in ~330s, unknown for 8h on
# a loaded 10-worker batch sharing one cache), so another process's or run's unknown (the shared
# record's budget included) is retried, never trusted. Scoped to (process, cache path): a forked
# child or a switched cache starts from its own tries only.
_LOCAL_UNKNOWN = {"owner": None, "budgets": {}}


def _local_unknown_budgets():
    owner = (os.getpid(), os.environ.get("BLOCK_PROOF_CACHE"))
    if _LOCAL_UNKNOWN["owner"] != owner:
        _LOCAL_UNKNOWN.update(owner=owner, budgets={})
    return _LOCAL_UNKNOWN["budgets"]


def reset_local_unknown():
    """Retry UNKNOWN on a new node attempt; shared decided answers stay valid."""
    _local_unknown_budgets().clear()


def cached_answer(keys, timeout_ms):
    """The decided answer, "unknown" if this process already timed out on the
    query with at least this budget (re-solving would only repeat the wait: the
    losing routes of a replayed obligation), else None.

    Skipping is never unsound (unknown proves nothing).
    """
    value = lookup(keys)
    if value in ("sat", "unsat"):
        return value
    budgets = _local_unknown_budgets()
    if timeout_ms > 0 and any(budgets.get(k, 0) >= timeout_ms for k in _key_list(keys)):
        return "unknown"
    return None


def statement_key(kind, items):
    """Key of a lemma statement: ordered (name, expected answer, query) items.

    The lemma holds iff every query has its expected answer; equal keys mean
    the queries are alpha-renamings of each other under ONE renaming (a
    single alpha_digest over all of them), with the same names and answers.
    """
    if not items:
        return None
    labels = tuple((name, expected) for name, expected, _ in items)
    try:
        body = alpha_digest([query for _, _, query in items])
    except (_UnsupportedAlpha, RecursionError):
        return None
    return sha256(f"{get_version_string()}\0{_TRANSPORT_VERSION}\0lemma\0{kind}\0{labels!r}\0{body}".encode()).hexdigest()


def lemma_proved(key):
    """True only if exactly this statement (same key) was proved before."""
    return key is not None and lookup(key) == "proved"


def record_lemma(key):
    """Call only after every item of the statement got its expected answer."""
    if key is not None:
        store(key, "proved", replace=True)


def lookup_hint(key):
    """Untrusted scheduling hint (never a proof): see store_hint."""
    value = lookup(f"hint\0{key}")
    return value.get("hint") if isinstance(value, dict) else None


def store_hint(key, value):
    store(f"hint\0{key}", {"hint": value}, replace=False)


def record_answer(keys, answer, timeout_ms):
    """Decided answers overwrite; an unknown keeps the largest budget tried."""
    if keys is None:
        return
    if answer in ("sat", "unsat"):
        store(keys, answer, replace=True)
        return
    value = lookup(keys)
    if value in ("sat", "unsat"):
        return
    budgets = _local_unknown_budgets()
    for k in _key_list(keys):
        budgets[k] = max(timeout_ms, budgets.get(k, 0))
    budget = max(timeout_ms, value.get("unknown", 0) if isinstance(value, dict) else 0)
    store(keys, {"unknown": budget}, replace=True)
