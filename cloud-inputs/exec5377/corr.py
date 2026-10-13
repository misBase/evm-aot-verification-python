"""Trie-decomposed evm_disjoint / x86_coverage on dumped path conditions, through the real _check.

usage: corr.py STEM 'BlockSpecialization(...)' DIR [what=disjoint,coverage] [orig_sample=N]   (cwd = snapshot)
DIR/paths.smt2 = [premise, evm conditions..., x86 conditions...], DIR/paths_meta.json = counts.
"""
import json
import os
import random
import sys
from pathlib import Path
from time import monotonic

sys.path.insert(0, ".")
os.environ.setdefault("BLOCK_PAIR_WORKERS", "1")
from z3 import And, Not, Or, is_and, is_not, is_true, parse_smt2_file, simplify, is_false  # noqa: E402
from verification import block_parallel as bp  # noqa: E402
from verification.block_specialization import BlockSpecialization  # noqa: E402,F401

stem, text, d = sys.argv[1], sys.argv[2], Path(sys.argv[3])
what = sys.argv[4].split(",") if len(sys.argv) > 4 else ["disjoint", "coverage"]
orig_sample = int(sys.argv[5]) if len(sys.argv) > 5 else 0
meta = json.loads((d / "paths_meta.json").read_text())
A = list(parse_smt2_file(str(d / "paths.smt2")))
assert len(A) == 1 + meta["evm"] + meta["x86"], (len(A), meta)
premise, evm, x86 = A[0], A[1:1 + meta["evm"]], A[1 + meta["evm"]:]

OPTIONS = dict(gas_check="full", gas_budget=1_000_000_000, num_inputs=0, timeout_ms=30000, node_seconds=3600,
               first_pass_node_seconds=None, max_parameter_values=32, max_depth=400, max_instances=8192,
               wall_seconds=6 * 3600, summaries=True)
bp.load_worker(stem, OPTIONS, [eval(text)])
prover = bp._WORKER["setup"].prover
prover.deadline = None


def conj(c):
    return list(c.children()) if is_and(c) else [c]


def complementary(a, b):
    return (is_not(a) and a.arg(0).eq(b)) or (is_not(b) and b.arg(0).eq(a)) or is_false(simplify(And(a, b)))


def check(name, formula):
    records = []
    t = monotonic()
    ok = prover._check(name, formula, records)
    return ok, records[-1].answer if records else "?", monotonic() - t


def lcp(a, b):
    n = 0
    while n < min(len(a), len(b)) and a[n].eq(b[n]):
        n += 1
    return n


if "disjoint" in what:
    paths = [conj(c) for c in evm]
    n = len(paths)
    groups, fallback = {}, []
    for i in range(n):
        for k in range(i + 1, n):
            L = lcp(paths[i], paths[k])
            if L == len(paths[i]) or L == len(paths[k]):
                fallback.append((i, k))
                continue
            key = (tuple(c.get_id() for c in paths[i][:L]), paths[i][L].get_id(), paths[k][L].get_id())
            groups.setdefault(key, (paths[i][:L], paths[i][L], paths[k][L], []))[3].append((i, k))
    t0 = monotonic()
    trivial = solved = 0
    worst = 0.0
    for prefix, a, b, members in groups.values():
        if complementary(a, b):
            ok, ans, dt = check("evm_disjoint_local", And(a, b))
            trivial += 1
        else:
            ok, ans, dt = check("evm_disjoint_local", And(premise, *prefix, a, b))
            solved += 1
        worst = max(worst, dt)
        if not ok:
            print("LOCAL FAILED", ans, len(members), flush=True)
    for i, k in fallback:
        ok, ans, dt = check(f"evm_disjoint_{i}_{k}", And(premise, evm[i], evm[k]))
        print("fallback", i, k, ans, f"{dt:.1f}s", flush=True)
    print("evm_disjoint trie: pairs", n * (n - 1) // 2, "groups", len(groups), "complementary", trivial,
          "with-prefix", solved, "fallback", len(fallback), f"total {monotonic() - t0:.1f}s worst {worst:.2f}s",
          flush=True)
    if orig_sample:
        pairs = [(i, k) for i in range(n) for k in range(i + 1, n)]
        random.seed(0)
        sample = random.sample(pairs, min(orig_sample, len(pairs)))
        t0 = monotonic()
        for i, k in sample:
            check(f"evm_disjoint_{i}_{k}", And(premise, evm[i], evm[k]))
        dt = monotonic() - t0
        print("original evm_disjoint sample", len(sample), f"{dt:.1f}s", "extrapolated",
              f"{dt / len(sample) * len(pairs):.0f}s", flush=True)

if "mapping" in what:
    # _correspondence's per-x86 proposal loop: original (fresh solver per path, 3s) vs one
    # incremental solver over [premise, conjuncts...] (a proposal only: any model is fine).
    from z3 import sat, unsat
    from verification.block_equivalence import _solver
    sys.path.insert(0, str(Path(__file__).parent))
    from reach_modes import PrefixSolver

    def hits_of(model):
        hs = [i for i, e in enumerate(evm) if is_true(model.eval(e, model_completion=True))]
        return hs[0] if len(hs) == 1 else "all"

    t0 = monotonic()
    orig = []
    for x in x86:
        q = And(premise, x)
        s = _solver(3000, q)
        s.add(q)
        a = s.check()
        orig.append(None if a == unsat else (hits_of(s.model()) if a == sat else "unknown"))
    t_orig = monotonic() - t0
    t0 = monotonic()
    ps, inc = PrefixSolver(), []
    for x in x86:
        a = ps.check([premise] + conj(x), 3000, {})
        inc.append(None if a == unsat else (hits_of(ps.solver.model()) if a == sat else "unknown"))
    t_inc = monotonic() - t0
    same = sum(1 for a, b in zip(orig, inc) if a == b)
    print("mapping original", f"{t_orig:.1f}s", "incremental", f"{t_inc:.1f}s", "same", same, "of", len(x86),
          "orig unknown", orig.count("unknown"), "inc unknown", inc.count("unknown"), flush=True)
    print("orig", orig, flush=True)
    print("inc ", inc, flush=True)

if "coverage" in what:
    paths = [conj(c) for c in x86]
    # trie: node = (prefix length, prefix ids) -> children edge conjuncts, leaf flag
    nodes = {}
    for p in paths:
        for L in range(len(p) + 1):
            key = tuple(c.get_id() for c in p[:L])
            node = nodes.setdefault(key, {"prefix": p[:L], "edges": {}, "leaf": False})
            if L == len(p):
                node["leaf"] = True
            else:
                node["edges"].setdefault(p[L].get_id(), p[L])
    t0 = monotonic()
    stats = {"leaf": 0, "complementary": 0, "true_or_repeat": 0, "solved": 0}
    slow = []
    for key, node in nodes.items():
        edges = list(node["edges"].values())
        if node["leaf"] or not edges:
            stats["leaf"] += 1
            continue
        ids = set(key)
        if len(edges) == 1 and (is_true(edges[0]) or edges[0].get_id() in ids):
            stats["true_or_repeat"] += 1
            continue
        if len(edges) == 2 and complementary(*edges):
            stats["complementary"] += 1
            ok, ans, dt = check("x86_coverage_local", Not(Or(*edges)))
        else:
            stats["solved"] += 1
            ok, ans, dt = check("x86_coverage_local", And(premise, *node["prefix"], Not(Or(*edges))))
        if dt > 1 or not ok:
            slow.append((len(key), len(edges), ans, round(dt, 1)))
        if not ok:
            print("COVERAGE LOCAL FAILED", len(key), len(edges), ans, flush=True)
    print("x86_coverage trie: nodes", len(nodes), stats, f"total {monotonic() - t0:.1f}s", "slow", slow, flush=True)

if "coverage_factored" in what:
    # Or(And(p_i)) rewritten by distributivity along the conjunct trie (equivalent formula).
    from z3 import BoolVal
    from verification.block_equivalence import solve_query
    paths = [conj(c) for c in x86]

    def factor(group, depth):
        # group: list of conjunct lists sharing the first `depth` conjuncts
        if any(len(p) == depth for p in group):
            return BoolVal(True)
        children = {}
        for p in group:
            children.setdefault(p[depth].get_id(), (p[depth], []))[1].append(p)
        alts = [And(e, factor(g, depth + 1)) for e, g in children.values()]
        return alts[0] if len(alts) == 1 else Or(*alts)

    sys.setrecursionlimit(100000)
    F = factor(paths, 0)
    t0 = monotonic()
    a = solve_query(simplify(And(premise, Not(F))), 30000)
    print("x86_coverage factored solve_query(30s):", a, f"{monotonic() - t0:.1f}s", flush=True)
    from verification.block_equivalence import abstract_nonlinear_mul
    for label, G in (("factored", F), ("flat", Or(*x86))):
        t0 = monotonic()
        relaxed, changed = abstract_nonlinear_mul(And(premise, Not(G)))
        a = solve_query(relaxed, 60000) if changed else "unchanged"
        print("x86_coverage", label, "mul->UF solve_query(60s):", a, f"{monotonic() - t0:.1f}s", flush=True)
    if os.environ.get("FACTORED_CHECK"):
        ok, ans, dt = check("x86_coverage", And(premise, Not(F)))
        print("x86_coverage factored _check:", ans, f"{dt:.1f}s", flush=True)

if "coverage_inc" in what:
    # Same trie obligations, each decided by one incremental solver (rlimit-bounded, 30s budget).
    from z3 import unsat
    sys.path.insert(0, str(Path(__file__).parent))
    from reach_modes import PrefixSolver
    paths = [conj(c) for c in x86]
    nodes = {}
    for p in paths:
        for L in range(len(p) + 1):
            key = tuple(c.get_id() for c in p[:L])
            node = nodes.setdefault(key, {"prefix": p[:L], "edges": {}, "leaf": False})
            if L == len(p):
                node["leaf"] = True
            else:
                node["edges"].setdefault(p[L].get_id(), p[L])
    t0 = monotonic()
    ps = PrefixSolver()
    answers, worst = {}, 0.0
    for key, node in nodes.items():
        edges = list(node["edges"].values())
        if node["leaf"] or not edges:
            continue
        if len(edges) == 1 and (is_true(edges[0]) or edges[0].get_id() in set(key)):
            continue
        t = monotonic()
        if len(edges) == 2 and complementary(*edges):
            a = "unsat"
        else:
            a = str(ps.check([premise, *node["prefix"], Not(Or(*edges))], 30000, {}))
        worst = max(worst, monotonic() - t)
        answers[a] = answers.get(a, 0) + 1
    print("x86_coverage trie incremental:", answers, f"total {monotonic() - t0:.1f}s worst {worst:.1f}s", flush=True)
