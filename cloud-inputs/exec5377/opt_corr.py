r"""Prototype (monkeypatch) of the correspondence / coverage changes.

P3 evm_disjoint by divergence: pairs (i, k) whose conjunct lists first differ at
   position L with edges a, b share the obligation  premise /\ prefix_L /\ a /\ b,
   a sub-conjunction of premise /\ cond_i /\ cond_k (its UNSAT implies the pair's).
   Syntactically complementary edges (x, Not x) need only  a /\ b.  Pairs where one
   list is a prefix of the other keep the original query.  Each record still carries
   its own name evm_disjoint_i_k (BlockTheorem._pairs_covered is unchanged).
P4 x86 -> EVM mapping proposals from ONE incremental solver over
   [premise, conjuncts of x86 path j] (a proposal only, never a proof).
P5 {evm,x86}_coverage: try the bvmul->UF refutation (_retry_over_nonlinear_mul,
   already a _check route) before the route cascade.
"""
from dataclasses import replace
from time import monotonic

from z3 import And, is_and, is_false, is_not, is_true, sat, simplify, unsat

import verification.block_equivalence as be
from verification.block_equivalence import (ProofBudgetExceeded, _QUICK_EXACT_MS, propose_from_siblings, Obligation)
from reach_modes import PrefixSolver

P = be.BlockEquivalenceProver


def conj(c):
    return list(c.children()) if is_and(c) else [c]


def complementary(a, b):
    return (is_not(a) and a.arg(0).eq(b)) or (is_not(b) and b.arg(0).eq(a)) or is_false(simplify(And(a, b)))


def disjoint_obligations(premise, conditions):
    """[(names, formula)]: one shared sub-conjunction obligation per divergence."""
    paths = [conj(c) for c in conditions]
    n, groups, out = len(paths), {}, []
    for i in range(n):
        for k in range(i + 1, n):
            a, b = paths[i], paths[k]
            L = 0
            while L < min(len(a), len(b)) and a[L].eq(b[L]):
                L += 1
            if L == len(a) or L == len(b):
                out.append(([f"evm_disjoint_{i}_{k}"], And(premise, conditions[i], conditions[k])))
                continue
            key = (tuple(c.get_id() for c in a[:L]), a[L].get_id(), b[L].get_id())
            if key not in groups:
                formula = And(a[L], b[L]) if complementary(a[L], b[L]) else And(premise, *a[:L], a[L], b[L])
                groups[key] = ([], formula)
                out.append(groups[key])
            groups[key][0].append(f"evm_disjoint_{i}_{k}")
    return out


def _correspondence(self, evm, x86, premise, records):
    n, m = len(evm), len(x86)
    if n < 2 or n * m <= n * (n - 1) // 2 + 2 * m:
        return ()
    trial = []
    for names, formula in disjoint_obligations(premise, [e.condition for e in evm]):
        sub = []
        if not self._check(names[0], formula, sub):
            return ()
        trial.extend(replace(sub[-1], name=name) for name in names)
    records.extend(trial)
    correspondence, unknown = [], []
    solver = PrefixSolver()
    for j, x in enumerate(x86):
        # P4b: the executor's last model of this path, if it also satisfies the premise.
        m = WIT.get(x.condition.get_id())
        if m is not None and is_true(m.eval(And(premise, x.condition), model_completion=True)):
            hits = [i for i, e in enumerate(evm) if is_true(m.eval(e.condition, model_completion=True))]
            if len(hits) == 1:
                WSTATS["hit"] += 1
                correspondence.append(hits[0])
                continue
        WSTATS["miss"] += 1
        budget = _QUICK_EXACT_MS
        if self.deadline is not None:
            budget = min(budget, int((self.deadline - monotonic()) * 1000))
        if budget <= 0:
            raise ProofBudgetExceeded("proof wall budget exhausted")
        answer = solver.check([premise, *conj(x.condition)], budget, {})
        if answer not in (sat, unsat):
            unknown.append(j)
        if answer == unsat:
            correspondence.append(None)
            continue
        target = "all"
        if answer == sat:
            model = solver.solver.model()
            hits = [i for i, e in enumerate(evm) if is_true(model.eval(e.condition, model_completion=True))]
            if len(hits) == 1:
                target = hits[0]
        correspondence.append(target)
    proposed = propose_from_siblings(correspondence, x86) if unknown else ()
    for j in unknown:
        if proposed[j] == "all" and self._empty_by_bvabs(premise, x86[j]):
            correspondence[j] = None
    print("[opt_corr] mapping witness", WSTATS, flush=True)
    return tuple(correspondence)


WIT, WSTATS, KEEP = {}, {"hit": 0, "miss": 0}, []


def install(log=print):
    from x86_64.cfg_executor import X86SymbolicExecutor
    inner_execute = X86SymbolicExecutor.execute

    def execute(self, *a, **k):
        finals = inner_execute(self, *a, **k)
        for st in list(finals) + list(getattr(self, "cut_states", [])):
            c = st.get_constraints()
            if c._witness is not None:
                cond = c.as_bool()
                WIT[cond.get_id()] = c._witness
                KEEP.append(cond)
        return finals
    X86SymbolicExecutor.execute = execute
    inner_check = P._check

    def check(self, name, formula, records, *, expected="unsat", split=True):
        if expected == "unsat" and name.endswith("_coverage"):
            started = monotonic()
            proved, answer, _ = self._retry_over_nonlinear_mul(formula, "unknown")
            log("coverage mul-first", name, answer, f"{monotonic() - started:.1f}s")
            if answer == "unsat":
                record = Obligation(name, proved.sexpr(), "unsat", expected, monotonic() - started)
                records.append(record)
                return True
        return inner_check(self, name, formula, records, expected=expected, split=split)

    P._check = check
    P._correspondence = _correspondence
