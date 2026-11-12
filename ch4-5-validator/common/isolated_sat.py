"""Checks whose bit-blasting can exceed Z3's own memory counters.

The ordinary child returns only its answer. A separate restricted scalar
witness search transports assignments that the parent checks against its exact
original formula; a missed witness never supplies an UNSAT result.
An OS memory limit, wall timeout, or abnormal exit means unknown.

An undecided summary entry never asserts satisfiability: block entry/domain
nonemptiness and the hit's raw coverage/effect obligations remain mandatory.
"""
from pathlib import Path
from contextlib import contextmanager
import json
import os
import subprocess
import sys
from time import monotonic

# Address-space headroom of one isolated child, still at most half of the node's free budget.
# PoolManager 18089 x86_maps_0_0 needs ~2.1 GB: unknown under the default 1 GiB, unsat in seconds at 4 GiB.
ISOLATED_MEMORY_MB = int(os.environ.get("BLOCK_ISOLATED_MEMORY_MB", "1024"))


def _child_memory_mb():
    from common.node_monitor import memory_headroom_mb
    headroom = memory_headroom_mb()
    return ISOLATED_MEMORY_MB if headroom is None else max(1, min(ISOLATED_MEMORY_MB, headroom // 2))


def _power_of_two(term):
    """A literal 2^k divisor: Z3 rewrites the division into an extract, no circuit."""
    from z3 import is_bv_value
    if not is_bv_value(term):
        return False
    value = term.as_long()
    return value > 0 and value & (value - 1) == 0


def expensive_bitblast(formula):
    """Route million-gate symbolic multiplication/division circuits to isolation."""
    from z3 import is_app, is_bv, is_bv_value, is_quantifier, Z3_OP_UNINTERPRETED
    seen, work, cost = set(), [formula], 0
    while work:
        term = work.pop()
        if term.get_id() in seen:
            continue
        seen.add(term.get_id())
        if is_quantifier(term):
            work.append(term.body())
        elif is_app(term):
            args = term.children()
            name = term.decl().name()
            if is_bv(term) and term.decl().kind() != Z3_OP_UNINTERPRETED and len(args) >= 2:
                symbolic = sum(not is_bv_value(arg) for arg in args)
                if name == "bvmul" and symbolic >= 2:
                    cost += term.size() ** 2
                elif (name.startswith(("bvudiv", "bvurem", "bvsdiv", "bvsrem", "bvsmod"))
                        and not is_bv_value(args[0]) and not _power_of_two(args[1])):
                    # A literal divisor still blasts a full divider: simplify turns
                    # mulmod(a, b, 2^256-1) into a 512-bit URem by a literal (PoolManager
                    # FullMath blocks: 2.8 GB in the parent's reachability check).
                    cost += 4 * term.size() ** 2
                if cost >= 1_000_000:
                    return True
            work.extend(args)
    return False


def _run_isolated(formula, end, *, blast=False, rlimit=None, pure_bv=False, scalar_model=False,
                  refute_probe=False):
    from verification.block_equivalence import _to_smt2, _parse_transport
    memory_mb = _child_memory_mb()
    if refute_probe:
        if blast or pure_bv or scalar_model or type(rlimit) is not int or rlimit <= 0:
            raise ValueError("refutation probe requires its original positive resource budget")
        from z3 import Solver
        meter = Solver()
        before = meter.statistics().get_key_value("rlimit count")
    text = _to_smt2(formula)  # Reject or repair binder capture before crossing the process boundary.
    _, expected_alpha = _parse_transport(text, formula.ctx)
    if refute_probe:
        # int(): past 2^32 Z3 reports the count as a double, and a float budget breaks the child's argv.
        rlimit -= int(meter.statistics().get_key_value("rlimit count") - before)
        if rlimit <= 0:
            return None  # Serialization may overshoot; it cannot supply an accepted answer.
        memory_mb = _child_memory_mb()
    remaining = end - monotonic()
    if remaining <= 0:
        return None
    command = [sys.executable, str(Path(__file__).resolve()), str(max(1, int(remaining * 1000))),
               str(memory_mb), str(int(blast)), str(0 if rlimit is None else rlimit), str(int(pure_bv))]
    if scalar_model:
        command.append("1")
    if refute_probe:
        command.extend(("0", "1", str(end)))  # scalar mode, refutation mode, absolute deadline
    result = subprocess.run(command, input=text, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, timeout=remaining)
    if monotonic() >= end:
        return None
    if result.returncode == 0:
        payload = json.loads(result.stdout)
        if (type(payload) is not dict or set(payload) != {"parsed_alpha", "payload"}
                or payload["parsed_alpha"] != expected_alpha):
            raise ValueError("child parsed statement digest mismatch")
        answer = payload["payload"]
        if scalar_model:
            if type(answer) is not dict:
                raise ValueError("invalid scalar transport payload")
            result.stdout = json.dumps(answer)
        else:
            if type(answer) is not str or answer not in ("sat", "unsat", "unknown"):
                raise ValueError("invalid answer transport payload")
            result.stdout = answer
    return result


def isolated_sat(formula, timeout_ms, *, blast=False, rlimit=None, pure_bv=False, refute_probe=False):
    """Solve without exposing the proof worker to the child's allocations.

    The Linux child gets at most 1 GiB beyond its own initial virtual size,
    also bounded by half the running node's remaining memory. This is an AS
    limit, not a limit derived from the parent's RSS. Unsupported OS limits
    fail closed as unknown; production proof workers run on Linux.
    """
    end = monotonic() + timeout_ms / 1000
    from z3 import Z3Exception
    from common.node_monitor import check_abort
    check_abort()
    try:
        result = _run_isolated(formula, end, blast=blast, rlimit=rlimit, pure_bv=pure_bv,
                               refute_probe=refute_probe)
        answer = result.stdout.strip() if result is not None and result.returncode == 0 else "unknown"
        answer = answer if answer in ("sat", "unsat", "unknown") else "unknown"
        if refute_probe:
            if result is not None and getattr(result, "stderr", "").strip():
                print("refute_probe child: " + result.stderr.strip()[:300], file=sys.stderr)
            if answer != "unsat" or monotonic() >= end:
                answer = "unknown"  # Only a complete, timely refutation of the original F transfers.
    except (OSError, MemoryError, ValueError, RecursionError, Z3Exception, subprocess.TimeoutExpired):
        answer = "unknown"
    check_abort()
    return answer


def _scalar_constants(formula, end):
    from z3 import Z3_OP_UNINTERPRETED, is_app, is_bool, is_bv, is_quantifier
    if not is_bool(formula):
        raise ValueError("not a Boolean formula")
    seen, declarations, work = set(), {}, [formula]
    while work:
        if monotonic() >= end:
            raise ValueError("witness budget expired")
        term = work.pop()
        if term.get_id() in seen:
            continue
        seen.add(term.get_id())
        if is_quantifier(term) or not is_app(term):
            raise ValueError("binder or open variable")
        if not (is_bool(term) or is_bv(term)):
            raise ValueError("non-scalar term")
        if term.decl().kind() == Z3_OP_UNINTERPRETED:
            if term.num_args():
                raise ValueError("nonconstant UF")
            declarations[term.decl().get_id()] = term
        work.extend(term.children())
    constants = list(declarations.values())
    if len({_scalar_signature(t) for t in constants}) != len(constants):
        raise ValueError("ambiguous scalar signatures")
    return constants


def _scalar_signature(term):
    from z3 import is_bv
    return (str(term.decl().name()), "BV" if is_bv(term) else "Bool", term.size() if is_bv(term) else 0)


def _scalar_model(formula, constants, payload, end):
    from z3 import BitVecVal, BoolVal, Model, is_true
    if type(payload) is not dict or set(payload) != {"answer", "constants"} or payload["answer"] != "sat":
        raise ValueError("not a scalar SAT model")
    rows = payload["constants"]
    if type(rows) is not list or len(rows) != len(constants):
        raise ValueError("missing or extra scalar assignments")
    expected = {_scalar_signature(t): t for t in constants}
    values = {}
    for row in rows:
        if monotonic() >= end:
            raise ValueError("witness budget expired")
        if type(row) is not dict or set(row) != {"name", "sort", "width", "value"}:
            raise ValueError("malformed scalar assignment")
        if type(row["name"]) is not str or type(row["sort"]) is not str or type(row["width"]) is not int:
            raise ValueError("invalid scalar signature")
        signature = (row["name"], row["sort"], row["width"])
        if signature not in expected or signature in values:
            raise ValueError("unknown or repeated scalar signature")
        value = row["value"]
        if row["sort"] == "BV":
            if type(value) is not int or not 0 <= value < 2 ** row["width"]:
                raise ValueError("invalid BV value")
            values[signature] = BitVecVal(value, row["width"], ctx=formula.ctx)
        else:
            if type(value) is not bool:
                raise ValueError("invalid Boolean value")
            values[signature] = BoolVal(value, ctx=formula.ctx)
    if values.keys() != expected.keys():
        raise ValueError("missing scalar assignment")
    model = Model(ctx=formula.ctx)
    for signature, value in values.items():
        model.update_value(expected[signature], value)
    # The child is only a witness source, not an authority on satisfiability.
    if not is_true(model.eval(formula, model_completion=True)) or monotonic() >= end:
        raise ValueError("model does not satisfy original formula within budget")
    return model


def isolated_small_mul_model(formula, timeout_ms):
    """Return only an original-valid scalar SAT witness, or None on any miss.

    The one-bit operand restriction is existential search, never an UNSAT
    argument. All candidate solving/model computation stays in the OS-limited
    child. The whole input must be ground, binder-free and pure Bool/BV with
    no nonconstant UF; the parent reconstructs/checks every original constant.
    """
    end = monotonic() + timeout_ms / 1000
    from z3 import Z3Exception
    from common.node_monitor import check_abort
    check_abort()
    model = None
    try:
        constants = _scalar_constants(formula, end)
        result = _run_isolated(formula, end, scalar_model=True)
        if result is not None and result.returncode == 0 and monotonic() < end:
            model = _scalar_model(formula, constants, json.loads(result.stdout), end)
    except (OSError, MemoryError, ValueError, RecursionError, Z3Exception, subprocess.TimeoutExpired):
        pass
    check_abort()
    return model if monotonic() < end else None


def _small_mul_payload(formula, end):
    from z3 import BitVecSort, SolverFor, ZeroExt, is_bv, is_true, sat, simplify, substitute
    from common.fresh_symbols import FreshSymbols
    from verification.block_equivalence import _nonlinear_mul_terms
    constants = _scalar_constants(formula, end)
    constant_ids = {t.get_id() for t in constants}
    fresh = FreshSymbols(formula)
    roots, seen, work = {}, set(), list(_nonlinear_mul_terms(formula))
    while work:
        if monotonic() >= end:
            return None
        term = work.pop()
        if term.get_id() in seen:
            continue
        seen.add(term.get_id())
        # Eligibility already rejected every nonconstant UF/binder/open Var.
        if term.get_id() in constant_ids and is_bv(term):
            roots[term.get_id()] = term
        work.extend(term.children())
    if not roots:
        return None
    pairs = [(r, ZeroExt(r.size() - 1, fresh.const(BitVecSort(1, ctx=formula.ctx), "small_operand")))
             for r in roots.values() if r.size() > 1]
    query = simplify(substitute(formula, *pairs), blast_select_store=True)
    remaining = int((end - monotonic()) * 1000)
    if remaining <= 0:
        return None
    solver = SolverFor("QF_AUFBV")
    solver.set(timeout=min(remaining, 2**32 - 1))
    solver.add(query)
    if solver.check() != sat:
        return None
    model = solver.model()
    for root, image in pairs:
        model.update_value(root, model.eval(image, model_completion=True))
    if not is_true(model.eval(formula, model_completion=True)):
        return None
    rows = []
    for term in constants:
        name, sort, width = _scalar_signature(term)
        value = model.eval(term, model_completion=True)
        rows.append(dict(name=name, sort=sort, width=width, value=value.as_long() if sort == "BV" else is_true(value)))
    return dict(answer="sat", constants=rows) if monotonic() < end else None


class _ProbeBudgetExceeded(Exception):
    pass


class _ProbeBudget:
    """One native-context resource meter; preparation overruns are rejected after they run."""

    def __init__(self, end, resources):
        from z3 import Solver
        self.meter = Solver()
        self.initial = self.meter.statistics().get_key_value("rlimit count")
        self.end, self.maximum = end, resources
        self.phase_end, self.phase_maximum = end, resources

    def spent(self):
        return int(self.meter.statistics().get_key_value("rlimit count") - self.initial)  # see _run_isolated

    def remaining(self):
        wall, resources = int((self.phase_end - monotonic()) * 1000), self.phase_maximum - self.spent()
        if wall <= 0 or resources <= 0:
            raise _ProbeBudgetExceeded("shared final probe budget expired")
        return wall, resources

    def call(self, function, *args, **kwargs):
        self.remaining()
        result = function(*args, **kwargs)
        self.remaining()
        return result


class _ProbeSolver:
    def __init__(self, solver, budget, timeout=0):
        self.solver, self.budget = solver, budget
        self.limits = {"timeout": timeout}

    def __getattr__(self, name):
        return getattr(self.solver, name)

    def set(self, *args, **kwargs):
        values = dict(zip(args[::2], args[1::2]))
        values.update(kwargs)
        for name in ("timeout", "rlimit"):
            old, new = self.limits.get(name, 0), values.get(name, 0)
            if old:
                values[name] = min(old, new) if new else old
        self.limits.update(values)
        return self.budget.call(self.solver.set, **values)

    def add(self, *args):
        return self.budget.call(self.solver.add, *args)

    def check(self, *args):
        wall, resources = self.budget.remaining()
        timeout, rlimit = self.limits.get("timeout", 0), self.limits.get("rlimit", 0)
        self.solver.set(timeout=min(timeout, wall) if timeout else wall,
                        rlimit=min(rlimit, resources) if rlimit else resources)
        return self.budget.call(self.solver.check, *args)


@contextmanager
def _probe_adapters(budget):
    """Only this one-shot child changes module-local factories, never Solver.check."""
    import verification.block_equivalence as be
    import common.isolated_sat as isolated
    original = be._solver, be.solve_query, be.solve_pure_bv
    private_query = be._solve_query
    modules = {sys.modules[__name__], isolated}  # __main__ and its imported alias in a real child
    runners = [(module, module._run_isolated) for module in modules]
    cache_env = os.environ.pop("BLOCK_PROOF_CACHE", None)

    def factory(timeout_ms, formula=None):
        return _ProbeSolver(budget.call(original[0], timeout_ms, formula), budget, timeout_ms)

    def query(formula, timeout_ms, trust_unknown=True):
        answer = budget.call(private_query, formula, timeout_ms)
        return answer if answer in ("sat", "unsat", "unknown") else "unknown"

    def pure_bv(formula, timeout_ms):
        solver = _ProbeSolver(be.Then("simplify", "ackermannize_bv", "bit-blast", "sat").solver(), budget)
        solver.set(timeout=timeout_ms)
        solver.add(formula)
        return str(solver.check())

    def no_nested(*args, **kwargs):
        raise RuntimeError("nested isolation refused: its resources cannot join this budget")

    be._solver, be.solve_query, be.solve_pure_bv = factory, query, pure_bv
    for module, _ in runners:
        module._run_isolated = no_nested
    try:
        yield
    finally:
        be._solver, be.solve_query, be.solve_pure_bv = original
        for module, runner in runners:
            module._run_isolated = runner
        if cache_env is not None:
            os.environ["BLOCK_PROOF_CACHE"] = cache_env


def _refute_probe(formula, budget):
    from z3 import SolverFor, simplify, unsat
    import verification.block_equivalence as be
    try:
        with _probe_adapters(budget):
            wall, resources = budget.remaining()
            budget.phase_end = min(budget.end, monotonic() + wall / 2000)
            budget.phase_maximum = budget.spent() + resources // 2
            try:
                relaxed, changed = budget.call(be.value_cut, formula)  # products and div/rem as congruent UFs
                if changed:
                    query = budget.call(simplify, relaxed, blast_select_store=True)
                    solver = _ProbeSolver(SolverFor("QF_AUFBV"), budget)
                    solver.add(query)
                    if solver.check() == unsat:
                        return "unsat"
            except _ProbeBudgetExceeded:
                pass  # The potential gets only what the whole original slot still has.
            budget.phase_end, budget.phase_maximum = budget.end, budget.maximum
            _, answer, records = budget.call(be.refute_over_bounded_potential, formula, budget.remaining()[0])
            return "unsat" if answer == "unsat" and all(record.proved for record in records) else "unknown"
    except Exception as exc:
        print(f"refute_probe unknown: {type(exc).__name__}: {str(exc)[:240]}", file=sys.stderr)
        return "unknown"


def _worker():
    import resource
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
    from z3 import And, SolverFor, Then, parse_smt2_string, simplify
    from verification.block_equivalence import _solve_query, _parse_transport

    timeout_ms, memory_mb, blast, rlimit = map(int, sys.argv[1:5])
    pure_bv = len(sys.argv) > 5 and int(sys.argv[5])
    scalar_model = len(sys.argv) > 6 and int(sys.argv[6])
    refute_probe = len(sys.argv) > 7 and int(sys.argv[7])
    end = monotonic() + timeout_ms / 1000
    if refute_probe:
        end = min(end, float(sys.argv[8]))
    parsed_alpha = None
    def emit(payload):
        print(json.dumps(dict(parsed_alpha=parsed_alpha, payload=payload)), flush=True)
    try:
        # Set the limit before reading/parsing the query. A fresh interpreter
        # avoids forking the proof worker while its NodeMonitor thread is live.
        pages = int(Path("/proc/self/statm").read_text().split()[0])
        total = pages * os.sysconf("SC_PAGE_SIZE") + memory_mb * 2**20
        _, hard = resource.getrlimit(resource.RLIMIT_AS)
        resource.setrlimit(resource.RLIMIT_AS, (total if hard == resource.RLIM_INFINITY else min(total, hard), hard))
        if refute_probe:
            if blast or pure_bv or scalar_model or rlimit <= 0:
                raise ValueError("incompatible refutation probe modes")
            os.environ.pop("BLOCK_PROOF_CACHE", None)
            budget = _ProbeBudget(end, rlimit)
            query, parsed_alpha = budget.call(_parse_transport, sys.stdin.read())
            query = query.arg(0) if query.num_args() == 1 else query  # Original refutation input shape.
            answer = budget.call(_refute_probe, query, budget)
            emit("unsat" if answer == "unsat" else "unknown")
            return
        query, parsed_alpha = _parse_transport(sys.stdin.read())
        if scalar_model:
            emit(_small_mul_payload(query, end) or {"answer": "unknown"})
            return
        if blast:
            query = simplify(query, blast_select_store=True)
        if pure_bv:
            solver = Then("simplify", "ackermannize_bv", "bit-blast", "sat").solver()
            solver.set(timeout=timeout_ms)
            solver.add(query)
            answer = str(solver.check())
        elif rlimit:
            solver = SolverFor("QF_AUFBV")
            solver.set(timeout=min(timeout_ms, 2**32 - 1), rlimit=min(rlimit, 2**32 - 1))
            solver.add(query)
            answer = str(solver.check())
        else:
            answer = _solve_query(query, timeout_ms)
        emit(answer if answer in ("sat", "unsat") else "unknown")
    except Exception:
        emit("unknown")


if __name__ == "__main__":
    _worker()
