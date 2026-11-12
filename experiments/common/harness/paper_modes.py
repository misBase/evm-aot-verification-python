"""Paper-mode switches: patch the frozen code in-process for an ablation.

Nothing is patched unless `apply()` is called, so the frozen snapshot's own code
paths stay byte-identical. Patches replace a function object everywhere it is bound
(including `from x import f as _f` aliases), so call `apply()` after the importers
below are loaded.

Modes:
  naive_arith_only B4a: Alive2-style DIV/MOD/SDIV/SMOD/ADDMOD on both sides
  no_div64_hint    B4c: omit only the DIV64 quotient-high-bits lemma
  no_div_bridge    B4b: verified_div_bridges returns no bridges
  no_path_ite      B4d: single-instruction harness without path-aware ITE pruning
  naive_arith      legacy combined arithmetic + broad hint removal
  no_arith_hints   legacy broad hint removal (not the V2-design B4c arm)
  bounded          A3 (Alive2 bounded semantics): accept incomplete path coverage,
                   check equivalence on the explored paths, record the reasons
"""
import importlib
import sys

from z3 import BitVecVal, BoolVal, Extract, If, SRem, UDiv, URem, ZeroExt

TRUNCATED = []  # coverage failures accepted under "bounded"
APPLIED = []

_IMPORTERS = (
    "common.arithmetic", "common.div_bridge", "evm_ir.semantics",
    "x86_64.go_function_semantics", "x86_64.summaries.div", "x86_64.summaries.sdiv",
    "x86_64.summaries.smod", "verification.equivalence_context",
    "verification.equivalence_paths", "verification.program_verifier",
)
_PREFIXES = ("common", "evm_ir", "x86_64", "verification", "state", "tests")


def _replace_everywhere(original, replacement):
    count = 0
    for name, module in list(sys.modules.items()):
        if module is None or not name.startswith(_PREFIXES):
            continue
        for attr, value in list(vars(module).items()):
            if value is original:
                setattr(module, attr, replacement)
                count += 1
    if not count:
        raise RuntimeError(f"paper mode: {original.__name__} is bound nowhere")
    return count


def _zero(value):
    return BitVecVal(0, 256, ctx=value.ctx)


def _div(a, b):
    return If(b == 0, _zero(a), UDiv(a, b))


def _mod(a, b):
    return If(b == 0, _zero(a), URem(a, b))


def _sdiv(a, b):
    return If(b == 0, _zero(a), a / b)  # z3 `/` on bit-vectors is bvsdiv; MIN/-1 wraps like EVM


def _smod(a, b):
    return If(b == 0, _zero(a), SRem(a, b))  # EVM SMOD takes the dividend's sign, as bvsrem


def _addmod(a, b, m):
    total = URem(ZeroExt(1, a) + ZeroExt(1, b), ZeroExt(1, m))
    return If(m == 0, _zero(a), Extract(255, 0, total))


def _naive_arith(arith):
    for name, naive in (("div_semantics", _div), ("mod_semantics", _mod),
                        ("sdiv_semantics", _sdiv), ("smod_semantics", _smod),
                        ("addmod_semantics", _addmod)):
        _replace_everywhere(getattr(arith, name), naive)


def _no_hints(arith):
    _replace_everywhere(arith.x86_div64_quotient_fits_assumption, lambda a, b: BoolVal(True))
    _replace_everywhere(arith.eq_borrow_chain_assumption, lambda a, b: BoolVal(True))
    for name in ("sdiv_speedup_assumptions", "smod_speedup_assumptions", "addmod_speedup_assumptions"):
        _replace_everywhere(getattr(arith, name), lambda *args: [])


def apply(modes):
    modes = [m for m in modes if m]
    for name in _IMPORTERS:
        importlib.import_module(name)
    arith = sys.modules["common.arithmetic"]
    for mode in modes:
        if mode in ("naive_arith_only", "naive_arith"):
            _naive_arith(arith)
            if mode == "naive_arith":
                _no_hints(arith)
        elif mode == "no_div64_hint":
            _replace_everywhere(arith.x86_div64_quotient_fits_assumption,
                                lambda a, b: BoolVal(True, ctx=a.ctx))
        elif mode == "no_arith_hints":
            _no_hints(arith)
        elif mode == "no_div_bridge":
            bridge = sys.modules["common.div_bridge"]
            _replace_everywhere(bridge.verified_div_bridges, lambda *args, **kwargs: [])
        elif mode == "no_path_ite":
            harness = importlib.import_module("tests.support.instruction_equivalence")
            harness._PATH_AWARE_ITE_EVM_KINDS = set()
        elif mode == "bounded":
            _bounded()
        else:
            raise ValueError(f"unknown paper mode {mode!r}")
        APPLIED.append(mode)


def depth_only(reason):
    """True if every part of a coverage-incomplete reason is a depth cutoff."""
    parts = [p for p in (reason or "").split("; ") if p]
    return bool(parts) and all("depth" in p for p in parts)


def _bounded():
    """Alive2 bounded semantics where it is sound to emulate.

    paths mode: a side whose only coverage gap is the depth bound is accepted; the
    pairwise check then covers the explored inputs both sides share (vacuity is
    flagged by worker.classify). Any other gap keeps the fail-closed check.
    merged mode is NOT bypassed: truncated branches fall to the merged default value
    outside the explored domain and can produce spurious counterexamples, so a depth
    cut there stays a fail-closed BOUND result (reason recorded).
    """
    verifier = sys.modules["verification.program_verifier"]
    original_merged = verifier._merged_coverage_failure

    def merged(evm_result, x86_result):
        failure = original_merged(evm_result, x86_result)
        if failure is not None:
            TRUNCATED.append("merged (not bypassed): " + failure)
        return failure

    verifier._merged_coverage_failure = merged

    paths = sys.modules["verification.equivalence_paths"]
    owners = [c for c in vars(paths).values()
              if isinstance(c, type) and "_check_path_coverage" in vars(c)]
    if len(owners) != 1:
        raise RuntimeError("paper mode bounded: _check_path_coverage owner not unique")
    original_paths = owners[0]._check_path_coverage

    def coverage(self, path_results, label, deadline, coverage=None, precondition=None):
        if coverage is not None and not coverage.complete and depth_only(coverage.reason):
            TRUNCATED.append(f"{label}: {coverage.reason}")
            return True, None  # Alive2: paths beyond the bound are not checked
        return original_paths(self, path_results, label, deadline, coverage, precondition)

    owners[0]._check_path_coverage = coverage
