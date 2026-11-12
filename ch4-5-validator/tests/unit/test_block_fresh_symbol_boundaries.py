"""Real helper boundaries must extend, rather than identify, input symbols.

Each case runs in an independent interpreter with its ordinary native context.
The fresh probe predicts the next native name; no counter reset, factory mock,
or alternate implementation of the helper is involved. The first four shapes
were SAT -> UNSAT counterexamples before the input-aware allocator was added.
"""
import json
import os
from pathlib import Path
import subprocess
import sys

import pytest


ROOT = Path(__file__).resolve().parents[2]
SCRIPT = r'''
import json
import sys
from time import monotonic

import z3 as z
import verification.block_equivalence as be

case = sys.argv[1]
word = z.BitVecSort(8)
x, y = z.BitVecs("boundary_x boundary_y", 8)

def next_name(prefix):
    probe = z.FreshConst(z.BoolSort(), "boundary_probe")
    return prefix + "!" + str(int(str(probe.decl().name()).rpartition("!")[2]) + 1)

def answer(formula):
    solver = z.Solver()
    solver.set(timeout=3000)
    solver.add(formula)
    return str(solver.check())

if case in ("divrem_result", "divrem_congruence", "mul_congruence", "uf_app"):
    if case == "divrem_result":
        existing = z.Const(next_name("divrem_result"), word)
        original = z.UDiv(x, y) != existing
        weakened, changed = be.abstract_divrem_results(original)
    elif case == "divrem_congruence":
        existing = z.Function(next_name("f"), word, word, word)
        original = z.UDiv(x, y) != existing(x, y)
        weakened, changed = be.abstract_divrem_congruence(original)
    elif case == "mul_congruence":
        existing = z.Function(next_name("f"), word, word, word)
        original = x * y != existing(x, y)
        weakened, changed = be.abstract_nonlinear_mul(original)
    else:
        existing = z.Const(next_name("uf_app"), word)
        function = z.Function("boundary_input_function", word, word)
        original = function(x) != existing
        pairs = be._uf_app_constants(original)
        weakened, changed = z.substitute(original, *pairs), bool(pairs)
    assert changed
    assert answer(original) == "sat"
    assert answer(weakened) == "sat"
    assert not z.is_false(z.simplify(weakened))
elif case == "core":
    existing = z.Bool(next_name("core"))
    assertions, goal = [z.Not(existing)], z.BoolVal(True)
    outcome = {}
    core = be._unsat_core(assertions, goal, 1000, outcome)
    assert core is None and outcome["answer"] == "sat"
    assert answer(z.And(*assertions, goal)) == "sat"
elif case == "skolem":
    a, b = (z.Array(name, word, word) for name in ("boundary_A", "boundary_B"))
    existing = z.Const(next_name("ext_w"), word)
    original = z.And(existing == 0, a[0] == b[0], a != b)
    weakened, lemmas = be.skolemize_array_disequalities(original, 1000)
    assert lemmas and all(lemma.answer == "unsat" for lemma in lemmas)
    assert answer(original) == answer(weakened) == "sat"
elif case == "array_equality_premise":
    a, b = (z.Array(name, word, word) for name in ("boundary_A", "boundary_B"))
    existing = z.Const(next_name("unify_idx"), word)
    premise = z.And(existing == 0, a[0] == b[0], a[1] != b[1])
    # The collided index occurs only in the premise, not in either array.
    proofs = be._prove_equal(premise, a, b, 1000, monotonic() + 3)
    assert proofs is None
    assert answer(premise) == "sat"
elif case == "cached_potential":
    n = 16
    p = be._potential(n)
    value = z.BitVec("boundary_memory_words", n)
    original = be._memory_cost(value) != p(value)
    weakened, changed = be.abstract_memory_potential(original)
    assert not changed and weakened.eq(original)
    assert answer(original) == answer(weakened) == "sat"
elif case == "reused_mul_namespace":
    functions = {}
    be.abstract_nonlinear_mul(x * y != 0, functions=functions)
    owned = next(iter(functions.values()))
    foreign = z.Function(str(owned.name()), word, word, word)
    original = x * y != foreign(x, y)
    assert foreign.eq(owned) and answer(original) == "sat"
    try:
        be.abstract_nonlinear_mul(original, functions=functions)
    except ValueError:
        pass
    else:
        raise AssertionError("a foreign input must not acquire the cached multiplication interpretation")
else:
    raise AssertionError(case)
print(json.dumps({"case": case, "checked": True}))
'''


@pytest.mark.parametrize("case", [
    "divrem_result", "divrem_congruence", "mul_congruence", "uf_app",
    "core", "skolem", "array_equality_premise", "cached_potential", "reused_mul_namespace",
])
def test_real_helpers_keep_input_symbol_boundaries(case):
    env = os.environ.copy()
    # Persistent proof answers must not conceal the current helper's result.
    env.pop("BLOCK_PROOF_CACHE", None)
    env.pop("BLOCK_PAIR_WORKERS", None)
    run = subprocess.run([sys.executable, "-c", SCRIPT, case], cwd=ROOT,
                         env=env, text=True, capture_output=True, timeout=30)
    assert run.returncode == 0, run.stdout + run.stderr
    assert json.loads(run.stdout.strip().splitlines()[-1]) == {"case": case, "checked": True}
