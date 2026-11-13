# Deep embedding of production EVM arithmetic expressions

This development invokes `evm_ir.semantics.EVMOperationSemantics` in the
configured Python verification checkout, imports the resulting symbolic Z3 ASTs
as Isabelle data, and proves their interpreted result values in HOL. The paper's
operation table determines the scope. The legacy scripts in `z3_proof/` are
neither the expression source nor evidence for these certificates.

## Scope and operand conventions

The exported set contains the table's 23 operations and the previously supported
ISZERO operation:

| Category | Operations |
| --- | --- |
| Arithmetic | ADD, SUB, MUL, DIV, MOD, SDIV, SMOD, ADDMOD, MULMOD |
| Comparison | LT, GT, EQ, SLT, SGT, ISZERO |
| Bitwise | AND, OR, XOR, NOT |
| Shift | SHL, SHR, SAR |
| Byte | BYTE, SIGNEXTEND |

EXP is outside this table and this export. Each expression is the actual,
unsimplified template returned for symbolic BV256 operands. Quantification over
its valuations covers all concrete BV256 input values. It does not establish
that every alternative Python input representation or Python-level
specialization path produces that same template.

Variables 0, 1, and 2 denote the first, second, and third Python method arguments.
SUB means `a - b`. Shifts take `(value, amount)`, BYTE and SIGNEXTEND take
`(index, value)`, and ADDMOD/MULMOD take `(a, b, modulus)`. Unary operations ignore
the remaining inputs. This interface does not assert a stack operand-order
correspondence for every instruction wrapper.

## Main certificates

`EVM_SMT_Certificates.thy` retains the initial eight-operation binary interface
and adds the complete registry `table_evm_op`. The main statement is:

```isabelle
decode_smt_word
  (smt_eval (evm_inputs3 x y m) (table_expression op)) =
Some (table_hol_result op x y m)
```

`table_arithmetic_correct` states this decoded correspondence, and
`table_arithmetic_eval` states the packed integer-valued result. Each opcode
also has a separate certificate about its actual exported root.
`table_arithmetic_type` and `table_arithmetic_inputs_consistent` establish
well-typedness and consistent variable declarations. These structural
properties alone are not arithmetic correctness proofs.

The target functions preserve the existing limb algorithms for addition,
subtraction, multiplication, comparison, shifts, Byte, and extend_sign. Signed
comparison additionally connects to the dispatcher's `word_sless` expression.
The modular and signed division/remainder results follow the integer result
expressions in the instruction semantics. `hol_sdiv_result` and
`hol_smod_result` name those scalar expressions, without importing the full
execution-state development.

The MUL certificate follows `EVMOperationSemantics.mul_semantics`, which calls
`Uint256.mul_codegen_order` with the second operand first. Its proof connects
the compiler's partial-product and carry order to the existing `uint256_mul`
definition, then uses the integer multiplication theorem to account for the
operand exchange. Regeneration must capture this actual template. A certificate
for the earlier `Uint256.mul_semantics` template does not cover a changed AST
until the exported-expression proof has been checked again. The evaluation
proof reuses kernel-checked equalities for the generated DAG nodes. It simplifies
each node with fresh variables for its child values, then discharges the temporary
hypotheses and instantiates the result with the already proved child equalities.
Local weak congruence rules defer integer-payload normalization until after this
traversal. The final phase restores the original congruences and checks the complete
result against the HOL model. The concatenation proof also reuses the existing
four-limb theorem instead of expanding nested integer remainders. These are proof-strategy
optimizations. They preserve the exported AST, theorem statements, and oracle
dependency checks.

The BYTE and SIGNEXTEND certificates target the `Byte` and `extend_sign` library
helpers. The separate `get_byte` and `signextend` dispatcher definitions still
need a correspondence theorem before claiming a result about those complete
instruction rules. Stack updates, gas, exceptions, memory, and CFG execution
are outside this scalar-result development.

## Uninterpreted-function contracts

Five production templates contain arithmetic summaries: DIV, MOD, SDIV, SMOD,
and ADDMOD. The Python encoder declares `holiman_udiv` and `holiman_udivrem` as
uninterpreted BV256 functions on their long-division paths. The exporter
preserves those declarations and adds no axioms to the SMT query.

The interpreter is parameterized by a function interpretation:

```isabelle
smt_eval_with uf env expression
```

The abbreviation `smt_eval` uses `mathematical_uf`, which assigns unsigned
mathematical quotient and remainder, with zero results at zero divisors. The
production branch guards exclude those zero-divisor calls. Thus the five
certificates are results under an explicit chosen interpretation. They are not
identities valid for every interpretation of an unconstrained Z3 function.

`table_arithmetic_eval_with_contract` makes the agreement requirement on the
symbols occurring in an expression explicit. For the other 19 templates,
`table_arithmetic_eval_summary_free` proves the same result for **any** function
interpretation, since those templates contain no summary calls.

The DIV target in `table_hol_result` is the mathematical reference quotient.
It must not be confused with a proof that the existing `uint256_div`/`udivrem`
Knuth implementation computes that quotient. The division theory separately
connects the production expression to the concrete helper interpretation.
A mathematical refinement theorem for the long-division helper is a separate
obligation. Likewise, a mathematical MOD opcode result and the library `Mod`
helper are distinct targets.

An unconstrained-summary query admits the intended interpretation, so an UNSAT
answer covers that interpretation. A SAT answer may rely on an unintended
summary interpretation. These certificates do not reconstruct the proof of any
external Z3 answer.

## Corrected HOL guards and proof dependencies

`Byte` now checks the full index against 32. `Lsh` and `Rsh` check the full shift
operand against 256, and `SRsh` returns the sign-filled result for an oversized
negative shift. Checking only the low limb incorrectly accepted inputs whose
higher limbs were nonzero. The in-range limb algorithms remain in place.
`uint256_div` also handles equal nonzero operands directly, matching the
production shortcut. `exported_div_concrete_correct` connects the actual DIV
expression to this helper under the concrete quotient/remainder interpretation.

The certificate theories check `Thm_Deps.all_oracles` on their central facts.
The build rejects transitive dependencies on admitted proofs, solver oracles,
or evaluation oracles. Literal `eval` proofs needed from `Exp.thy` use
kernel-checked `code_simp` instead. No correctness claim rests merely on a
finite test suite or a solver's reported answer.

## Files and trust boundary

- `SMT_BV.thy`: typed expression syntax, input and summary-symbol analysis,
  interpreter, type preservation, evaluation completeness, and value bounds.
- `Generated_EVM_Arithmetic.thy`: imported shared AST nodes and checked typing,
  input-set, and summary-symbol lemmas. Regenerate rather than edit it.
- `EVM_SMT_Representation.thy`, `EVM_SMT_Bit_Representation.thy`, and operation
  theories: representation bridges and per-expression correctness proofs.
- `EVM_SMT_Substitution.thy`: environment congruence and expression-substitution
  lemmas, parameterized by arbitrary function interpretations.
- `generated/*.smt2`: SMT-LIB input/output relations for provenance, not solver
  proofs. Z3's text printer may flatten associative nodes. The HOL exporter
  instead traverses the raw expression DAG.
- `generated/manifest.json`: production revision, imported source hashes,
  Python/Z3 versions, operand declarations, summary symbols, and artifact hashes.

The Python AST capture and serialization remain unverified. Unknown variables,
sorts, operators, and function signatures fail closed. Hashes detect drift but
do not prove the serializer correct. The two structural translations are
ordered binary folds for n-ary Boolean connectives and negated equality for
binary Distinct. The exporter never invokes simplification or a solver.

The HOL interpreter specifies the supported SMT fragment. Its correspondence
with external SMT-LIB primitive behavior is a reviewed boundary. Isabelle's
kernel checks the imported-expression theorems, not the Python exporter or a
complete formalization of Z3.

## Build and regeneration

Use Isabelle2025 and the Python dependencies required by the production
semantics, including `z3-solver`. From this directory:

```sh
make open       # Main certificates in Isabelle/jEdit
make build      # Compile every theory imported by the local sessions
```

Configure the Python checkout once from the repository root:

```sh
cp config/paths.example.json config/paths.local.json
```

Set `python_repo` in `config/paths.local.json` to your checkout. The example
assumes the two repositories are siblings. Relative paths resolve from the
configuration file's directory, and `~` expands to your home directory.
The local configuration is ignored by Git. The exporter and production tests
read the same configuration regardless of the working directory.

Run the checks from the repository root:

```sh
python3 tools/export_evm_smt.py
python3 tools/export_evm_smt.py --check
python3 -m unittest discover -s tools -p 'test_export_evm_smt.py' -v
isabelle build -D smt

# Provenance, regression suite, and Isabelle build together:
make check-smt
```

The checkout selection order is `--python-repo`, `EVM_PYTHON_REPO`, then the
configuration's `python_repo`. Select a configuration using `--config` or
`EVM_SMT_CONFIG`, otherwise the default is `config/paths.local.json` under this
repository. CLI and environment paths resolve from the working directory.
Use `EVM_SMT_CONFIG` or `EVM_PYTHON_REPO` when overriding settings for both the
exporter and the unittest command, including through `make check-smt`.

```sh
python3 tools/export_evm_smt.py --config /path/to/paths.json --check
python3 tools/export_evm_smt.py --python-repo /path/to/checkout --check
EVM_SMT_CONFIG=/path/to/paths.json make check-smt
```

Without a default local configuration, standalone unit tests skip the production
integration tests. Invalid or explicitly selected missing configurations fail
instead. The full `make check-smt` command always requires a configured checkout.

`--check` compares generated bytes without rewriting them. The exporter does not
modify the Python checkout or create bytecode caches. Changed source hashes or
runtime versions require deliberate review and regeneration.

`EVM_SMT_Base` caches the original arithmetic theories through symlinks to
`EVMCommType`, `uint256`, and `Exp`. `EVM_SMT` checks the imported expressions
and their certificates. This standalone build does not certify the unrelated
full EVM_AOT state/gas session. `ISABELLE` overrides the executable used by the
Makefile.
