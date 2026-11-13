# Chapter 3: U256 model, EVM semantics and encoding consistency (Isabelle/HOL)

| Path | Paper | Contents |
|---|---|---|
| `theory/` | U256 model, EVM semantics | EVM semantics in Isabelle/HOL with 256-bit words represented as four 64-bit limbs (`uint256.thy`), state, syntax and instruction semantics (`EVM_state.thy`, `EVM_syntax.thy`, `EVM_semantics.thy`), gas and parameters, Keccak; `Exp.thy` verifies EXP (excluded from Table 1). Includes the fixes of `state-tests/FIXES.md`. Session `EVM_AOT` (`ROOT`) |
| `fixes/` | Validation against GeneralStateTests | `EVM_semantics_fixes.thy`: the regression lemmas for the fixes of `state-tests/FIXES.md`, restated for the four-limb representation and checked by evaluation. Session `EVM_AOT_Fixes` (`ROOT`) |
| `z3_proof/` | U256 algorithm proofs, Table 1 | One Python/Z3 script per operation, encoding the Go `uint256` algorithm over four `uint64` limbs and checking it against 256-bit unsigned/signed semantics (`GOAL.md` states the conventions) |
| `smt/` | Deep embedding, encoding-consistency theorem | The SMT deep embedding: SMT DSL and interpreter (`SMT_BV.thy`), the validator's operation encodings imported as Isabelle data (`generated/*.smt2`, `Generated_EVM_Arithmetic.thy`, `generated/manifest.json`), representation lemmas and per-category certificates (`EVM_SMT_*_Certificates.thy`); the consistency theorem is in `EVM_SMT_Certificates.thy`. Sessions `EVM_SMT_Base`, `EVM_SMT` (`smt/ROOT`) |
| `division/` | U256 DIV/MOD | Correctness of the four-limb `uint256` division algorithm (64-bit fast path, division by one limb, Knuth long division with normalization and reciprocal), in `theory/Div*.thy`; `Div.thy` states the top-level DIV/MOD theorems. Session `EVM_Div` (`division/ROOT`, on top of `EVM_SMT_Base`) |
| `state-tests/` | Validation against GeneralStateTests | `execute_evm_bytecode` exported to Rust, the runner and comparison harness for the official vectors, and the semantic errors this found (`FIXES.md`); see its README |
| `tools/` | Deep embedding (decoder) | `export_evm_smt.py` (the `smt2Isabelle` decoder: runs the validator's encoder on symbolic operands and emits the DSL terms) and its tests; `compare_export.py` checks that the packaged validator still produces the certified expressions |

## Requirements

Isabelle2024 (`isabelle` on `PATH`, or `make ISABELLE=/path/to/isabelle`); the sessions use only HOL,
HOL-Library and HOL-Data_Structures. The Z3 scripts and the export check use the validator's Python environment
(`make install` in the artifact root).

## Check

```sh
make semantics       # sessions EVM_AOT, EVM_AOT_Fixes (a few minutes)
make smt             # sessions EVM_SMT_Base, EVM_SMT (a few minutes)
make division        # session EVM_Div
make z3              # Z3 scripts of Table 1
make export-check    # the validator in ../ch4-5-validator produces the expressions certified in smt/
make all             # everything above
make -C state-tests smoke   # GeneralStateTests harness, needs a Rust toolchain (see state-tests/README.md)
```

`smt/base/` and `division/sources/` link to `theory/` (symbolic links), so keep the directory layout when copying.
