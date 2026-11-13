# Validation against the Ethereum GeneralStateTests

The Isabelle definition `execute_evm_bytecode` was exported to Rust and run on the official `GeneralStateTests`
vectors; mismatches caused by the semantics were fixed in the Isabelle rules and the Rust code regenerated.
`FIXES.md` lists the confirmed semantic errors found this way.

| Path | Contents |
|---|---|
| `theory/` | The semantics the Rust code was generated from (256-bit words as `word`), with the fixes of `FIXES.md`. `EVM_semantics_test.thy` holds a regression lemma for each fix, checked by evaluation. Session `EVM_StateTests` (`ROOT`) |
| `export1/src/EVM_Execute.rs` | The generated Rust code (`execute_evm_bytecode` and everything it depends on), crate `isabelle_exported`; produced from `theory/EVM_semantics.thy` with the Isabelle-to-Rust code generator [Isabelle2Rust](https://github.com/OpenSourceVerif/Isabelle2Rust) and checked in as generated |
| `runner/` | Command-line driver: builds the pre-state, calls `execute_evm_bytecode`, prints the resulting state |
| `harness/`, `compare_state_test.py`, `compare_state_suite.py` | Load the test vectors, drive the runner per post-state, and compare status, output, gas, storage and balances with the expected values |
| `fixtures/`, `run_smoke.py` | One hand-written vector for a quick check |
| `scripts/fetch_general_state_tests.sh` | Sparse checkout of `GeneralStateTests` from `ethereum/tests` into `tests/` |

`../theory/` is the same semantics with 256-bit words represented as four 64-bit limbs, used for the U256 and
SMT results of Chapter 3. It contains the same fixes; `../fixes/` restates the regression lemmas for that
representation (session `EVM_AOT_Fixes`). SAR is the exception: the four-limb version implements it with `SRsh`,
which the Z3 script `../z3_proof/uint256_sar.py` checks separately.

The harness runs only records that `execute_evm_bytecode` covers: records that need message calls, contract
creation from inside the code, or transaction-level processing are filtered (see `create_post_runnable` and
`classify_official_tests.py`).

## Requirements

Isabelle2024 for `make semantics`; a stable Rust toolchain (`cargo +stable`, via rustup) and Python 3 for the rest.
`make full-test` downloads the test vectors from GitHub.

## Check

```sh
make semantics    # session EVM_StateTests, including the regression lemmas
make smoke        # build the runner, run the hand-written vector (seconds)
make full-test    # fetch GeneralStateTests and run every applicable record
```
