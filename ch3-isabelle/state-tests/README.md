# Validation against the Ethereum GeneralStateTests

The Isabelle definition `execute_evm_bytecode` was exported to Rust and run on the official `GeneralStateTests`
vectors; mismatches caused by the semantics were fixed in the Isabelle rules and the Rust code regenerated.
`FIXES.md` lists the confirmed semantic errors found this way.

| Path | Contents |
|---|---|
| `theory/` | The semantics the Rust code was generated from (256-bit words as `word`), with the fixes of `FIXES.md`. `EVM_semantics_test.thy` holds a regression lemma for each fix, checked by evaluation. Session `EVM_StateTests` (`ROOT`) |
| `export1/src/EVM_Execute.rs` | The generated Rust code (`execute_evm_bytecode` and everything it depends on), crate `isabelle_exported`; produced from `theory/EVM_semantics.thy` with the Isabelle-to-Rust code generator [Isabelle2Rust](https://github.com/OpenSourceVerif/Isabelle2Rust) and checked in as generated |
| `runner/` | Command-line driver: builds the pre-state, calls `execute_evm_bytecode`, prints the resulting state |
| `harness/`, `compare_state_test.py`, `compare_state_suite.py` | Load the test vectors, classify them (`classify_official_tests.py`, `split_call_create.py`), drive the runner per post-state, and compare status, output, gas, storage and balances with the expected values |
| `fixtures/`, `run_smoke.py` | One hand-written vector for a quick check |
| `scripts/fetch_general_state_tests.sh` | Downloads `fixtures_general_state_tests.tgz` of `ethereum/tests` at commit `c67e485ff8b5be9abc8ad15345ec21aa22e290d9` (the snapshot of the paper), checks its SHA-256 and unpacks the 2,642 state-test files into `tests/GeneralStateTests` |
| `results/` | Recorded results (below) |

`../theory/` is the same semantics with 256-bit words represented as four 64-bit limbs, used for the U256 and
SMT results of Chapter 3. It contains the same fixes; `../fixes/` restates the regression lemmas for that
representation (session `EVM_AOT_Fixes`). SAR is the exception: the four-limb version implements it with `SRsh`,
which the Z3 script `../z3_proof/uint256_sar.py` checks separately.

## Selected records

`classify_official_tests.py` classifies every record of the snapshot. A record is runnable when it has a code
account, no unsupported opcode and no dependence on host behaviour (message calls, contract creation from inside
the code, `SELFDESTRUCT`); `split_call_create.py` then separates the runnable records whose transaction calls an
account (`to` set) from those that deploy code (empty `to`). `compare_state_suite.py` runs the call records, each
with all of its post-states.

| Records | Count |
|---|---:|
| In the snapshot | 2,642 |
| Runnable without host behaviour | 788 |
| of which call records (run) | 732 (4,126 post-states) |
| of which create records (need top-level deployment, not run) | 56 |
| Need host behaviour or contain an unsupported opcode | 1,765 |
| Without a code account | 89 |

## Recorded results

| File | Produced by |
|---|---|
| `results/official_test_classification.json` | `harness/classify_official_tests.py` on the snapshot: totals and per-directory counts |
| `results/official_runnable_candidates.jsonl` | the same run: the 788 runnable records (name, file, code, classification) |
| `results/call_create_split.json` | `harness/split_call_create.py` on the candidates: 732 call / 56 create records and their post-state counts |
| `results/process-records/` | runner outputs recorded during the fixing process and their re-judgement (below) |

`make classify` regenerates the three files into `out/`; they are identical to `results/` for the pinned snapshot.

Each selected case was run ten times by running the complete suite (`make full-test`) ten times in a row, with
inputs and expected outcomes unchanged.

## Records of the fixing process

`results/process-records/` keeps the runner outputs recorded while the semantic errors of `FIXES.md` were being
found and fixed (2026-09-29/30). They come from the development runner and harness of that time, not from the
final interpreter in `export1/`, so they are supporting evidence for how mismatches were found and disappeared.
Each line is one post-state run: record name, fork, post index, the command the harness ran (with its `--check-*`
expected values; the runner path is reduced to its file name) and the runner's output. Reports that were empty
are omitted.

`harness/recheck_process_reports.py` re-judges every line without executing anything: it looks the line up in the
pinned snapshot and compares the recorded output with the checks recorded in its command, using the evaluation of
`compare_state_suite.py`. The result is `results/process-records/recheck.json` (`make recheck` writes it to `out/`).
Runs named after a fix show the mismatches of that directory disappearing (FAIL/PASS per report; two `stShift`
post-states produced no output in every run):

| Directory | Reports in order | FAIL / PASS |
|---|---|---|
| `stExample` | `baseline`, `step1`, `step2`, `step3`, `verify` | 7/4, 1/10, 1/10, 0/11, 0/11 |
| `stShift` | `after_fixes`, `sstore_fix`, `sar_fix`, `memfix_regress` | 28/0, 4/24, 0/28, 0/28 |
| `stMemoryTest` | `msize_baseline`, `msize_fixed`, `mem_fix`, `fail_settle` | 29/1, 9/21, 7/23, 0/30 |

## Requirements

Isabelle2024 for `make semantics`; a stable Rust toolchain (`cargo +stable`, via rustup) and Python 3 for the rest
(tested with Python 3.13; the Python 3.6 of older Linux distributions is too old).
`make setup-tests`, `make classify` and `make full-test` download the test vectors (9.3 MB) from GitHub.

## Check

```sh
make semantics    # session EVM_StateTests, including the regression lemmas
make smoke        # build the runner, run the hand-written vector (seconds)
make classify     # fetch the snapshot, classify the records into out/ (compare with results/)
make recheck      # re-judge results/process-records/ against the snapshot into out/recheck.json
make full-test    # fetch the snapshot and run the 732 call records, all post-states
```
