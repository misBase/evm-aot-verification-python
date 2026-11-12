# Artifact: Translation Validation of an EVM Ahead-of-Time Compiler to x86-64

This artifact accompanies the paper. It contains the mechanized development of Chapter 3, the validator of
Chapters 4–5, the inputs used in the evaluation, and scripts that reproduce the tables and figures of the evaluation
section.

| Directory | Paper | Contents |
|---|---|---|
| `ch3-isabelle/` | Chapter 3 | Isabelle/HOL semantics of EVM with the 4×64-bit U256 model, the SMT deep embedding (`smt2Isabelle`) and its consistency certificates, and the Z3 scripts of the U256 algorithms (see `ch3-isabelle/README.md`) |
| `ch4-5-validator/` | Chapters 4–5 | The validator (Python, Z3, Capstone): EVM IR and x86-64 semantics, path-based validation, block-level and instruction-level lockstep, program certificates; unit and integration tests; evaluation inputs in `data/` |
| `experiments/` | Section 6 | One directory per experiment (E1–E7), each with a README, `run.sh` and the recorded results in `expected/` |
| `Makefile` | | Entry points: `make install`, `make smoke`, `make isabelle`, `make e1` … `make e7` |
| `Dockerfile` | | Pinned Linux environment for Chapters 4–5 and the experiments |

## Requirements

- **Chapters 4–5 and experiments:** Linux x86-64 (the harness pins jobs with `taskset` and reads `/proc`),
  Python 3.13 and the pinned packages of `ch4-5-validator/requirements.txt` (Z3 4.15.4.0, Capstone 5.0.6).
  Results depend on the Z3 version. The smoke test, E6 and E7 also run on macOS.
- **Chapter 3:** Isabelle2024 with HOL-Library and HOL-Data_Structures (see `ch3-isabelle/README.md`).
- **Hardware:** the smoke test needs 4 cores and 8 GB. The paper's complete-contract runs used a 16-core / 31 GB
  host; cores, small programs and function slices used an 8-core / 16 GB host. Per-experiment times are listed in
  `experiments/README.md`.
- **Disk:** about 1 GB including the Python environment.

## Installation

With Docker (recommended for Chapters 4–5):

```sh
docker build -t evm-aot-artifact .
docker run --rm -it evm-aot-artifact make smoke
```

Or locally:

```sh
make install          # creates ch4-5-validator/.venv from requirements.txt (PYTHON=python3.13 by default)
make smoke            # about 5 minutes
```

`make install` also snapshots the validator into `.validator-git/` (the certification CLI records the validator's
git revision) and writes the validator's source pin to `experiments/common/harness/SOURCE_PIN.json`. Every
experiment job checks that pin before and after it runs.

## Kick-the-tires (about 5 minutes)

```sh
make smoke            # 10 jobs: instruction core ADD (V1, V2), program two_block (V1, V2, V2-O1, V2-O2, V3),
                      # ENSRegistry.owner slice (V2, V2-O1, V2-O2); all should be VERIFIED (about 1 minute)
make tables           # the paper's recorded results as summary tables
make e7               # re-runs the RQ3 ledger and figure data from recorded data; prints "matches expected"
```

## Reproducing the paper

| Command | Paper | Time on the paper's hosts |
|---|---|---|
| `make isabelle` | Chapter 3: semantics session and SMT consistency certificates | see `ch3-isabelle/README.md` |
| `make e1` | Table 3 (cores), Table 5, core-ablation figure | ~1 h |
| `make e2` | Table 3 (small programs), program figure, Table 6 | ~2 h |
| `make e3` | function-ablation figure | ~0.5 h |
| `make e4` | Table 4, whole-contract figure | ~9 h |
| `make e5` | extended-budget V3 results (all six contracts certified) | hours per contract |
| `make e6` | shift-summary figure (from recorded measurements) | minutes |
| `make e7` | Tables 7–8, V3 cost figures (from recorded data) | minutes |

Each `run.sh` accepts `CPUS` (taskset list) and `MEM` (sum of the concurrent jobs' memory caps, MiB); per-job
limits are fixed by the experiment. Results are written to `experiments/<E>/results/` and summarized with
`python experiments/common/summarize.py experiments/<E>/results`; compare with `expected/`. Outcome classes
should agree; wall times depend on the host and on co-located jobs.

## Configurations

V1 is the whole-program baseline (merged terminal states, bounded path depth). V2 adds the O1 optimizations
(terminal-path comparison and path-pair parallelism) and the O2 optimizations (instruction summaries and
compiler-shaped arithmetic encoding); the ablations remove O1 or O2. V3 is block-level lockstep in mixed mode:
block-level proofs first, instruction-level lockstep for blocks whose first pass fails. V1/V2 run with gas checking
OFF; V3 checks gas in FULL mode. See `experiments/README.md`.

## Inputs

`ch4-5-validator/data/contracts/` holds the six complete contracts (ENSRegistry, Permit2, Safe, CErc20, Uniswap V4
PoolManager, Aave Pool) as exported EVM IR (`.json`) and x86-64 machine code (`.hex`) produced by the AOT compiler; `ch4-5-validator/tests/data/` holds the instruction cores' and small programs' inputs. The compiler itself is
not part of this artifact; validation needs only its outputs.

`ch4-5-validator/data/traces/` holds per-instruction codegen traces (x86 intervals and value locations of each IR
instruction) recorded from an instrumented build of the compiler. They are untrusted hints for instruction-level
lockstep: they only choose which per-instruction lemmas are stated, every lemma is proved, and the chain of lemmas
is checked to start at the real block entry and to be contiguous. A wrong trace makes a proof fail, never succeed.
A trace is used only if its machine code is byte-identical to the input (`data/SHA256SUMS`).

## Using the validator directly

```sh
cd ch4-5-validator
.venv/bin/python main.py tests/data/two_block.json "$(cat tests/data/two_block.hex)"   # one program, path-based
PYTHONPATH=. .venv/bin/python -m tools.verify_block_lockstep --help                   # block-level lockstep CLI
```

See `ch4-5-validator/README.md`.
