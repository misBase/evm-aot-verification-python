# Experiments

Each subdirectory reproduces one group of results of the evaluation section. Every experiment has a `README.md`
(claim, command, expected time and resources), a `run.sh`, and an `expected/` directory with the measurements used
in the paper, so results can be checked without re-running the long experiments.

| Dir | Paper | What it measures | Time (16 cores / 32 GB) |
|---|---|---|---|
| `E1-cores` | Table 3 (cores), Table 5, core-ablation figure | 93 instruction cores under V1/V2; the 25-core ablation cohort under V2, V2−O1, V2−O2 | ~1 h |
| `E2-programs` | Table 3 (small programs), program figure, Table 6 | 18 small programs under V1, V2, V2−O1, V2−O2, V3 | ~2 h |
| `E3-functions` | function-ablation figure | 4 admitted ENSRegistry function slices under V2, V2−O1, V2−O2 | ~0.5 h |
| `E4-whole` | Table 4, whole-contract figure | 6 complete contracts × V1/V2/V3 × 2 rounds, 3600 s / 6000 MiB each | ~9 h |
| `E5-extended-v3` | extended-budget V3 results | V3 on the 6 complete contracts until a program certificate is issued | hours per contract |
| `E6-shift` | shift-summary figure | summary cost vs. target expansion on k = 1..8 independent SHR operations | minutes (figure) |
| `E7-v3-costs` | Tables 7–8, V3 cost figures | where optimized V3 spends its proof time (read-only analyses) | minutes |

## Configurations

| Name | Meaning |
|---|---|
| V1 | Whole-program baseline: merged terminal states, no optimizations, bounded path depth |
| V2 | V1 plus O1 (terminal-path comparison, path-pair parallelism) and O2 (instruction summaries, compiler-shaped arithmetic encoding) |
| V2−O1, V2−O2 | V2 without O1 / without O2 (RQ2 ablations) |
| V3 | Block-level lockstep in mixed mode: block-level proofs first, instruction-level lockstep for blocks the first pass misses; discovery, entry obligations, local proofs, successor obligations and certificate consumption |

V1, V2 and the ablations check gas in OFF mode (concrete initial gas, no final gas comparison); V3 uses FULL (symbolic
initial gas, remaining gas compared), as declared in the paper.

## Common machinery (`common/`)

- `harness/`: the experiment harness. `matrix.py` schedules jobs (CPU pinning, memory budget, repetitions),
  `run_one.py` guards each job (wall-clock limit, process-tree RSS limit, CPU/RSS accounting), `worker.py` runs one
  configuration on one input. Every job checks the validator's source pin (`harness/source_pin.py`).
- `env.sh`: paths shared by the `run.sh` scripts.
- `summarize.py ROOT`: outcome counts per configuration and per-input outcomes / wall times for one experiment.
- `repeat_names.py`: the repetition rule (only jobs whose first wall time is below 300 s are repeated).

## Outcome classes

VERIFIED (all coverage and equivalence obligations closed; for V3 the program certificate check passed), BOUNDED
(completed depth-truncated check, not a proof), BOUND (coverage failure from a depth bound), TO (query or external
timeout), OOM (memory limit), UNK (other inconclusive result), ERR (execution error), N/A (missing input pair).
Failed runs never contribute completion times.

## Notes

- Timings depend on the host and on co-located jobs. The paper's runs used a 16-core / 31 GB host for complete
  contracts and an 8-core / 16 GB host for cores, programs and functions, with the stated per-job limits.
- `E5` reruns take hours per contract; `E6` and `E7` reproduce figures and analyses from recorded measurements.
