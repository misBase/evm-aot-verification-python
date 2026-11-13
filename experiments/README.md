# Experiments

Each subdirectory reproduces one group of results. Every experiment has a `README.md` (claim, command, expected
time and resources), a `run.sh`, and its recorded results (`expected/`, or `analysis/` for E7), so results can be
checked without re-running the long experiments. Table and figure numbers refer to the submitted paper.

## Paper experiments (Section 6)

| Dir | `make` | Paper | What it measures | Time (16 cores / 32 GB) |
|---|---|---|---|---|
| `E1-cores` | `e1` | Table 1 (microbenchmarks, V1 and V2); Table 2 (microbenchmarks); Fig. 6 | 93 instruction cores under V1/V2; the 25-core ablation cohort under V2, V2−O1, V2−O2 (Fig. 6 shows its 13 arithmetic cores) | ~1 h |
| `E2-programs` | `e2` | Table 1 (small programs); Fig. 5; Table 2 (small-program subset) | 18 small-program inputs (14 counted in the paper) under V1, V2, V2−O1, V2−O2, V3 | ~2 h |
| `E4-whole` | `e4` | Table 1 (complete contracts, 3600 s); RQ1 ENSRegistry wall times and peak RSS | 6 complete contracts × V1/V2/V3 × 2 rounds, 3600 s / 6000 MiB each | ~9 h |
| `E5-extended-v3` | `e5` | Table 1 (complete contracts, extended); RQ1 extended-budget wall times | V3 on the 6 complete contracts until a program certificate is issued | hours per contract |
| `E7-v3-costs` | `e7` | Fig. 7 (a) and (b); the RQ3 numbers in Section 6.4 | where optimized V3 spends its proof time (read-only analyses of recorded data) | minutes |

`make paper` runs all five; `make small` runs E1 and E2; `make tables` prints the recorded results. Two results in
the paper are not produced by these experiments: V3's microbenchmark entry in Table 1 (marked † there; confirmed
separately and not re-run here) and Section 3 (`ch3-isabelle/`, `make isabelle`; Section 3.5 is
`ch3-isabelle/state-tests/`).

## Supplementary experiments (not reported in the paper)

These complement RQ2 and RQ3, but the paper does not cite their figures or tables. E3 uses the current experiment
harness and validator snapshot; E6 redraws measurements from an earlier baseline-comparison snapshot. E7's
supporting figures use its recorded profiling data. Their READMEs describe the scope of each analysis.

| Dir / output | `make` | Relation to the paper | What it measures | Time |
|---|---|---|---|---|
| `E3-functions` | `e3` | RQ2 ablation on a real contract | 4 admitted ENSRegistry function slices under V2, V2−O1, V2−O2 | ~0.5 h |
| `E6-shift` | `e6` | cost of one O2 summary (RQ2) | summary cost vs. target expansion on k = 1..8 independent SHR operations; figure from recorded runs | minutes |
| `E7-v3-costs`, supporting figures | `e7` | RQ3 | the figures `make e7` renders besides Fig. 7: repeated proofs, scheduling, the single-factor experiments, shared-lemma duplication, route cascades (see `E7-v3-costs/README.md`) | minutes |

`make extra` runs E3 and E6; `make all` runs the paper and supplementary experiments.

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
- `E5` reruns take hours per contract; `E7` (paper) and `E6` (supplementary) reproduce figures and analyses from
  recorded measurements.
