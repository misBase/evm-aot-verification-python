# E6: Summary cost vs. target expansion (SHR family)

**Paper:** shift-summary figure (RQ2).

**Inputs:** `programs/e22_shr_k{1..8}`: programs with k independent variable SHR operations on 64 bytes of symbolic
calldata, compiled by the AOT compiler. Only the shift-summary setting changes between the two arms
(summary off vs. the fallback summary); gas OFF, depth 400, one worker, 600 s wall, the stated RSS limit, three
repetitions under the 300 s rule.

**Contents:**

- `expected/formal-v1/`: per-run records (`timing-k<k>-shift-<off|on>-r<n>.json`) and diagnostics;
- `expected/TIMING-ROOT-ANALYSIS.json`: the aggregated measurements plotted in the paper;
- `expected/shift-summary-wall-paper.pdf`: the figure as it appears in the paper;
- `scripts/e22_formal_worker.py`, `scripts/e22_formal_run.py`: the measurement driver used for the recorded runs;
- `scripts/e22_analyze_timing.py`, `scripts/e22_v2.py`: aggregation and plotting.

**Scope:** the recorded runs used the baseline-comparison snapshot of the validator (the same snapshot as the
earlier RQ2 measurements). `run.sh` regenerates the figure from those measurements. Regenerating the programs
requires the AOT compiler, which is not part of this artifact; the compiled programs are included.

## Run

```sh
make e6                      # or: bash run.sh   -> figures/E22_shift_summary.pdf
```
