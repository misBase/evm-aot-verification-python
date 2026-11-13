# E6: Summary cost vs. target expansion (supplementary SHR family)

**Relation to the paper:** supplementary analysis of one O2 summary, complementing RQ2. The current paper does
not contain a shift-summary figure. E6 is included in `make extra` and `make all`, not `make paper`.

**Inputs:** `programs/e22_shr_k{1..8}`: programs with k independent variable SHR operations on 512 bytes of symbolic
calldata, compiled by the AOT compiler. Only the shift-summary setting changes between the two arms
(summary off vs. the fallback summary); gas OFF, depth 400, one worker, 600 s wall, the stated RSS limit, three
repetitions under the 300 s rule.

**Contents:**

- `expected/formal-v1/`: per-run records (`timing-k<k>-shift-<off|on>-r<n>.json`) and diagnostics;
- `expected/TIMING-ROOT-ANALYSIS.json`: the aggregated measurements used by the plot;
- `expected/shift-summary-wall-paper.pdf`: the archived figure from the earlier evaluation;
- `scripts/e22_formal_worker.py`, `scripts/e22_formal_run.py`: the original measurement driver, retained for provenance;
- `scripts/e22_analyze_timing.py`, `scripts/e22_v2.py`: aggregation and plotting.

**Scope:** the recorded runs used an earlier baseline-comparison snapshot, not the current E1/E2 batch.
`run.sh` regenerates the figure from those measurements; it does not launch new verification jobs. The original
measurement driver needs its development snapshot, prepared plan and harness, which are not packaged as a
standalone rerun environment. Regenerating the programs requires the AOT compiler, which is not part of this
artifact; the compiled programs are included. The plot shows completed CPU-time medians and min–max ranges;
timeout outcomes have no completed-time coordinate.

## Run

```sh
make e6                      # or: bash run.sh   -> figures/E22_shift_summary.pdf
```

A few minutes. The renderer checks the recorded cohort (36 runs: 30 VERIFIED, 6 TO; 12 protocol skips) and writes
the PDF, PNG and `figures/E22_shift_summary.source.json`, which records the plotted points and source hashes.
