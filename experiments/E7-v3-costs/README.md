# E7: Remaining V3 costs (RQ3)

**Paper:** RQ3, Fig. 7: (a) cost concentration over the final instances of five contracts (`concentration` in
`figure-data.json`; the paper renders this panel with its own layout); (b) composition of node proof time,
`figures/v3-cost-where-4cat-5c.pdf` (H2 / Local / Shared lemmas including instruction-chain proofs / Other, five
contracts). The SafeMath context and memory-size variants quoted in the text are `ectx` and `emsize`. The other
figures (repeated proofs, scheduling, single-factor mechanisms, shared-lemma duplication, route cascades) are
supporting analyses.

**Data:**

- the certification reports of E5 (`../E5-extended-v3/expected/`) and the block-level-only CErc20 report used by
  the ledger (`reports/CErc20.json`);
- `analysis/`: the whole-run ledger (A1: `a1.json`, `a1-safe.json`, `master.json`), PPS-sampled instance replays
  (`sample-a2s.json`, `a2s-weighted.json`: 32 replays of ENSRegistry, CErc20, PoolManager and Pool;
  `sample-a2s-with-safe.json`, `a2s-weighted-with-safe.json`: the same plus Safe's 8 replays), scheduling
  simulations (`sim.jsonl`) and route replays (`b2.json`);
- `runs/`: raw events of the local replays and synthetic single-factor experiments; `local/`, `synth/`, `host-A/`:
  their receipts and summaries (`host-A/a2s-summary.tgz`, and `host-A/a2s-summary-safe.tgz` for Safe);
- `figures/`: `build_figure_data.py` freezes every plotted number into `figure-data.json`;
  `render_v3_figures.py` renders the figures from that file only.

**Tools** (`tools/`): `a1.py` (ledger), `sim.py` (scheduling what-if), `run.py`/`hooks.py` (observed replays),
`replay.py` (one proof instance), `sample.py`/`a2s_report.py` (PPS sampling and weighting), `oracle.py`/`b2_jobs.py`
(route replays), `analyze.py` (event buckets).

## Run

```sh
make e7                      # or: bash run.sh
```

A few minutes. It re-runs A1 on the reports, rebuilds `figure-data.json` from `analysis/` and `runs/`, renders the
figures, and reports whether each result matches `expected` (the recorded analyses).

`make paper` includes E7. The same command also renders its supplementary figures; no new proof-instance
replays are needed to regenerate them.

| Output in `results/figures/` | Paper / supplementary use |
|---|---|
| `figure-data.json`, `v3-cost-tail.pdf/.png` | Fig. 7(a) data: five contracts; the paper uses its own layout for this panel |
| `v3-cost-where-4cat-5c.pdf/.png` | Fig. 7(b): five contracts, four categories (H2 / Local / Shared lemmas / Other) |
| `v3-cost-mechanisms.pdf/.png` | Controlled context, stack-depth and memory-size variants discussed in Section 6.4; the figure itself is supplementary |
| `v3-cost-where.pdf/.png` | Supplementary detailed cost categories, original four-contract cohort |
| `v3-cost-repetition.pdf/.png` | Supplementary repeated proofs and unknown memory size |
| `v3-cost-schedule.pdf/.png` | Supplementary scheduling simulations |
| `v3-cost-lemma.pdf/.png` | Supplementary shared-lemma duplication |
| `v3-cost-routing.pdf/.png` | Supplementary proof-route comparisons |

The original four-contract cost data and supporting analyses remain unchanged. The paper's cost composition
uses `where_with_safe` and `sample_sizes_with_safe` in `figure-data.json` (40 replays, eight per contract).
Local combines obligation solving and construction; Shared lemmas combines shared-lemma and instruction-chain
proofs. These are weighted shares of node proof time, not whole-contract elapsed time.

Replaying instances (`tools/run.py ... tools/replay.py ...`) needs the discovery output of a certification run
(E5) and takes from minutes to hours per instance; the recorded replays are in `runs/` and `analysis/`.

**Safe's replays** were run after the first 32, with the same tools, snapshot and replay configuration.
`tools/sample.py` seeds each contract separately (seed 20261112), so `sample.py OUT 8 Safe=<Safe report>` draws
the same eight instances the joint run would have drawn. `build_figure_data.py` checks that adding Safe leaves
the other four contracts' weighted shares unchanged.
