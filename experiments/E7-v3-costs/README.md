# E7: Remaining V3 costs (RQ3)

**Paper:** Tables 7–8 and the V3 cost figures (cost concentration, repeated proofs, composition of node time,
scheduling, single-factor mechanisms, shared-lemma duplication, route cascades).

**Data:**

- the certification reports of E5 (`../E5-extended-v3/expected/`) and the block-level-only CErc20 report used by
  the ledger (`reports/CErc20.json`);
- `analysis/`: the whole-run ledger (A1: `a1.json`, `a1-safe.json`, `master.json`), PPS-sampled instance replays
  (`sample-a2s.json`, `a2s-weighted.json`), scheduling simulations (`sim.jsonl`) and route replays (`b2.json`);
- `runs/`: raw events of the local replays and synthetic single-factor experiments; `local/`, `synth/`, `host-A/`:
  their receipts and summaries;
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

Replaying instances (`tools/run.py ... tools/replay.py ...`) needs the discovery output of a certification run
(E5) and takes from minutes to hours per instance; the recorded replays are in `runs/` and `analysis/`.
