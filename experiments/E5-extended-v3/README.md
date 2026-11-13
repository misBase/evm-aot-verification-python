# E5: V3 on complete contracts with an extended budget

**Paper:** RQ1, Table 1, row "Real-world complex (extended)" (V3 6/6), and the contract wall times quoted in
Section 6.2. These runs establish completion under extended resources; E4 supplies the comparison under the
common 3600 s / 6000 MiB budget.

**What runs:** `tools.verify_block_lockstep` in mixed mode on one contract: discovery of the reachable block
specializations, the entry obligations, a local block theorem per proof instance (block-level lockstep first,
instruction-level lockstep for instances the 300 s first pass misses), the successor obligations, and the final
certificate check. A contract is VERIFIED only if the certificate check passes.

**Parameters:** gas FULL, query timeout 30 s, first pass 300 s and full node budget 28800 s, segment depth 400,
wall limit 72 h, fresh proof cache; by default 13 node workers, 6000 MB per node (9000 MB for Pool, whose block 7200
needs about 5.8 GB in the instruction-level assembly phase).

## Run

```sh
make e5                      # all six; or: bash run.sh Pool CErc20   (env WORKERS, NODE_MB, CPUS, OUT)
make tables                  # recorded results, including the E5 summary table
```

Each contract takes from about 15 minutes (ENSRegistry) to several hours (CErc20, PoolManager) on a 16-core /
32 GB host. Run one contract at a time.

## Expected

`expected/` holds all six reports behind the paper's numbers. Each has status `verified`:

| Contract | Wall | Notes |
|---|---|---|
| ENSRegistry | 906 s | 5 workers, 3000 MB per node |
| Permit2 | 11732 s | cold run, 7 workers, 6000 MB per node |
| CErc20 | 20613 s | cold run, 13 workers, 6000 MB per node |
| PoolManager | 22422 s | 13 workers, 4000 MB per node |
| Safe | 13030 s + ~81 min | first ~81 min with 5 workers, then resumed from its own results directory with 13 workers; the report covers the resumed segment |
| Pool | 13298 s + 5011 s | first run (7 workers, 3000 MB per node) proved all instances but block 7200, which exceeded the node memory cap (`supplementary/Pool-r1-inconclusive.json`); resumed from its results directory with 1 worker and 9000 MB, block 7200 proved by instruction-level lockstep |

Resuming reuses only the run's own results directory under the same source, options and traces; the final report
still checks the complete certificate.

The Safe and Pool reports contain only the resumed segment's wall time. Section 6.2 reports approximate
cumulative times: Safe 17890 s (81 min + 13030 s), Pool 18309 s (13298 s + 5011 s). The summary table printed by
`table.py` uses each report's wall time, not these cumulative totals. Worker counts, node memory limits and
resumption differ across the recorded runs; their wall times do not form a controlled performance comparison.
