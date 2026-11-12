# E5: V3 on complete contracts with an extended budget

**Paper:** the extended-budget V3 results (program certificates for all six complete contracts).

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
python table.py results      # summary table
```

Each contract takes from about 15 minutes (ENSRegistry) to several hours (CErc20, PoolManager) on a 16-core /
32 GB host. Run one contract at a time.

## Expected

`expected/` holds the reports behind the paper's numbers (`python table.py expected`):

| Contract | Wall | Notes |
|---|---|---|
| ENSRegistry | 906 s | 5 workers, 3000 MB per node |
| PoolManager | 22422 s | 13 workers, 4000 MB per node |
| Safe | 13030 s + ~81 min | first ~81 min with 5 workers, then resumed from its own results directory with 13 workers; the report covers the resumed segment |
| Pool | 13298 s + 5011 s | first run (7 workers, 3000 MB per node) proved all instances but block 7200, which exceeded the node memory cap (`supplementary/Pool-r1-inconclusive.json`); resumed from its results directory with 1 worker and 9000 MB, block 7200 proved by instruction-level lockstep |
| Permit2, CErc20 | | cold runs with 7 and 13 workers (reports added when the runs complete) |

Resuming reuses only the run's own results directory under the same source, options and traces; the final report
still checks the complete certificate.
