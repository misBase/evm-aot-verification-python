# E2: Small programs

**Paper:** RQ1, Table 1, row "Small-program benchmarks" (V1 6/14, V2 8/14, V3 14/14), Fig. 5 and the `two_block`
medians quoted in Section 6.2; RQ2, Table 2, column "Small-program subset" (the 8 programs V2 completes: V2 w/o O1
8/8, V2 w/o O2 6/8). Appendix E (Table 4) describes the programs.

**Inputs:** 18 program inputs in `ch4-5-validator/tests/data/` (arithmetic, conditional branches, memory returns,
storage, symbolic loops). `static_bounded`, `dynamic_bounded` and `unbounded` have IR but no machine code and are
reported as N/A; `jumpi_2block_err` is a byte-identical alias of `jumpi_2block`. The paper counts the remaining 14
inputs, so its counts are the summary's VERIFIED counts without the alias.

**Configurations:** V1, V2, V2−O1, V2−O2 (depth 400, gas OFF) and V3 (mixed mode, gas FULL, 4 node workers).

**V3 traces:** seven programs have a byte-exact codegen trace in `ch4-5-validator/data/traces/` (two_block,
three_block, mstore_return, sstore_load, lockstep_counter_loop, lockstep_fmp_loop, lockstep_return_loop). The other
programs were compiled by an earlier compiler build, so no matching trace exists; V3 then has no instruction-level
fallback and behaves as block-level lockstep. All small programs verify in V3's block-level first pass.

**Limits:** 600 s wall; 3000 MiB process-tree RSS (4000 MiB for V3). Three repetitions under the 300 s rule.

## Run

```sh
make e2                      # or: bash run.sh   (CPUS=0-7 MEM=12000 by default)
```

About 2 hours with 8 CPUs.

## Check

```sh
python ../common/summarize.py expected
python ../common/summarize.py results
```
