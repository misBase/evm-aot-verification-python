# E2: Small programs

**Paper:** Table 3 (small-program column), program figure, Table 6 (small-program ablation).

**Inputs:** 18 compiled programs in `ch4-5-validator/tests/data/` (arithmetic, conditional branches, memory returns,
storage, symbolic loops). `static_bounded`, `dynamic_bounded` and `unbounded` have IR but no machine code and are
reported as N/A; byte-identical aliases are not counted as independent samples in the paper.

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
