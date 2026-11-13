# E4: Complete contracts under the comparison budget

**Paper:** RQ1, Table 1, row "Real-world complex (3600 s)" (V1 0/6, V2 1/6, V3 1/6), and the ENSRegistry
wall times and peak RSS quoted in Section 6.2. There is no separate whole-contract figure in the current paper.

**Inputs:** ENSRegistry, Permit2, Safe, CErc20, Uniswap V4 PoolManager and Aave Pool
(`ch4-5-validator/data/contracts/`, IR and x86-64 machine code as produced by the AOT compiler).

**Configurations:** V1 and V2 (path depth 100000, gas OFF) and V3 (mixed mode with the contract's trace, gas FULL,
4 node workers, 2000 MiB per node, segment depth 400; Pool 800).

**Limits:** 3600 s wall and 6000 MiB process-tree RSS per run; two rounds. With the default memory budget of
24000 MiB the matrix runs four jobs at a time.

## Run

```sh
make e4                      # or: bash run.sh   (CPUS=0-14 MEM=24000 by default)
```

About 9 hours on a 16-core / 32 GB host (36 runs of at most one hour, four at a time). On a smaller host lower
`MEM` (fewer concurrent jobs, longer total time); the per-job limits stay the same.

## Check

```sh
python ../common/summarize.py expected
python ../common/summarize.py results
```

The recorded summary prints each cell as "round 1/round 2"; both rounds have the same outcome for every
contract/configuration pair. Table 1 reports the completion counts, and the Section 6.2 ENSRegistry wall times
are medians over the two rounds. Under this budget V2 and V3 complete only ENSRegistry (V2 within about
150–180 s of the limit); completing the other contracts takes the longer budget of E5.
