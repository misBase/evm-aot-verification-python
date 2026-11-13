# E3: Function slices (supplementary)

**Relation to the paper:** supplementary O1/O2 ablation on a real contract, complementing RQ2. The current paper
reports instruction-core and small-program ablations (Table 2 and Fig. 6), not these function slices. E3 is
included in `make extra` and `make all`; it is not run by `make paper` or `make small`.

**Inputs:** the ENSRegistry functions `owner`, `resolver`, `setOwner` and `setSubnodeOwner`, each as a slice of the
complete contract pinned to its selector and calldata size. These four are the candidates admitted by the
sample-admission gate (non-empty domain, complete slice coverage, evidence of reduced exploration); the other
candidates in `common/harness/slices.py` are not validated by the gate. This experiment reuses that admission and
runs only the ablation (jobs `fnx/...`).

**Configurations:** V2, V2−O1, V2−O2; depth 100000, gas OFF.

**Limits:** 1800 s wall, 4000 MiB process-tree RSS, one run per function and configuration.

## Run

```sh
make e3                      # or: bash run.sh   (CPUS=0-7 MEM=12000 by default)
```

About 30 minutes.

## Check

```sh
python ../common/summarize.py expected
python ../common/summarize.py results
```
