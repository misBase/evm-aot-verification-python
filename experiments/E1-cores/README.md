# E1: Instruction cores

**Paper:** RQ1, Table 1, row "Microbenchmarks" (V1 85/93, V2 93/93); RQ2, Table 2, column "Microbenchmarks"
(V2 25/25, V2 w/o O1 20/25 with 5 TO, V2 w/o O2 20/25 with 1 TO and 4 OOM) and Fig. 6 (the 13 arithmetic cores of
the cohort), with the SHL wall times quoted in Section 6.3. V3's entry in Table 1 (93/93, marked †) was confirmed
separately and is not part of this experiment.

**Inputs:** 93 instruction cores (the x86-64 code the compiler emits for one EVM instruction, with the operands and
context declared by each case; `ch4-5-validator/tests/integration/test_single_ins_equivalence.py`). The ablation
cohort is 13 arithmetic cores (MUL, DIV, MOD, SDIV, SMOD, ADDMOD, MULMOD, EXP, SIGNEXTEND, BYTE, SHL, SHR, SAR) and
12 memory cores (MLOAD, MSTORE, MSTORE8, CALLDATALOAD, CALLDATACOPY, CODECOPY, RETURNDATACOPY, MCOPY, MCOPY_OVERLAP,
SHA3, LOG0, LOG4).

**Configurations:** all cores under V1 and V2; the cohort also under V2−O1 and V2−O2. Depth 400, gas OFF, one worker.

**Limits:** 600 s wall and 2000 MiB process-tree RSS per job. Three repetitions; a job whose first run exceeds 300 s
runs once.

## Run

```sh
make e1                      # or: bash run.sh   (CPUS=0-3 MEM=8000 by default)
```

About 1 hour with 4 CPUs. Results go to `results/r1..r3`; `run.sh` ends with the summary tables.

## Check

```sh
python ../common/summarize.py expected     # the paper's runs
python ../common/summarize.py results      # your run
```

Outcome classes should agree; completed wall times vary with the host.
