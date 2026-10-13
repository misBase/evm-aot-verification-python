#!/bin/bash
# A/B in worker emulation: one process per (code, context), obligations in row order.
# usage: ab.sh OUT_ROOT SECONDS
R=$(cd "$(dirname "$0")/../.." && pwd)
S=${SCRATCH:?set SCRATCH to a dir holding basewt/ and newwt/ worktrees}
D=$R/cloud-inputs/server/r37d-5377
OUT=$1; SEC=$2
A="$D/a-pair_85_6_b4c723df3825.smt2 $D/a-pair_72_7_7d7e5ca31520.smt2 $D/a-pair_68_8_1e97f22c4bf7.smt2 $D/a-pair_67_9_043d50291a99.smt2 $D/a-pair_63_10_0c88ecb42eb9.smt2 $D/a-pair_58_12_4338d1bcf9bd.smt2 $D/a-pair_53_14_0e7fe3cd0120.smt2 $D/a-pair_43_18_97db0f0c4b3e.smt2"
B="$D/b-pair_85_6_9b0f56c5d16b.smt2 $D/b-pair_72_7_9c2f3fcb32d9.smt2 $D/b-pair_68_8_313a128bb00a.smt2 $D/b-pair_63_10_1a551f1988e3.smt2 $D/b-pair_58_12_b77bbb662104.smt2 $D/b-pair_57_13_cd822d2b4259.smt2 $D/b-pair_53_14_cdd13428051d.smt2 $D/b-pair_48_16_d65efe24c839.smt2"
run() {  # code_dir label files
  mkdir -p $OUT/$2
  (cd $1 && PYTHONPATH=. $R/.venv/bin/python $R/cloud-inputs/tools/route_trace.py --sequence $OUT/$2 $3 --seconds $SEC > $OUT/$2.log 2>&1)
}
run $S/basewt base-a "$A" &
run $S/basewt base-b "$B" &
run $S/newwt new-a "$A" &
run $S/newwt new-b "$B" &
wait
echo ABDONE
