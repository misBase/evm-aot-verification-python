#!/bin/bash
# usage: runall.sh CODE_DIR OUT_DIR SECONDS
CODE=$1; OUT=$2; SEC=$3; R=$(cd "$(dirname "$0")/../.." && pwd)
mkdir -p $OUT
ls -S $R/cloud-inputs/server/r37d-5377/*.smt2 | xargs -P 4 -I{} sh -c 'cd '$CODE' && f={}; b=$(basename $f .smt2); PYTHONPATH=. '$R'/.venv/bin/python '$R'/cloud-inputs/tools/route_trace.py '$OUT'/$b.json $f --seconds '$SEC' > '$OUT'/$b.log 2>&1'
echo ALLDONE
