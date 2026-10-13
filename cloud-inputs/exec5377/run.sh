#!/bin/bash
# run.sh OUTNAME NODE_SECONDS [SPEC_FILE] [STEM]  -- one xseg run in the background (env passes through: REACH_MODE, RECORD, STOP)
V=~/evm-verif
A=$V/agents/exec5377
cd $V/bl-runs/snap-r34h
export BLOCK_SUMMARY_LEMMAS=1 PYTHONHASHSEED=0 PYTHONPATH=. BLOCK_PAIR_WORKERS=1 BLOCK_PROOF_CACHE=${CACHE:-$A/$1/cache.sqlite}
mkdir -p $A/$1
SPEC=${3:-spec2.txt}
STEM=${4:-tests/data/ext_contracts/calldataload_fixed/Safe}
nohup nice -n 5 $V/.venv/bin/python $A/${SCRIPT:-xseg.py} $STEM "$(cat $A/$SPEC)" $2 $A/$1 > $A/$1/stdout.log 2>&1 < /dev/null &
echo $! > $A/$1/pid
echo started $!
