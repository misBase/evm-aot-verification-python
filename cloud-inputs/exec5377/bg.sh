#!/bin/bash
# bg.sh LOGNAME SCRIPT ARGS...  -- one python job in the background (cwd = snapshot)
V=~/evm-verif
A=$V/agents/exec5377
cd $V/bl-runs/snap-r34h
export BLOCK_SUMMARY_LEMMAS=1 PYTHONHASHSEED=0 PYTHONPATH=. BLOCK_PAIR_WORKERS=1 BLOCK_PROOF_CACHE=${CACHE:-$A/bgcache.sqlite}
log=$A/$1; shift
nohup nice -n 5 $V/.venv/bin/python "$@" > $log 2>&1 < /dev/null &
echo $! > $log.pid
echo started $!
