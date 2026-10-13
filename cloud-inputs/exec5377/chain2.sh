#!/bin/bash
# chain.sh WAIT_PID -- sequential jobs (one python process at a time)
# start: nohup ./chain.sh PID > chain.log 2>&1 < /dev/null &
V=~/evm-verif
A=$V/agents/exec5377
while kill -0 $1 2>/dev/null; do sleep 20; done
cd $V/bl-runs/snap-r34h
export BLOCK_SUMMARY_LEMMAS=1 PYTHONHASHSEED=0 PYTHONPATH=. BLOCK_PAIR_WORKERS=1 DUMP_PATHS=1
SAFE=tests/data/ext_contracts/calldataload_fixed/Safe
OPT="REACH_MODE=incprobe_entry OPT_CORR=1 OPT_APPLY=1"
run() {  # run OUT SPECFILE STEM SECONDS ENV...
  out=$A/$1; rm -rf $out; mkdir -p $out
  local spec=$2 stem=$3 secs=$4; shift 4
  env "$@" BLOCK_PROOF_CACHE=$out/cache.sqlite nice -n 5 $V/.venv/bin/python $A/xseg.py $stem "$(cat $A/$spec)" $secs $out > $out/stdout.log 2>&1 < /dev/null
  echo "$(date) done $out"
}




for item in $2; do
  spec=${item%%:*}; stem=tests/data/ext_contracts/calldataload_fixed/${item##*:}; tag=${spec%.txt}
  [ "$3" = both ] && run val_${tag}_base $spec $stem 3600 ${FULLFLAG:-FULL=1} REACH_MODE=base
  run val_${tag}_opt $spec $stem 3600 ${FULLFLAG:-FULL=1} $OPT
done
echo "$(date) chain finished"
