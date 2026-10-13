#!/bin/bash
# valchain.sh "spec:stem ..."  -- sequential FULL proofs, base then opt, one process at a time.
# start: nohup ./valchain.sh "s6898:Safe s2193:Safe c6626:CErc20" > valchain.log 2>&1 < /dev/null &
V=~/evm-verif
A=$V/agents/exec5377
cd $V/bl-runs/snap-r34h
export BLOCK_SUMMARY_LEMMAS=1 PYTHONHASHSEED=0 PYTHONPATH=. BLOCK_PAIR_WORKERS=1 FULL=1
for item in $1; do
  spec=${item%%:*}
  stem=tests/data/ext_contracts/calldataload_fixed/${item##*:}
  for mode in base opt; do
    out=$A/val_${spec}_$mode
    rm -rf $out && mkdir -p $out
    if [ $mode = opt ]; then
      env REACH_MODE=incprobe_entry OPT_CORR=1 BLOCK_PROOF_CACHE=$out/cache.sqlite \
        nice -n 5 $V/.venv/bin/python $A/xseg.py $stem "$(cat $A/$spec.txt)" 3600 $out > $out/stdout.log 2>&1 < /dev/null
    else
      env REACH_MODE=base BLOCK_PROOF_CACHE=$out/cache.sqlite \
        nice -n 5 $V/.venv/bin/python $A/xseg.py $stem "$(cat $A/$spec.txt)" 3600 $out > $out/stdout.log 2>&1 < /dev/null
    fi
    echo "$spec $mode done $(date)"
  done
done
