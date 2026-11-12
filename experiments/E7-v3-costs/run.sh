#!/bin/bash
# E7: where optimized V3 still spends its time (RQ3: Tables 7-8 and the V3 cost figures).
# Read-only: re-runs the whole-run ledger (A1) on the certification reports, rebuilds the figure data from the
# recorded analyses and replay events, and renders the figures. Prints whether the results match expected.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
source "$HERE/../common/env.sh"
E5=$ARTIFACT/experiments/E5-extended-v3/expected
OUT=${OUT:-$HERE/results}
mkdir -p "$OUT"
"$PY" -m pip show matplotlib > /dev/null 2>&1 || { echo "matplotlib is needed: $PY -m pip install matplotlib"; exit 1; }
# A1: the four reports of tools/a1.py's main table, and Safe separately (as in analysis/a1.json, a1-safe.json).
"$PY" "$HERE/tools/a1.py" "$OUT/a1.json" "$E5/ENSRegistry.json" "$HERE/reports/CErc20.json" \
  "$E5/PoolManager.json" "$E5/Pool.json" > "$OUT/a1.log"
"$PY" "$HERE/tools/a1.py" "$OUT/a1-safe.json" "$E5/Safe.json" > "$OUT/a1-safe.log"
"$PY" - "$HERE/analysis" "$OUT" <<'EOF'
import json, sys
from pathlib import Path
expected, out = Path(sys.argv[1]), Path(sys.argv[2])
for name in ("a1.json", "a1-safe.json"):
    same = json.loads((expected / name).read_text()) == json.loads((out / name).read_text())
    print(f"{name}: {'matches expected' if same else 'DIFFERS from expected'}")
EOF
export E7_OUT=$OUT/figures
"$PY" "$HERE/figures/build_figure_data.py" > /dev/null
MPLCONFIGDIR=${TMPDIR:-/tmp}/mpl "$PY" "$HERE/figures/render_v3_figures.py" > /dev/null
"$PY" -c "import json,sys; print('figure-data.json:', 'matches expected' if json.load(open(sys.argv[1])) == json.load(open(sys.argv[2])) else 'DIFFERS from expected')" \
  "$HERE/figures/figure-data.json" "$E7_OUT/figure-data.json"
echo "figures: $E7_OUT/v3-cost-*.pdf"
