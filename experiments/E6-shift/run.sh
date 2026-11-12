#!/bin/bash
# E6: summary cost vs. target expansion on the SHR family (RQ2, shift-summary figure).
# Regenerates the figure from the recorded measurements in expected/ (see README for the measurement scope).
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
source "$HERE/../common/env.sh"
"$PY" -m pip show matplotlib > /dev/null 2>&1 || { echo "matplotlib is needed: $PY -m pip install matplotlib"; exit 1; }
"$PY" "$HERE/scripts/e22_v2.py"
echo "figure: $HERE/figures/E22_shift_summary.pdf"
