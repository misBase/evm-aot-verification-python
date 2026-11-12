# Shared settings for experiments/*/run.sh (sourced, not executed).
ARTIFACT=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
VALIDATOR=$ARTIFACT/ch4-5-validator
HARNESS=$ARTIFACT/experiments/common/harness
FIXTURES=$VALIDATOR/data/contracts
# The validator's virtual environment (created by `make install`); override with PY=/path/to/python.
PY=${PY:-$VALIDATOR/.venv/bin/python}
# V3 runs in mixed mode: block-level lockstep first, instruction-level lockstep for blocks the first pass misses.
# It reads the per-input codegen trace trace-<name>.json from this directory.
export PAPER_HINTS_DIR=${PAPER_HINTS_DIR:-$VALIDATOR/data/traces}
export PAPER_FIXTURES=$FIXTURES
MATRIX=("$PY" "$HARNESS/matrix.py" --snap "$VALIDATOR" --fixtures "$FIXTURES" --python "$PY")
# The certification CLI records the validator's git revision. `make install` snapshots the validator into a
# separate git directory, so ch4-5-validator/ itself stays a plain directory.
export GIT_DIR=$ARTIFACT/.validator-git GIT_WORK_TREE=$VALIDATOR

if [ ! -x "$PY" ]; then
  echo "error: $PY not found; run 'make install' first (or set PY)" >&2
  exit 1
fi
if [ ! -d "$GIT_DIR" ]; then
  echo "error: $GIT_DIR not found; run 'make install' first" >&2
  exit 1
fi
