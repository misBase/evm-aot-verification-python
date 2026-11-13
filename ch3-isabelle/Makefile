# Chapter 3 checks.
#   ISABELLE: the Isabelle2024 executable;  PY: a Python with z3-solver (default: the validator's environment,
#   created by `make install` in the artifact root).
ISABELLE ?= isabelle
PY       ?= $(CURDIR)/../ch4-5-validator/.venv/bin/python
# The SMT exporter records the validator's git revision: use the artifact's validator snapshot.
export GIT_DIR      := $(CURDIR)/../.validator-git
export GIT_WORK_TREE := $(CURDIR)/../ch4-5-validator

.PHONY: all semantics smt division z3 export-check open

all: semantics smt division z3 export-check

# EVM semantics with the four-limb U256 model (session EVM_AOT; document output off, no LaTeX needed)
# and the regression lemmas for state-tests/FIXES.md (session EVM_AOT_Fixes).
semantics:
	$(ISABELLE) build -v -o document=false -d . EVM_AOT EVM_AOT_Fixes

# SMT deep embedding (smt2Isabelle) and the encoding-consistency certificates (sessions EVM_SMT_Base, EVM_SMT).
smt:
	$(ISABELLE) build -v -D smt

# Correctness of the four-limb uint256 DIV/MOD algorithm (session EVM_Div on top of EVM_SMT_Base).
division:
	$(ISABELLE) build -v -d smt -D division

# Z3 scripts checking the four-uint64 U256 algorithms against 256-bit semantics (Table 1).
z3:
	cd z3_proof && for f in uint256_*.py; do \
	  [ $$f = uint256_udivrem_common.py ] && continue; echo "== $$f"; PYTHONUTF8=1 $(PY) $$f || exit 1; done

# The validator in ../ch4-5-validator still produces the expressions certified in smt/.
export-check:
	$(PY) tools/compare_export.py
	cd tools && $(PY) -m unittest test_export_evm_smt -v

open:
	$(ISABELLE) jedit -d . theory/EVM_semantics.thy
