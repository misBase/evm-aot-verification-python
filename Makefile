# Artifact entry points. Run `make help` for an overview.
SHELL      := /bin/bash
VALIDATOR  := ch4-5-validator
PYTHON     ?= python3.13
PY         := $(CURDIR)/$(VALIDATOR)/.venv/bin/python
GITVAL     := git --git-dir=$(CURDIR)/.validator-git --work-tree=$(CURDIR)/$(VALIDATOR)
EXP        := experiments

.PHONY: help install pin smoke test isabelle e1 e2 e3 e4 e5 e6 e7 small all tables clean distclean

help:
	@echo "make install   create the Python environment ($(PYTHON), pinned requirements) and the validator snapshot"
	@echo "make smoke     kick-the-tires check, a few minutes"
	@echo "make isabelle  Chapter 3: Isabelle sessions, Z3 scripts, export consistency (needs Isabelle2024)"
	@echo "make test      validator unit tests (about 12 minutes with all cores)"
	@echo "make e1 .. e7  one experiment (see experiments/README.md for paper mapping, time and resources)"
	@echo "make small     e1 e2 e3 (cores, small programs, function slices; about 3.5 hours)"
	@echo "make all       every experiment (more than a day on a 16-core / 32 GB host)"
	@echo "make tables    summary tables of the recorded results in experiments/*/expected"
	@echo "make clean     remove local results and caches; make distclean also removes .venv and .validator-git"

install:
	cd $(VALIDATOR) && $(PYTHON) -m venv .venv && .venv/bin/pip install -q --upgrade pip \
	  && .venv/bin/pip install -q -r requirements.txt
	@# The certification CLI records the validator's git revision: snapshot the validator into .validator-git.
	@if [ ! -d .validator-git ]; then \
	  $(GITVAL) init -q && $(GITVAL) add -A && \
	  $(GITVAL) -c user.name=artifact -c user.email=artifact@localhost commit -qm "artifact snapshot"; fi
	$(MAKE) pin

pin:
	$(PY) $(EXP)/common/harness/source_pin.py $(VALIDATOR)

smoke:
	bash $(EXP)/common/smoke.sh

# Real captured formulas under a 30 s wall-clock solver budget: under full parallel load they may end `unknown`,
# so they run serially after the parallel suite (assertions and budgets unchanged).
WALLCLOCK_TESTS := \
  tests/unit/test_block_divrem_congruence.py::test_the_same_route_refutes_other_captured_instances \
  tests/unit/test_block_store_views.py::test_real_4418_capture_is_refuted_with_conditional_store_dependencies \
  tests/unit/test_signed_summary_proofs.py::test_wrong_builtin_operand_slots_match_but_cannot_be_certified

test:
	cd $(VALIDATOR) && rc=0; \
	  $(PY) -m pytest tests/unit -q -n auto -p no:cacheprovider $(addprefix --deselect ,$(WALLCLOCK_TESTS)) || rc=1; \
	  $(PY) -m pytest -q -p no:cacheprovider $(WALLCLOCK_TESTS) || rc=1; exit $$rc

isabelle:
	$(MAKE) -C ch3-isabelle all PY=$(PY)

e1:
	bash $(EXP)/E1-cores/run.sh
e2:
	bash $(EXP)/E2-programs/run.sh
e3:
	bash $(EXP)/E3-functions/run.sh
e4:
	bash $(EXP)/E4-whole/run.sh
e5:
	bash $(EXP)/E5-extended-v3/run.sh
e6:
	bash $(EXP)/E6-shift/run.sh
e7:
	bash $(EXP)/E7-v3-costs/run.sh

small: e1 e2 e3
all: e1 e2 e3 e4 e5 e6 e7

clean:      # results, generated figures and caches of local runs
	rm -rf $(EXP)/smoke-results $(EXP)/*/results $(EXP)/E6-shift/figures ch3-isabelle/state-tests/*/target \
	  ch3-isabelle/state-tests/out
	find . -name __pycache__ -prune -exec rm -rf {} + ; find . -name .pytest_cache -prune -exec rm -rf {} +

distclean: clean   # also the Python environment and the validator snapshot created by `make install`
	rm -rf $(VALIDATOR)/.venv .validator-git ch3-isabelle/state-tests/tests

tables:
	@for e in E1-cores E2-programs E3-functions E4-whole; do \
	  if [ -d $(EXP)/$$e/expected ]; then $(PY) $(EXP)/common/summarize.py $(EXP)/$$e/expected; echo; fi; done
	@$(PY) $(EXP)/E5-extended-v3/table.py $(EXP)/E5-extended-v3/expected
