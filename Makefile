# Artifact entry points. Run `make help` for an overview.
SHELL      := /bin/bash
VALIDATOR  := ch4-5-validator
PYTHON     ?= python3.13
PY         := $(CURDIR)/$(VALIDATOR)/.venv/bin/python
GITVAL     := git --git-dir=$(CURDIR)/.validator-git --work-tree=$(CURDIR)/$(VALIDATOR)
EXP        := experiments

.PHONY: help install pin smoke test isabelle e1 e2 e3 e4 e5 e6 e7 small paper extra all tables clean distclean

help:
	@echo "Setup"
	@echo "  make install   create the Python environment ($(PYTHON), pinned requirements) and the validator snapshot"
	@echo "  make smoke     kick-the-tires check, a few minutes"
	@echo "  make test      validator unit tests (about 12 minutes with all cores)"
	@echo ""
	@echo "Paper (mapping, time and resources: experiments/README.md)"
	@echo "  make isabelle  Section 3, Appendix A: Isabelle sessions, Z3 scripts, export consistency (Isabelle2024)"
	@echo "                 Section 3.5 (GeneralStateTests): make -C ch3-isabelle/state-tests, see its README"
	@echo "  make e1        Table 1 microbenchmarks; Table 2 and Fig. 6 (O1/O2 ablation)          ~1 h"
	@echo "  make e2        Table 1 small programs; Fig. 5; Table 2 small-program subset         ~2 h"
	@echo "  make e4        Table 1 complete contracts under the 3600 s budget                   ~9 h"
	@echo "  make e5        Table 1 complete contracts, extended budget (V3 certificates)        hours per contract"
	@echo "  make e7        Fig. 7 and the RQ3 numbers, from recorded data                       minutes"
	@echo "  make small     e1 e2 (about 3 hours)"
	@echo "  make paper     e1 e2 e4 e5 e7 (more than a day on a 16-core / 32 GB host)"
	@echo "  make tables    summary tables of the recorded results (experiments/*/expected)"
	@echo ""
	@echo "Supplementary (not reported in the paper; experiments/README.md)"
	@echo "  make e3        O1/O2 ablation on four ENSRegistry function slices                   ~0.5 h"
	@echo "  make e6        shift-summary cost vs. target expansion, figure from recorded runs  minutes"
	@echo "  make extra     e3 e6"
	@echo "  make all       paper and supplementary experiments"
	@echo ""
	@echo "  make clean     remove local results and caches; make distclean also removes .venv and .validator-git"

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

# Paper experiments
e1:
	bash $(EXP)/E1-cores/run.sh
e2:
	bash $(EXP)/E2-programs/run.sh
e4:
	bash $(EXP)/E4-whole/run.sh
e5:
	bash $(EXP)/E5-extended-v3/run.sh
e7:
	bash $(EXP)/E7-v3-costs/run.sh

# Supplementary experiments (not reported in the paper)
e3:
	bash $(EXP)/E3-functions/run.sh
e6:
	bash $(EXP)/E6-shift/run.sh

small: e1 e2
paper: e1 e2 e4 e5 e7
extra: e3 e6
all: paper extra

clean:      # results, generated figures and caches of local runs
	rm -rf $(EXP)/smoke-results $(EXP)/*/results $(EXP)/E6-shift/figures ch3-isabelle/state-tests/*/target \
	  ch3-isabelle/state-tests/out
	find . -name __pycache__ -prune -exec rm -rf {} + ; find . -name .pytest_cache -prune -exec rm -rf {} +

distclean: clean   # also the Python environment and the validator snapshot created by `make install`
	rm -rf $(VALIDATOR)/.venv .validator-git ch3-isabelle/state-tests/tests

tables:
	@echo "# E1: Table 1 (microbenchmarks); Table 2 and Fig. 6 (V2-O1, V2-O2 on the 25-core cohort)"; echo
	@$(PY) $(EXP)/common/summarize.py $(EXP)/E1-cores/expected; echo
	@echo "# E2: Table 1 (small programs), Fig. 5, Table 2 (small-program subset)."
	@echo "# The paper counts 14 inputs: the 3 N/A inputs and the alias jumpi_2block_err are not counted."; echo
	@$(PY) $(EXP)/common/summarize.py $(EXP)/E2-programs/expected; echo
	@echo "# E4: Table 1 (complete contracts, 3600 s; cells are round 1/round 2)"; echo
	@$(PY) $(EXP)/common/summarize.py $(EXP)/E4-whole/expected; echo
	@echo "# E5: Table 1 (complete contracts, extended budget). Safe and Pool were resumed once: their wall time is"
	@echo "# the resumed segment's; the paper's cumulative times are in experiments/E5-extended-v3/README.md"; echo
	@$(PY) $(EXP)/E5-extended-v3/table.py $(EXP)/E5-extended-v3/expected; echo
	@echo "# Supplementary, not in the paper. E3: function slices"; echo
	@$(PY) $(EXP)/common/summarize.py $(EXP)/E3-functions/expected
