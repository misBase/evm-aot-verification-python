.PHONY: semantics build smoke setup-tests full-test

ISABELLE ?= isabelle
TEST_DIR := tests/ethereum-tests/GeneralStateTests
RUNNER := runner/target/release/evm_execute_runner_stage2
FULL_TEST_ARGS ?=

# The semantics the Rust code was generated from, including the regression lemmas of FIXES.md.
semantics:
	$(ISABELLE) build -v -o document=false -d . EVM_StateTests

build:
	cargo +stable build --release --manifest-path runner/Cargo.toml

smoke: build
	python3 run_smoke.py

setup-tests:
	bash scripts/fetch_general_state_tests.sh

full-test: build setup-tests
	python3 compare_state_suite.py $(TEST_DIR) --all --runner $(RUNNER) --all-posts --timeout 0 --no-color $(FULL_TEST_ARGS)
