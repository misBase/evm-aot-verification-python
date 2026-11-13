.PHONY: semantics build smoke setup-tests classify recheck full-test

ISABELLE ?= isabelle
TEST_DIR := tests/GeneralStateTests
RUNNER := runner/target/release/evm_execute_runner_stage2
FULL_TEST_ARGS ?=
# Local runs write here; the recorded results are in results/.
OUT := out

# The semantics the Rust code was generated from, including the regression lemmas of FIXES.md.
semantics:
	$(ISABELLE) build -v -o document=false -d . EVM_StateTests

build:
	cargo +stable build --release --manifest-path runner/Cargo.toml

smoke: build
	python3 run_smoke.py

# ethereum/tests at the pinned commit (see scripts/fetch_general_state_tests.sh).
setup-tests:
	bash scripts/fetch_general_state_tests.sh

# Classify all records and split the runnable ones into call/create (compare with results/; seconds, no Rust needed).
classify: setup-tests
	mkdir -p $(OUT)
	python3 harness/classify_official_tests.py $(TEST_DIR) --report $(OUT)/official_test_classification.json \
	  --candidates $(OUT)/official_runnable_candidates.jsonl > $(OUT)/classify.log
	python3 harness/split_call_create.py $(OUT)/official_runnable_candidates.jsonl . --out $(OUT)/call_create_split.json

# Re-judge the outputs recorded during the fixing process (nothing is executed; compare with results/process-records/).
recheck: setup-tests
	mkdir -p $(OUT)
	python3 harness/recheck_process_reports.py tests results/process-records/*.jsonl --out $(OUT)/recheck.json

full-test: build setup-tests
	python3 compare_state_suite.py $(TEST_DIR) --all --runner $(RUNNER) --all-posts --timeout 0 --no-color $(FULL_TEST_ARGS)
