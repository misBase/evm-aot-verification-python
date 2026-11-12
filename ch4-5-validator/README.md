# Validator (Chapters 4–5)

Translation validation of EVM IR against the x86-64 machine code an ahead-of-time compiler emits for it. Both sides
are given symbolic semantics in Z3; equivalence obligations are discharged as SMT queries (UNSAT = equivalent,
SAT = counterexample, UNKNOWN = inconclusive). 256-bit EVM words are modeled as four 64-bit limbs, little-endian.

## Layout

| Package | Contents |
|---|---|
| `evm_ir/` | EVM IR model (`EVMBlock`, operations), JSON loader, operation semantics, gas semantics, CFG executor |
| `x86_64/` | Capstone disassembly, x86-64 instruction semantics, CFG executor, ABI profile of the target runtime, Go host-function semantics, instruction summaries (`summaries/`: MUL, DIV, SDIV/SMOD, shifts, memory gas, copy loops, CALLDATALOAD) with per-hit proofs |
| `state/` | Symbolic machine state: EVM stack, memory, storage, transient storage, gas; x86 registers and memory domains |
| `common/` | U256 limb arithmetic, compiler-shaped arithmetic encodings, shared helpers |
| `verification/` | Path-based program validation (`program_verifier.py`, `equivalence_*`); content-addressed proof cache (`proof_cache.py`); block-level lockstep (`block_equivalence.py`, `block_relation.py`, `block_specialization.py`, `block_program.py`, `block_parallel.py`); instruction-level lockstep (`instruction_chain.py`); loop induction and cutpoints |
| `tools/` | `verify_block_lockstep.py` (complete-program certification CLI) and analysis utilities |
| `tests/` | Unit, integration and composition tests; `tests/data/` holds the instruction cores' and small programs' inputs |
| `data/` | Evaluation inputs: `contracts/` (six complete contracts, IR + machine code), `traces/` (per-instruction codegen traces used as untrusted hints), `SHA256SUMS` |

## Install

```sh
python3.13 -m venv .venv && .venv/bin/pip install -r requirements.txt     # or: poetry install
```

(`make install` in the artifact root does this and the snapshot needed by the certification CLI.)

## Path-based validation of one program

```sh
.venv/bin/python main.py tests/data/two_block.json "$(cat tests/data/two_block.hex)" [--timeout MS] [--verbose]
.venv/bin/python main.py IR.json HEX --gas-check full        # symbolic initial gas, gas compared on every path
```

## Block-level lockstep certification of a complete program

```sh
PYTHONPATH=. .venv/bin/python -m tools.verify_block_lockstep data/contracts/ENSRegistry \
  --gas-check full --timeout-ms 30000 --summaries --discover-first --constant-insensitive \
  --first-pass-node-seconds 300 --node-seconds 28800 --node-workers 4 --node-memory-mb 4000 \
  --results-dir /tmp/ens-results --output /tmp/ens.json \
  --instruction-hints data/traces/trace-ENSRegistry.json      # mixed mode; omit for block-level only
```

The run discovers the reachable block specializations, proves the entry obligations, one local theorem per proof
instance and the successor obligations, and prints `VERIFIED` only if the final certificate check passes. With
`--instruction-hints`, instances whose block-level first pass fails are retried with instruction-level lockstep.
The CLI records the validator's git revision; run it inside a git work tree (or with `GIT_DIR`/`GIT_WORK_TREE`
set as in `../experiments/common/env.sh`).

## Tests

```sh
.venv/bin/python -m pytest tests/unit -q -n auto          # about 10 minutes with all cores
.venv/bin/python -m pytest tests/integration -q -n auto   # longer
```
