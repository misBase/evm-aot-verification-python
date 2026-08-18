# CLAUDE.md

Python formal verification for EVM AOT compilation to x86-64. It uses Z3 to prove equivalence between EVM IR semantics and compiled x86-64 machine-code semantics.

## Commands

Use Poetry consistently; do not mix Python environments.

```bash
poetry install
poetry run python main.py <ir_json_path> <x86_hex> [--base-addr ADDR] [--timeout MS] [--verbose]
poetry run pytest
poetry run pytest tests/integration/test_equivalence_checker.py
```

## Key External Projects

- `go-hpc-evm`: target EVM AOT compiler verified by this repo.
  - Path: `$GOPATH/src/github.com/bcds/go-hpc-evm`
  - Key files: `evm/aot/impl_amd64.go` (4360 lines, x86-64 codegen), `evm/aot/ir/evm_ir.go` (IR types), `evm/aot/engine_evm.go` (builtin registry), `evm/instructions.go`
- `go-hpc-fvm-compiler`: concrete amd64/x64 assembler and instruction encoding backend.
  - Path: `$GOPATH/src/github.com/bcds/go-hpc-fvm-compiler`
  - Key file: `asm/amd64/impl.go`

### Target Compiler Key Facts

- **IR structure**: Go side exports `CompilerEVMResult { ControlFrames: []*Block }` (top-level keys to expect in IR JSON); Python mirrors in `evm_ir/models.py`.
- **Reserved registers (Go ABI)**: `R13=callEngine`, `R14=stack base`, `R15=memory base`.
- **Stack layout**: `evmStackValueSize=4`; each uint256 occupies 4×uint64 slots at `[R14 + sp*8]`.
- **Builtin/host function indices**: see `x86_64/aot_profile.py` (`GO_HPC_EVM_PROFILE.builtin_functions` / `.host_functions`); per-contract overrides via `dataclasses.replace(...)`.

## Architecture

- Pipeline: load EVM IR JSON, disassemble x86-64 hex with Capstone, build both Z3 semantics, then prove equivalence.

## Domain Notes

- Uint256 is 4 x 64-bit limbs, little-endian (`z0` is least significant); see `common/uint256.py`. Z3 counterexamples report values as `z0..z3`.
- Current CALLVALUE model is 64-bit zero-extended to uint256. Widen the SMT model if the compiler changes to full 256-bit CALLVALUE.
- Z3 results: `UNSAT` means equivalent, `SAT` means counterexample, `UNKNOWN` means timeout or solver complexity.

## Shell Command Policy

- No here-doc syntax (`<<EOF`), piped code, or multi-line stdin.
- Use `poetry run python3 -c "<single-line>"` or write a temp file instead.
