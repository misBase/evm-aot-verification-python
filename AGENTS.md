# AGENTS.md

Python formal verification for EVM AOT compilation to x86-64. It compares EVM IR semantics and x86-64 machine-code semantics with Z3 to prove program equivalence.

## Key External Projects

- `go-hpc-evm`: target EVM AOT compiler verified by this repo.
  - Path: `$GOPATH/src/github.com/bcds/go-hpc-evm`
  - `evm/aot/impl_amd64.go`
  - `evm/instructions.go`
- `go-hpc-fvm-compiler`: provides the concrete amd64/x64 assembler and instruction encoding implementation.
  - Path: `$GOPATH/src/github.com/bcds/go-hpc-fvm-compiler`
  - `asm/amd64/impl.go`
