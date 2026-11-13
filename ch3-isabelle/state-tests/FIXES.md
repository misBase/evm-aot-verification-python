# EVM Benchmark Isabelle Semantic Fixes

This file records only the final, confirmed fixes to the Isabelle EVM semantics. Runner, driver, and generated-interpreter resource-limit issues are intentionally omitted.

## Confirmed Isabelle semantic fixes

- **EIP-2929 cold/warm storage access**
  SSTORE and SLOAD now charge 2100 for cold slots and 100 for warm slots. SLOAD also records accessed slots in the warm set.

- **EIP-4399 PREVRANDAO**
  `DIFFICULTY` returns `prevrandao` after Paris instead of `block_difficulty`.

- **Implicit STOP**
  Reading past the end of bytecode now returns `ContractReturn []` instead of `ContractFail [ShouldNotHappen]`.

- **Complete SSTORE gas and refund state machine**
  SSTORE gas now distinguishes original, current, and new values according to EIP-2929 and EIP-3529, including correct clear refunds and warm/cold handling.

- **Signed arithmetic right shift**
  `SAR` determines the 256-bit sign bit from the unsigned word value and applies sign extension consistently.

- **Monotone memory-expansion gas**
  Memory expansion gas uses `max` of the old and new memory sizes before computing the cost difference, avoiding negative deltas.

- **MSIZE byte size**
  `MSIZE` returns the active byte size directly rather than multiplying the already aligned byte length by 32.

- **EXP gas byte rounding**
  EXP dynamic gas rounds the exponent bit length up to whole bytes as `(bit_length e + 7) div 8`.

- **Keccak multi-block absorption**
  Keccak block-boundary handling no longer includes the capacity byte, so inputs of at least 136 bytes are hashed correctly.

- **EIP-2929 cold account access**
  `BALANCE`, `EXTCODESIZE`, `EXTCODEHASH`, and `EXTCODECOPY` charge 2600 for cold accounts and 100 for warm accounts, and record accessed accounts in the warm set.

- **External code size**
  `CODESIZE` and `EXTCODESIZE` return the byte length of code rather than the number of instructions.

- **SELFBALANCE gas**
  `SELFBALANCE` uses the fast-step gas cost rather than the previous incorrect value.

## Evidence

These fixes are confirmed by the official Ethereum `GeneralStateTests` vectors through the generated Rust entry point. Each issue corresponds to a mismatch that disappeared after correcting the Isabelle rules and regenerating the Rust executable.
