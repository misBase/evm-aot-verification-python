# z3_proof goal

Verify that the Go `uint256.Int` type, represented as four `uint64` words, is
mathematically equivalent to 256-bit unsigned/signed integer semantics for its
operations.

- Four-word representation: `z0, z1, z2, z3`, low word first.
- Mathematical value:
  `x = z0 + z1*2^64 + z2*2^128 + z3*2^192`.
- Implementation references:
  - `third-party/holiman/uint256@v1.3.2/uint256.go`
  - `third-party/holiman/uint256@v1.3.2/div.go`
  - EVM op dispatch: `aot-compiler/evm/instructions.go`
- `Sign` must follow Go's limb-level rule:
  `0 if z == 0; +1 if z3 < 2^63; otherwise -1`.
- Operations to verify:
  ADD, SUB, MUL, DIV, MOD, ADDMOD, MULMOD, SDIV, SMOD, comparisons, bitwise
  operations, and shifts.
- `Sign` helpers must be shared by the implementation being checked (`lhs`),
  not defined separately from the expression that uses them.
- Currently repaired and verified:
  `uint256_add.py`, `uint256_sub.py`, `uint256_mul.py`,
  `uint256_div.py`, `uint256_mod.py`, `uint256_addmod.py`,
  `uint256_mulmod.py`, `uint256_sdiv.py`, `uint256_smod.py`,
  `uint256_slt.py`, `uint256_sgt.py`, `uint256_byte.py`,
  `uint256_shl.py`, `uint256_shr.py`, `uint256_sar.py`,
  `uint256_eq.py`, `uint256_lt.py`, `uint256_gt.py`,
  `uint256_and.py`, `uint256_or.py`, `uint256_xor.py`, `uint256_not.py`.
- Removed obsolete one-case files, `uint256_exp.py`, `udivrem.py`, and
  `uint512_mod.py`; each remaining main script covers the full domain.

- Limb-level DIV/MOD model:
  `uint256_udivrem_common.py` models Go's `reciprocal2by1`,
  `udivrem2by1`, `addTo`, `subMulTo`, `udivremBy1`, `udivremKnuth`,
  normalization, denormalization, and the `Div`/`Mod` wrappers.
  `uint256_udivrem.py` is wired to this model. The QF_BV 64-bit
  `udivrem2by1` proof still times out in the current Z3 configuration; do not
  treat the printed `unknown` cases as proof. The semantic `Div`/`Mod` wrappers
  are verified separately in `uint256_div.py` and `uint256_mod.py` using Int.
