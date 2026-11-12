# Automated proofs using the Z3 automatic theorem prover

Install Z3 for Python:

    pip install z3-solver

Run one proof, for example:

    PYTHONUTF8=1 python uint256_add.py

The main scripts verify the Go/holiman four-`uint64` implementation against
256-bit unsigned/signed EVM semantics:

    uint256_add.py      uint256_sub.py      uint256_mul.py
    uint256_div.py      uint256_mod.py      uint256_addmod.py
    uint256_mulmod.py   uint256_sdiv.py     uint256_smod.py
    uint256_eq.py       uint256_lt.py       uint256_gt.py
    uint256_slt.py      uint256_sgt.py      uint256_byte.py
    uint256_and.py      uint256_or.py       uint256_xor.py
    uint256_not.py      uint256_shl.py      uint256_shr.py
    uint256_sar.py

The limb-level DIV/MOD implementation is in
`uint256_udivrem_common.py`; `uint256_udivrem.py` checks the raw
`udivrem` algorithm against `UDiv`/`URem`.

See GOAL.md for the modeling conventions and current verification status.
