# EVM AOT Translation Verification

This project implements **translation verification** for EVM (Ethereum Virtual Machine) AOT (Ahead-of-Time) compilation to x86-64 machine code using the **Z3 SMT solver**. It formally proves that the compiled machine code has semantically equivalent behavior to the original EVM bytecode.

## Overview

The system verifies that:
```
EVM_Bytecode(inputs) ≡ x86_64_AOT_Code(inputs)
```

This system performs **symbolic verification** using Z3 SMT solver to prove:
```
∀ a, b ∈ Uint256. EVM_ADD(a, b) ≡ x86_64_AOT_ADD(a, b)
```

- **EVM operation**: ADD instruction (pops two 256-bit values, pushes sum)
- **x86-64 machine code**: AOT-compiled ADD with stack-based 256-bit arithmetic
- **Result**: FORMALLY PROVEN equivalent for ALL possible inputs ✓

## Installation

### Prerequisites
- Python 3.8 or higher
- pip

### Setup

```bash
# Clone or navigate to the project directory
cd evm-aot-verification-python

# Install dependencies (including Z3)
pip install -r requirements.txt
```

或者在运行之前先开启代理：
```bash
proxyold
pip install -r requirements.txt
```

## Usage

### Quick Start

Run the complete verification suite:
```bash
python main.py
```

### Command-Line Options

```bash
# Run with verbose Z3 output
python main.py --verbose

# Set custom timeout (in milliseconds)
python main.py --timeout 30000

# Verify a single ADD operation
python main.py --single 0x60 0x10
python main.py --single 0xFF 0xFF

# Run unit tests
python test_verification.py

# Run examples with detailed explanations
python example.py
```

## Architecture

### Core Components

1. **`evm_interpreter.py`** - EVM Semantics Model
   - Models EVM stack operations (PUSH1, ADD)
   - Represents 256-bit integers as 4×64-bit limbs (z0, z1, z2, z3)
   - Implements ADD with modular arithmetic and carry propagation

2. **`x86_semantics.py`** - x86-64 Semantics Model
   - Models x86-64 instructions: MOV, ADD, ADC
   - Tracks register state and CPU flags (carry flag)
   - Simulates memory operations
   - Implements the exact instruction sequence from AOT output

3. **`verifier.py`** - Z3 Verification Engine
   - Executes both EVM and x86-64 symbolically
   - Constructs equivalence assertions
   - Uses Z3 to prove or disprove equivalence
   - Returns UNSAT (proven) or SAT (counterexample found)

4. **`main.py`** - Command-Line Interface
   - Coordinates verification workflow
   - Provides user-friendly output
   - Supports multiple test cases

5. **`test_verification.py`** - Unit Tests
   - Comprehensive test suite for all components
   - Tests edge cases and boundary conditions

6. **`example.py`** - Interactive Examples
   - Step-by-step demonstrations
   - Educational explanations of the verification process

## Verification Approach

### Symbolic Execution (Not Just Testing!)

Traditional testing checks specific values:
- ✓ Does `0x60 + 0x10 = 0x70`?
- ✓ Does `0xFF + 0x01 = 0x100`?
- ❌ Can't test all 2^512 possible input combinations!

**Symbolic verification** proves correctness for ALL inputs:
- ✓ Proves `∀ a, b. EVM_ADD(a, b) = x86_ADD(a, b)` mathematically
- ✓ Single proof covers all 2^512 input combinations!
- ✓ Uses Z3 SMT solver for formal verification

### EVM ADD Operation

```
EVM Stack Layout (each value is 256 bits):
  Before: [val1, val2, ...]
  After:  [val1+val2, ...]

Implementation:
  - Pop two 256-bit values from stack
  - Add with modulo 2^256 arithmetic
  - Push 256-bit result to stack
```

### x86-64 AOT Compiled Code

From the disassembly (address 0x6c - 0xac):
```asm
; Stack layout: R14 points to stack base
; [R14-0x40..0x28] = val1 (4×64-bit limbs)
; [R14-0x20..0x08] = val2 (4×64-bit limbs)

6c:  mov rax, [r14-0x40]   ; Load val1.z0 (LSB)
70:  add rax, [r14-0x20]   ; Add val2.z0, set carry flag
74:  mov rcx, [r14-0x38]   ; Load val1.z1
78:  adc rcx, [r14-0x18]   ; Add val2.z1 + carry
7c:  mov rdx, [r14-0x30]   ; Load val1.z2
80:  adc rdx, [r14-0x10]   ; Add val2.z2 + carry
84:  mov rbx, [r14-0x28]   ; Load val1.z3 (MSB)
88:  adc rbx, [r14-0x08]   ; Add val2.z3 + carry
8c:  mov [r14-0x40], rax   ; Store result.z0
90:  mov [r14-0x38], rcx   ; Store result.z1
94:  mov [r14-0x30], rdx   ; Store result.z2
98:  mov [r14-0x28], rbx   ; Store result.z3

Result: [R14-0x40] = (val1 + val2) mod 2^256 (4×64-bit limbs)
```

### Verification Result

```
✓ VERIFIED: EVM and x86-64 ADD are semantically equivalent for ALL inputs

This is a FORMAL PROOF that:
  ∀ a, b ∈ Uint256. EVM_ADD(a, b) = x86_ADD(a, b)

Z3 returns UNSAT when checking: EVM_result ≠ x86_result
Meaning: There exists NO input where they differ
Therefore: They are ALWAYS equal (mathematically proven!)
```

## How It Works

### 1. Symbolic Execution

Both EVM and x86-64 code are executed **symbolically** using Z3 bitvectors:
- EVM: Models stack operations with 256-bit symbolic values
- x86-64: Models register operations with 64-bit symbolic values

### 2. Equivalence Checking

To prove equivalence, we check:
```python
assert(EVM_result != x86_result)
result = Z3_solver.check()
```

If the solver returns **UNSAT** (unsatisfiable), it means there's no input where the results differ, thus proving equivalence.

### 3. Multi-Limb Arithmetic

Both implementations use 4×64-bit limbs to represent 256-bit values:
```
256-bit value = [z3:bits192-255][z2:bits128-191][z1:bits64-127][z0:bits0-63]
                      RBX             RDX             RCX           RAX
```

### 4. Carry Propagation

The critical insight is modeling carry propagation correctly:
```
sum0, carry0 = add64(a.z0, b.z0, 0)
sum1, carry1 = add64(a.z1, b.z1, carry0)
sum2, carry2 = add64(a.z2, b.z2, carry1)
sum3, _      = add64(a.z3, b.z3, carry2)
```

This matches the x86-64 sequence: `ADD` (generates carry) → `ADC` (uses carry).

## Example Output

```
======================================================================
EVM AOT TRANSLATION VERIFICATION
Verifying ADD instruction with symbolic execution
======================================================================

======================================================================
TEST 1: SYMBOLIC VERIFICATION (FORMAL PROOF)
======================================================================

=== Symbolic Verification of ADD ===
Proving: ∀ a, b ∈ Uint256. EVM_ADD(a, b) ≡ x86_ADD(a, b)

[1] Executing EVM ADD symbolically...
    EVM input 1: Uint256(z0=evm_val1_z0, z1=evm_val1_z1, ...)
    EVM input 2: Uint256(z0=evm_val2_z0, z1=evm_val2_z1, ...)
    EVM result: computed symbolically

[2] Executing x86-64 ADD symbolically...
    x86 stack initialized with same symbolic values
    x86 result: computed symbolically

[3] Checking equivalence with Z3...
    Asserting: EVM_result ≠ x86_result
    If UNSAT, then they are always equal (proven!)

✓ VERIFIED: EVM and x86-64 ADD are semantically equivalent for ALL inputs

This is a FORMAL PROOF that:
  ∀ a, b ∈ Uint256. EVM_ADD(a, b) = x86_ADD(a, b)

======================================================================
TEST 2-5: CONCRETE TEST CASES (SANITY CHECKS)
======================================================================

[Test] Standard case: 0x60 + 0x10
✓ VERIFIED: EVM and x86-64 semantics are equivalent
  Result: 0x70

[Test] Zero + Zero: 0x0 + 0x0
✓ VERIFIED: EVM and x86-64 semantics are equivalent
  Result: 0x0

======================================================================
VERIFICATION SUMMARY
======================================================================

🎉 FORMAL PROOF COMPLETE!
   Proven: ∀ a, b. EVM_ADD(a, b) = x86_ADD(a, b)

   This means the AOT compiler's ADD implementation
   is MATHEMATICALLY PROVEN to be equivalent to EVM's
   ADD operation for ALL possible 256-bit inputs.

======================================================================
ALL TESTS PASSED ✓

The ADD instruction is FORMALLY VERIFIED!
======================================================================
```

## Design Documents

See [`DESIGN.md`](DESIGN.md) for comprehensive design documentation including:
- Detailed architecture explanation
- Mathematical formulation of verification
- Implementation rationale
- Future extensions

## Project Structure

```
evm-aot-verification-python/
├── evm_interpreter.py      # EVM semantics model
├── x86_semantics.py        # x86-64 semantics model
├── verifier.py             # Z3 verification engine
├── main.py                 # CLI entry point
├── example.py              # Interactive examples
├── test_verification.py    # Unit tests
├── requirements.txt        # Python dependencies
├── README.md              # This file
├── DESIGN.md              # Design documentation
└── .gitignore             # Git ignore rules
```

## Future Extensions

1. **More Instructions**: SUB, MUL, DIV, MOD, bitwise operations
2. **Symbolic Inputs**: Verify for all possible input values (not just concrete)
3. **Memory Operations**: MLOAD, MSTORE verification
4. **Control Flow**: JUMP, JUMPI verification
5. **Full Bytecode**: End-to-end verification of complete contracts

## References

- **AOT Compiler Implementation**: `/Users/june/Work/go/src/github.com/bcds/go-hpc-evm/evm/aot/impl_amd64.go`
- **Z3 Reference**: [uint256_add.py example](../isabelle-proves/z3_proof/uint256_add.py)
- **EVM Specification**: Ethereum Yellow Paper
- **x86-64 ISA**: Intel/AMD Architecture Manuals

## License

This is a research prototype for translation verification.

