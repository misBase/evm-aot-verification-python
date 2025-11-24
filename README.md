# EVM AOT Translation Verification

This project implements **program-level translation verification** for EVM (Ethereum Virtual Machine) AOT (Ahead-of-Time) compilation to x86-64 machine code using the **Z3 SMT solver**. It formally proves that the compiled machine code has semantically equivalent behavior to the original EVM bytecode.

## Overview

The system verifies **entire programs** (not just individual blocks) with:
```
EVM_Program(inputs) ≡ x86_64_AOT_Program(inputs)
```

This system performs **program-level logical semantics modeling** (Alive2-style) using Z3 SMT solver to prove:
```
∀ a, b ∈ Uint256. x86_ADD_Program(a, b) ≡ EVM_ADD_Program(a, b)
```

- **EVM program**: Sequence of IR blocks including ADD operations
- **x86-64 machine code**: Complete AOT-compiled program with stack-based 256-bit arithmetic
- **Result**: FORMALLY PROVEN equivalent for ALL possible inputs ✓

## Installation

### Prerequisites
- Python 3.8 or higher
- pip

### Setup

```bash
# Clone or navigate to the project directory
cd evm-aot-verification-python

# Install dependencies (Z3 SMT solver, Capstone disassembler, pytest)
pip install -r requirements.txt
```

**Main Dependencies:**
- `z3-solver>=4.12.0`: SMT solver for formal verification
- `capstone>=5.0.0`: x86-64 instruction disassembler
- `pytest>=7.0.0`: Testing framework

或者在运行之前先开启代理：
```bash
proxyold
pip install -r requirements.txt
```

## Usage

### Quick Start

Verify EVM IR and x86-64 machine code:
```bash
python3 main.py <ir_json_path> <x86_hex> [--base-addr ADDR] [--timeout MS] [--verbose]
```

Or run the test suite:
```bash
python3 -m tests.test_verifier
```

### Command-Line Options

```bash
# Basic verification
python3 main.py tests/data/example_ir.json 498b46c0490346e0...

# With base address
python3 main.py contract.ir.json 498b46c0... --base-addr 0x6c

# With custom timeout and verbose output
python3 main.py contract.ir.json 498b46c0... --timeout 30000 --verbose

# Run all tests
./run_tests.sh

# Run individual tests
python3 tests/test_basic.py
python3 tests/test_ir_json.py
python3 tests/test_verifier.py
python3 tests/test_disassembler.py
python3 tests/test_add_carry.py
python3 tests/test_uint256_add.py
```

## Project Structure

```
evm-aot-verification-python/
├── common/                    # 公共模块
│   ├── uint256.py            # 256位整数表示（4个64位limbs）+ 语义方法
│   └── evm_stack.py          # EVM栈模型
│
├── evm_ir/                    # EVM IR相关模块
│   ├── models.py             # EVM IR数据模型（Block, Operator）
│   ├── json_parser.py        # JSON格式IR解析器
│   ├── semantics.py          # EVM IR语义建模（调用Uint256方法）
│   └── program.py            # EVM程序级模型（整个程序的语义建模）
│
├── x86_64/                    # x86-64相关模块
│   ├── models.py             # x86-64数据模型（Block, Instruction, Register）
│   ├── disassembler.py       # x86-64机器码反汇编器（使用Capstone）
│   ├── execution_state.py    # x86-64执行状态管理（寄存器、内存、标志位）
│   ├── inst_executor.py      # x86-64指令执行器
│   ├── semantics.py          # x86-64指令语义建模（MOV, ADD, ADC等）
│   └── program.py            # x86程序级模型（整个程序的语义建模）
│
├── verification/              # 验证相关模块
│   ├── refinement_checker.py # 精化关系检查器（使用Z3验证x86精化EVM）
│   └── program_verifier.py   # 程序等价性验证器（主要验证接口）
│
├── tests/                     # 测试目录
│   ├── test_basic.py         # 基础功能测试
│   ├── test_ir_json.py       # EVM IR JSON解析测试
│   ├── test_verifier.py      # 验证器测试
│   ├── test_program_verifier.py # 程序级验证器测试
│   ├── test_disassembler.py  # x86-64反汇编器测试
│   ├── test_add_carry.py     # 进位传播测试
│   ├── test_uint256_add.py   # Uint256.add_semantics()直接测试
│   └── data/                 # 测试数据目录
│       └── example_ir.json   # 示例EVM IR JSON文件
│
├── main.py                    # 主入口程序（使用 ProgramEquivalenceChecker）
├── run_tests.sh               # 测试运行脚本
└── requirements.txt           # Python依赖
```

## Architecture

### Design Philosophy

The architecture follows the same pattern as the Go implementation (`instructions.go`), where operations call methods on the `uint256` type:

**Go Implementation**:
```go
func opAdd(_ *uint64, _ *EVMInterpreter, scope *ScopeContext) ([]byte, error) {
    x, y := scope.Stack.pop(), scope.Stack.peek()
    y.Add(&x, y)  // 调用uint256的Add方法
    return nil, nil
}
```

**Python Implementation**:
```python
# 在 evm_ir/semantics.py 中
def add_semantics(self, a: BitVec, b: BitVec) -> BitVec:
    a_uint = Uint256.from_bv256(a)
    b_uint = Uint256.from_bv256(b)
    result_uint = a_uint.add_semantics(b_uint)  # 调用Uint256的方法
    return result_uint.to_bv256()
```

### Core Components

#### 1. `common/uint256.py` - Uint256 Semantic Modeling
- **Purpose**: Defines Uint256 data structure and semantic methods
- **Key Features**:
  - Represents 256-bit integers as 4×64-bit limbs (z0, z1, z2, z3)
  - `add_semantics(other)`: Implements 4×64-bit limb addition with carry propagation
  - `to_bv256()` / `from_bv256()`: Conversion to/from Z3 BitVec

#### 2. `evm_ir/` - EVM IR Processing
- **`models.py`**: Data models for EVM blocks and operations
- **`json_parser.py`**: Parses EVM IR from JSON (exported by Go compiler)
- **`semantics.py`**: Semantic modeling for EVM operations
  - `EVMOperationSemantics.add_semantics()`: Delegates to `Uint256.add_semantics()`
  - `EVMIRSemantics.build_block_semantics()`: Builds block-level semantics
- **`program.py`**: **Program-level** semantic modeling (NEW)
  - `EVMProgram`: Wraps CompilerEVMResult for whole-program verification
  - `build_program_semantics()`: Builds semantics for entire IR sequence

#### 3. `x86_64/` - x86-64 Instruction Modeling
- **`models.py`**: Data models for x86 blocks, instructions, and registers
- **`disassembler.py`**: Disassembles hex-encoded machine code into X86Instruction objects using Capstone
  - Handles various hex string formats
  - Fixes R14 register identification issues
  - Parses operands into structured format
- **`execution_state.py`**: Manages execution state (registers, memory, flags) during instruction execution
- **`inst_executor.py`**: Executes instruction sequences using semantic modeling
  - Supports MOV, ADD, ADC instructions
  - Updates execution state accordingly
- **`semantics.py`**: Semantic modeling for x86-64 instructions
  - Implements MOV, ADD, ADC instruction semantics
  - Models the exact AOT-compiled instruction sequence
  - Builds semantic formulas from instruction sequences
- **`program.py`**: **Program-level** semantic modeling (NEW)
  - `X86Program`: Represents complete x86-64 programs
  - `build_program_semantics()`: Builds semantics for entire instruction sequence
  - `build_program_semantics_from_limbs()`: Convenience method for 256-bit inputs

#### 4. `verification/` - Verification Engine
- **`refinement_checker.py`**: Uses Z3 to check refinement relation (x86 refines EVM)
- **`program_verifier.py`**: **Program-level** verification (MAIN INTERFACE)
  - `ProgramEquivalenceChecker`: Verifies entire programs
  - `create_default_initial_state()`: Creates default initial SMT state with symbolic inputs
  - `verify_program_pair()`: Main verification entry point

#### 5. `tests/test_verifier.py` - Verification Test Cases
- Contains test cases for ADD operation verification
- `test_verify_add_symbolic()`: Formal proof using symbolic execution (∀ inputs)
- `test_verify_add_concrete()`: Verification with concrete values
- `test_verify_add_concrete_large()`: Verification with large values and carry
- Uses `ProgramEquivalenceChecker` for program-level verification

## Verification Approach

### Logical Semantics Modeling (Alive2-style)

Instead of symbolic execution, this system uses **logical semantics modeling**:
- Directly constructs logical formulas representing program semantics
- No execution state transitions
- More efficient for verification

### EVM ADD Operation

EVM ADD uses 4×64-bit limb representation:
```
256-bit value = [z3:bits192-255][z2:bits128-191][z1:bits64-127][z0:bits0-63]

Implementation (in Uint256.add_semantics()):
  - Decompose inputs into 4×64-bit limbs
  - Perform 4 additions with carry propagation:
    sum0, carry0 = add64(a.z0, b.z0, 0)
    sum1, carry1 = add64(a.z1, b.z1, carry0)
    sum2, carry2 = add64(a.z2, b.z2, carry1)
    sum3, _      = add64(a.z3, b.z3, carry2)
  - Combine limbs back into 256-bit result
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

### 1. Semantic Formula Construction

Both EVM and x86-64 semantics are modeled as logical formulas:
- **EVM**: `Uint256.add_semantics()` constructs formula for 4×64-bit addition
- **x86-64**: `X86SemanticsModel.build_add_sequence_semantics()` constructs formula for instruction sequence
- Both use the same underlying algorithm (4×64-bit limbs with carry)

### 2. Equivalence Checking

To prove equivalence, we check:
```python
solver.add(EVM_result != x86_result)
result = solver.check()
```

If the solver returns **UNSAT** (unsatisfiable), it means there's no input where the results differ, thus proving equivalence.

### 3. Multi-Limb Arithmetic

Both implementations use 4×64-bit limbs to represent 256-bit values:
```
256-bit value = [z3:bits192-255][z2:bits128-191][z1:bits64-127][z0:bits0-63]
                      RBX             RDX             RCX           RAX
```

The key insight: **EVM and x86-64 use the same algorithm**, so they produce identical results.

## Usage Examples

### Example 1: Direct Uint256 Addition

```python
from common.uint256 import Uint256

# Create two Uint256 values
val1 = Uint256.from_int(0x60)
val2 = Uint256.from_int(0x10)

# Call add_semantics method (similar to Go's y.Add(&x, y))
result = val1.add_semantics(val2)

# Result is also a Uint256 object
print(result.z0)  # 112 (0x70)
```

### Example 2: EVM IR JSON Parsing

```python
from evm_ir.json_parser import load_ir_from_json
from evm_ir.semantics import EVMIRSemantics
from common.uint256 import Uint256

# Load IR from JSON (exported by Go compiler)
ir_result = load_ir_from_json("tests/data/example_ir.json")

# Build semantics for a block
semantics = EVMIRSemantics()
block = ir_result.blocks[0]

# Create symbolic inputs
val1 = Uint256.symbolic("val1")
val2 = Uint256.symbolic("val2")
input_stack = [val1.to_bv256(), val2.to_bv256()]

# Build block semantics
result = semantics.build_block_semantics(block, input_stack)
```

### Example 3: x86-64 Disassembly

```python
from x86_64.disassembler import disassemble_hex
from x86_64.models import Register

# Disassemble hex-encoded machine code
hex_code = "498b46c0490346e0"  # mov rax, [r14-0x40]; add rax, [r14-0x20]
instructions = disassemble_hex(hex_code, base_addr=0x6c)

for insn in instructions:
    print(f"{insn.addr:04x}: {insn.mnemonic} {insn.op_str}")
```

### Example 4: Program-Level Verification

```python
from evm_ir.json_parser import load_ir_from_json
from evm_ir.program import EVMProgram
from x86_64.program import X86Program
from verification.program_verifier import ProgramEquivalenceChecker

# Load EVM program from JSON
compiler_result = load_ir_from_json("contract_ir.json")
evm_program = EVMProgram(compiler_result)

# Create x86 program from compiled machine code
x86_program = X86Program.from_hex(hex_code, base_addr=0x0)

# Verify program equivalence
checker = ProgramEquivalenceChecker()
initial_state = ProgramEquivalenceChecker.create_default_initial_state()
verified, msg = checker.verify_program_pair(evm_program, x86_program, initial_state)
```

## Testing

### Run All Tests

```bash
./run_tests.sh
```

This runs:
1. Basic functionality tests
2. EVM IR JSON parsing tests
3. Verifier tests
4. x86-64 disassembler tests
5. ADD with carry propagation tests
6. Uint256.add_semantics() direct tests

### Run Individual Tests

```bash
python3 tests/test_basic.py
python3 tests/test_ir_json.py
python3 tests/test_verifier.py
python3 tests/test_disassembler.py
python3 tests/test_add_carry.py
python3 tests/test_uint256_add.py
```

## Example Output

```
======================================================================
EVM AOT TRANSLATION VERIFICATION
Verifying ADD instruction with logical semantics modeling
======================================================================

======================================================================
TEST 1: SYMBOLIC VERIFICATION (FORMAL PROOF)
======================================================================

=== Logical Semantics Verification of ADD ===
Proving: ∀ a, b ∈ Uint256. x86_ADD(a, b) refines EVM_ADD(a, b)

[1] Building EVM ADD logical semantics...
    EVM input 1: Uint256(z0=evm_val1_z0, z1=evm_val1_z1, ...)
    EVM input 2: Uint256(z0=evm_val2_z0, z1=evm_val2_z1, ...)
    EVM semantic formula: result = (a + b) mod 2^256

[2] Building x86-64 ADD sequence logical semantics...
    x86 stack initialized with same symbolic values
    x86 semantic formula: composed from instruction sequence
      (MOV/ADD/ADC chain with carry propagation)

[3] Checking refinement relation with Z3...
    Verifying: x86 refines EVM (x86_result = EVM_result for all inputs)
    Asserting: x86_result ≠ EVM_result
    If UNSAT, then refinement holds (proven!)

✓ VERIFIED: x86 refines EVM (semantically equivalent for all inputs)

This is a FORMAL PROOF that:
  ∀ a, b ∈ Uint256. x86_ADD(a, b) refines EVM_ADD(a, b)
  (For deterministic ADD, refinement = equivalence)
```

## Key Design Decisions

### 1. Uint256 Semantic Modeling

Following the Go implementation pattern, semantic operations are encapsulated in the `Uint256` class:
- `Uint256.add_semantics()`: Implements 4×64-bit limb addition
- EVM operations call `Uint256` methods
- Ensures consistency and code reuse

### 2. Logical Semantics vs Symbolic Execution

This system uses **logical semantics modeling** (Alive2-style):
- Directly constructs logical formulas
- No execution state tracking
- More efficient for verification

### 3. Program-Level Verification

The system is designed for **program-level verification**:
- **EVM IR**: Parsed as complete programs (sequences of blocks)
- **x86-64 code**: Treated as complete instruction sequences
- **Verification**: Proves equivalence of entire programs

#### Key Advantages:
1. **Whole-Program Reasoning**: Captures inter-block control flow
2. **Scalable**: Can verify programs of arbitrary size
3. **Compositional**: Can focus on specific operations within programs
4. **Flexible**: Supports both symbolic and concrete inputs

## Future Extensions

1. **More EVM Operations**: MUL, SUB, DIV, MOD, bitwise operations (XOR, AND, OR, NOT)
2. **More x86-64 Instructions**: Support for more instruction patterns (SUB, MUL, shifts, etc.)
3. **Control Flow Verification**: JUMP, JUMPI verification with inter-block control flow
4. **Full Contract Verification**: End-to-end verification of complete smart contracts
5. **Performance Optimization**: Parallel verification of multiple programs
6. **Enhanced Program Analysis**: Automatic program segmentation and alignment
7. **Call Graph Analysis**: Verification across function boundaries
8. **Memory Model Verification**: Formal verification of memory operations

## References

- **AOT Compiler Implementation**: `/Users/june/Work/go/src/github.com/bcds/go-hpc-evm/evm/aot/`
- **EVM IR Definition**: `/Users/june/Work/go/src/github.com/bcds/go-hpc-evm/evm/aot/ir/evm_ir.go`
- **Z3 SMT Solver**: https://z3prover.github.io/
- **EVM Specification**: Ethereum Yellow Paper
- **x86-64 ISA**: Intel/AMD Architecture Manuals

## License

This is a research prototype for translation verification.
