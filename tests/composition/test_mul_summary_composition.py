"""MUL summary 的局部组合证明测试。

完整验证链分三段：
1. unit 测试保证 matcher/apply 能正确实例化 summary；
2. single-ins refinement 证明 EVM MUL == summary；
3. 本文件补 raw x86 compileEVMMul slice == summary 语义。

第 3 段按 q2/q3/q4 编译期零值分支覆盖 2^3 种 row 形态（固化在
_GO_COMPILER_MUL_VARIANTS 的 8 个 branch-* fixture 里）；operand load
的 register/constant/stack 来源、具体寄存器和 stack offset 来自 matcher
的 location grammar，并由对应的 register/constant/stack fixture 覆盖。
代表性机器码已固化为 fixture，本测试只消费固定机器码，不在运行时调用
Go codegen，也不读取任何 Go 源码树。

证明分四类 lemma：
1. glue lemma（核心）：把 p/q limb 放成自由符号后整体符号执行 raw slice，
   逐 checkpoint 证明中间寄存器 == 分支化 limb 算法的输出，最后执行尾部
   4 条 result store 并证明 stack 内存上的最终值逐 limb 正确。实现在生产
   模块 x86_64/summaries/mul_proof.py（per-hit proof 同一份代码），本文件
   只保留薄 wrapper。
2. primitive lemma：每条 mul、每对 add/adc 在孤立符号输入下符合
   _mul64/_add64 helper；glue 失败时用于定位是哪条指令的建模出了问题。
3. composition lemma：手写的分支化 limb 算法 == uint256 乘法语义；
   z0/z1/z2 直接证明，z3 拆成 accumulator formula 再接到 mul_semantics。
4. frame/clobber lemma：slice 只写 summary 声明的 4 个 result stack slot，
   写过的寄存器都被 summary freshen，且不触碰 R13/R14/R15。

per-hit 信任缺口已关闭：生产 verification 在 discover 阶段对每次 matcher
命中调用 mul_proof.prove_mul_slice_cached（fail-closed，fallback 模式下
证明失败同样报错），本文件的 fixture 族此后作为回归与 lemma 分解的文档。
"""

import pytest
from z3 import BitVec, Or, Solver, unsat

from common.uint256 import Uint256
from state.smt_state import SMTState
from tests.integration.test_single_ins_refinement import X86_MUL_CORE_HEX_SEQUENCE
from x86_64.cfg import identify_basic_blocks
from x86_64.disassembler import disassemble_hex, parse_operands
from x86_64.models import Register, X86Instruction
from x86_64.summaries.mul import (
    ConstLimbLocation,
    StackLimbLocation,
    discover_mul_summaries,
)
from x86_64.summaries.mul_proof import (
    _ZERO64,
    _add64,
    _execute_insns,
    _is_stack_store,
    _mul64,
    _umul_hop,
    _umul_step,
    _umul_step_x86_order,
    _zero_branch_flags,
    prove_mul_slice_refines_summary,
)


_GO_COMPILER_MUL_VARIANTS = [
    {
        "name": 'branch-q2=full-q3=full-q4=full',
        "hex": (
            "498b46e0498b4ec048f7e14989c04889d3498b46e0498b4ec848f7e14801d84883d2004889c34889"
            "d6498b46e0498b4ed048f7e14801f04883d2004889c64889d7498b46e0498b4ed848f7e14801f848"
            "83d2004889c7498b46e8498b4ec048f7e14801d84883d2004989c14889d3498b46e8498b4ec848f7"
            "e14801f04883d2004801d84883d2004889c64889d3498b46e8498b4ed048f7e14801f84883d20048"
            "01d84883d2004889c7498b46f0498b4ec048f7e14801f04883d2004989c24889d3498b46f0498b4e"
            "c848f7e14801f84883d2004801d84883d2004889c7498b46f8498b4ec048f7e14801f84883d20049"
            "89c34d8946c04d894ec84d8956d04d895ed8"
        ),
    },
    {
        "name": 'branch-q2=full-q3=full-q4=zero',
        "hex": (
            "498b46e0498b4ec048f7e14989c04889d3498b46e0498b4ec848f7e14801d84883d2004889c34889"
            "d6498b46e0498b4ed048f7e14801f04883d2004889c64889d7498b46e0498b4ed848f7e14801f848"
            "83d2004889c7498b46e8498b4ec048f7e14801d84883d2004989c14889d3498b46e8498b4ec848f7"
            "e14801f04883d2004801d84883d2004889c64889d3498b46e8498b4ed048f7e14801f84883d20048"
            "01d84883d2004889c7498b46f0498b4ec048f7e14801f04883d2004989c24889d3498b46f0498b4e"
            "c848f7e14801f84883d2004801d84883d2004889c74989fb4d8946c04d894ec84d8956d04d895ed8"
        ),
    },
    {
        "name": 'branch-q2=full-q3=zero-q4=full',
        "hex": (
            "498b46e0498b4ec048f7e14989c04889d3498b46e0498b4ec848f7e14801d84883d2004889c34889"
            "d6498b46e0498b4ed048f7e14801f04883d2004889c64889d7498b46e0498b4ed848f7e14801f848"
            "83d2004889c7498b46e8498b4ec048f7e14801d84883d2004989c14889d3498b46e8498b4ec848f7"
            "e14801f04883d2004801d84883d2004889c64889d3498b46e8498b4ed048f7e14801f84883d20048"
            "01d84883d2004889c74989f2498b46f8498b4ec048f7e14801f84883d2004989c34d8946c04d894e"
            "c84d8956d04d895ed8"
        ),
    },
    {
        "name": 'branch-q2=full-q3=zero-q4=zero',
        "hex": (
            "498b46e0498b4ec048f7e14989c04889d3498b46e0498b4ec848f7e14801d84883d2004889c34889"
            "d6498b46e0498b4ed048f7e14801f04883d2004889c64889d7498b46e0498b4ed848f7e14801f848"
            "83d2004889c7498b46e8498b4ec048f7e14801d84883d2004989c14889d3498b46e8498b4ec848f7"
            "e14801f04883d2004801d84883d2004889c64889d3498b46e8498b4ed048f7e14801f84883d20048"
            "01d84883d2004889c74989f24989fb4d8946c04d894ec84d8956d04d895ed8"
        ),
    },
    {
        "name": 'branch-q2=zero-q3=full-q4=full',
        "hex": (
            "498b46e0498b4ec048f7e14989c04889d3498b46e0498b4ec848f7e14801d84883d2004889c34889"
            "d6498b46e0498b4ed048f7e14801f04883d2004889c64889d7498b46e0498b4ed848f7e14801f848"
            "83d2004889c74989d9498b46f0498b4ec048f7e14801f04883d2004989c24889d3498b46f0498b4e"
            "c848f7e14801f84883d2004801d84883d2004889c7498b46f8498b4ec048f7e14801f84883d20049"
            "89c34d8946c04d894ec84d8956d04d895ed8"
        ),
    },
    {
        "name": 'branch-q2=zero-q3=full-q4=zero',
        "hex": (
            "498b46e0498b4ec048f7e14989c04889d3498b46e0498b4ec848f7e14801d84883d2004889c34889"
            "d6498b46e0498b4ed048f7e14801f04883d2004889c64889d7498b46e0498b4ed848f7e14801f848"
            "83d2004889c74989d9498b46f0498b4ec048f7e14801f04883d2004989c24889d3498b46f0498b4e"
            "c848f7e14801f84883d2004801d84883d2004889c74989fb4d8946c04d894ec84d8956d04d895ed8"
        ),
    },
    {
        "name": 'branch-q2=zero-q3=zero-q4=full',
        "hex": (
            "498b46e0498b4ec048f7e14989c04889d3498b46e0498b4ec848f7e14801d84883d2004889c34889"
            "d6498b46e0498b4ed048f7e14801f04883d2004889c64889d7498b46e0498b4ed848f7e14801f848"
            "83d2004889c74989d94989f2498b46f8498b4ec048f7e14801f84883d2004989c34d8946c04d894e"
            "c84d8956d04d895ed8"
        ),
    },
    {
        "name": 'branch-q2=zero-q3=zero-q4=zero',
        "hex": (
            "498b46e0498b4ec048f7e14989c04889d3498b46e0498b4ec848f7e14801d84883d2004889c34889"
            "d6498b46e0498b4ed048f7e14801f04883d2004889c64889d7498b46e0498b4ed848f7e14801f848"
            "83d2004889c74989d94989f24989fb4d8946c04d894ec84d8956d04d895ed8"
        ),
    },
    {
        "name": 'positive-stack-offsets',
        "hex": (
            "498b4620498b0e48f7e14989c04889d3498b4620498b4e0848f7e14801d84883d2004889c34889d6"
            "498b4620498b4e1048f7e14801f04883d2004889c64889d7498b4620498b4e1848f7e14801f84883"
            "d2004889c7498b4628498b0e48f7e14801d84883d2004989c14889d3498b4628498b4e0848f7e148"
            "01f04883d2004801d84883d2004889c64889d3498b4628498b4e1048f7e14801f84883d2004801d8"
            "4883d2004889c7498b4630498b0e48f7e14801f04883d2004989c24889d3498b4630498b4e0848f7"
            "e14801f84883d2004801d84883d2004889c7498b4638498b0e48f7e14801f84883d2004989c34d89"
            "064d894e084d8956104d895e18"
        ),
    },
    {
        "name": 'q1-constant-zero',
        "hex": (
            "48c7c000000000498b4ec048f7e14989c04889d348c7c000000000498b4ec848f7e14801d84883d2"
            "004889c34889d648c7c000000000498b4ed048f7e14801f04883d2004889c64889d748c7c0000000"
            "00498b4ed848f7e14801f84883d2004889c7498b46e8498b4ec048f7e14801d84883d2004989c148"
            "89d3498b46e8498b4ec848f7e14801f04883d2004801d84883d2004889c64889d3498b46e8498b4e"
            "d048f7e14801f84883d2004801d84883d2004889c7498b46f0498b4ec048f7e14801f04883d20049"
            "89c24889d3498b46f0498b4ec848f7e14801f84883d2004801d84883d2004889c7498b46f8498b4e"
            "c048f7e14801f84883d2004989c34d8946c04d894ec84d8956d04d895ed8"
        ),
    },
    {
        "name": 'q2-nonzero-constant',
        "hex": (
            "498b46e0498b4ec048f7e14989c04889d3498b46e0498b4ec848f7e14801d84883d2004889c34889"
            "d6498b46e0498b4ed048f7e14801f04883d2004889c64889d7498b46e0498b4ed848f7e14801f848"
            "83d2004889c748c7c007000000498b4ec048f7e14801d84883d2004989c14889d348c7c007000000"
            "498b4ec848f7e14801f04883d2004801d84883d2004889c64889d348c7c007000000498b4ed048f7"
            "e14801f84883d2004801d84883d2004889c7498b46f0498b4ec048f7e14801f04883d2004989c248"
            "89d3498b46f0498b4ec848f7e14801f84883d2004801d84883d2004889c7498b46f8498b4ec048f7"
            "e14801f84883d2004989c34d8946c04d894ec84d8956d04d895ed8"
        ),
    },
    {
        "name": 'p1-nonzero-constant',
        "hex": (
            "498b46e048c7c10b00000048f7e14989c04889d3498b46e0498b4ec848f7e14801d84883d2004889"
            "c34889d6498b46e0498b4ed048f7e14801f04883d2004889c64889d7498b46e0498b4ed848f7e148"
            "01f84883d2004889c7498b46e848c7c10b00000048f7e14801d84883d2004989c14889d3498b46e8"
            "498b4ec848f7e14801f04883d2004801d84883d2004889c64889d3498b46e8498b4ed048f7e14801"
            "f84883d2004801d84883d2004889c7498b46f048c7c10b00000048f7e14801f04883d2004989c248"
            "89d3498b46f0498b4ec848f7e14801f84883d2004801d84883d2004889c7498b46f848c7c10b0000"
            "0048f7e14801f84883d2004989c34d8946c04d894ec84d8956d04d895ed8"
        ),
    },
    {
        "name": 'q1-register-rcx',
        "hex": (
            "4889c8498b5ec048f7e34989c14889d64889c8498b5ec848f7e34801f04883d2004889c64889d748"
            "89c8498b5ed048f7e34801f84883d2004889c74989d04889c8498b5ed848f7e34c01c04883d20049"
            "89c0498b46e8498b5ec048f7e34801f04883d2004989c24889d6498b46e8498b5ec848f7e34801f8"
            "4883d2004801f04883d2004889c74889d6498b46e8498b5ed048f7e34c01c04883d2004801f04883"
            "d2004989c0498b46f0498b5ec048f7e34801f84883d2004989c34889d6498b46f0498b5ec848f7e3"
            "4c01c04883d2004801f04883d2004989c0498b46f8498b5ec048f7e34c01c04883d2004989c44d89"
            "4ec04d8956c84d895ed04d8966d8"
        ),
    },
    {
        "name": 'p1-register-rcx',
        "hex": (
            "498b46e04889cb48f7e34989c14889d6498b46e0498b5ec848f7e34801f04883d2004889c64889d7"
            "498b46e0498b5ed048f7e34801f84883d2004889c74989d0498b46e0498b5ed848f7e34c01c04883"
            "d2004989c0498b46e84889cb48f7e34801f04883d2004989c24889d6498b46e8498b5ec848f7e348"
            "01f84883d2004801f04883d2004889c74889d6498b46e8498b5ed048f7e34c01c04883d2004801f0"
            "4883d2004989c0498b46f04889cb48f7e34801f84883d2004989c34889d6498b46f0498b5ec848f7"
            "e34c01c04883d2004801f04883d2004989c0498b46f84889cb48f7e34c01c04883d2004989c44d89"
            "4ec04d8956c84d895ed04d8966d8"
        ),
    },
    {
        "name": 'live-register-rcx',
        "hex": (
            "498b46e0498b5ec048f7e34989c14889d6498b46e0498b5ec848f7e34801f04883d2004889c64889"
            "d7498b46e0498b5ed048f7e34801f84883d2004889c74989d0498b46e0498b5ed848f7e34c01c048"
            "83d2004989c0498b46e8498b5ec048f7e34801f04883d2004989c24889d6498b46e8498b5ec848f7"
            "e34801f84883d2004801f04883d2004889c74889d6498b46e8498b5ed048f7e34c01c04883d20048"
            "01f04883d2004989c0498b46f0498b5ec048f7e34801f84883d2004989c34889d6498b46f0498b5e"
            "c848f7e34c01c04883d2004801f04883d2004989c0498b46f8498b5ec048f7e34c01c04883d20049"
            "89c44d894ec04d8956c84d895ed04d8966d8"
        ),
    },
    {
        "name": 'q1-register-rbx',
        "hex": (
            "4889d8498b4ec048f7e14989c14889d64889d8498b4ec848f7e14801f04883d2004889c64889d748"
            "89d8498b4ed048f7e14801f84883d2004889c74989d04889d8498b4ed848f7e14c01c04883d20049"
            "89c0498b46e8498b4ec048f7e14801f04883d2004989c24889d6498b46e8498b4ec848f7e14801f8"
            "4883d2004801f04883d2004889c74889d6498b46e8498b4ed048f7e14c01c04883d2004801f04883"
            "d2004989c0498b46f0498b4ec048f7e14801f84883d2004989c34889d6498b46f0498b4ec848f7e1"
            "4c01c04883d2004801f04883d2004989c0498b46f8498b4ec048f7e14c01c04883d2004989c44d89"
            "4ec04d8956c84d895ed04d8966d8"
        ),
    },
    {
        "name": 'p1-register-rbx',
        "hex": (
            "498b46e04889d948f7e14989c14889d6498b46e0498b4ec848f7e14801f04883d2004889c64889d7"
            "498b46e0498b4ed048f7e14801f84883d2004889c74989d0498b46e0498b4ed848f7e14c01c04883"
            "d2004989c0498b46e84889d948f7e14801f04883d2004989c24889d6498b46e8498b4ec848f7e148"
            "01f84883d2004801f04883d2004889c74889d6498b46e8498b4ed048f7e14c01c04883d2004801f0"
            "4883d2004989c0498b46f04889d948f7e14801f84883d2004989c34889d6498b46f0498b4ec848f7"
            "e14c01c04883d2004801f04883d2004989c0498b46f84889d948f7e14c01c04883d2004989c44d89"
            "4ec04d8956c84d895ed04d8966d8"
        ),
    },
    {
        "name": 'live-register-rbx',
        "hex": (
            "498b46e0498b4ec048f7e14989c14889d6498b46e0498b4ec848f7e14801f04883d2004889c64889"
            "d7498b46e0498b4ed048f7e14801f84883d2004889c74989d0498b46e0498b4ed848f7e14c01c048"
            "83d2004989c0498b46e8498b4ec048f7e14801f04883d2004989c24889d6498b46e8498b4ec848f7"
            "e14801f84883d2004801f04883d2004889c74889d6498b46e8498b4ed048f7e14c01c04883d20048"
            "01f04883d2004989c0498b46f0498b4ec048f7e14801f84883d2004989c34889d6498b46f0498b4e"
            "c848f7e14c01c04883d2004801f04883d2004989c0498b46f8498b4ec048f7e14c01c04883d20049"
            "89c44d894ec04d8956c84d895ed04d8966d8"
        ),
    },
    {
        "name": 'q1-register-rsi',
        "hex": (
            "4889f0498b4ec048f7e14989c14889d34889f0498b4ec848f7e14801d84883d2004889c34889d748"
            "89f0498b4ed048f7e14801f84883d2004889c74989d04889f0498b4ed848f7e14c01c04883d20049"
            "89c0498b46e8498b4ec048f7e14801d84883d2004989c24889d3498b46e8498b4ec848f7e14801f8"
            "4883d2004801d84883d2004889c74889d3498b46e8498b4ed048f7e14c01c04883d2004801d84883"
            "d2004989c0498b46f0498b4ec048f7e14801f84883d2004989c34889d3498b46f0498b4ec848f7e1"
            "4c01c04883d2004801d84883d2004989c0498b46f8498b4ec048f7e14c01c04883d2004989c44d89"
            "4ec04d8956c84d895ed04d8966d8"
        ),
    },
    {
        "name": 'p1-register-rsi',
        "hex": (
            "498b46e04889f148f7e14989c14889d3498b46e0498b4ec848f7e14801d84883d2004889c34889d7"
            "498b46e0498b4ed048f7e14801f84883d2004889c74989d0498b46e0498b4ed848f7e14c01c04883"
            "d2004989c0498b46e84889f148f7e14801d84883d2004989c24889d3498b46e8498b4ec848f7e148"
            "01f84883d2004801d84883d2004889c74889d3498b46e8498b4ed048f7e14c01c04883d2004801d8"
            "4883d2004989c0498b46f04889f148f7e14801f84883d2004989c34889d3498b46f0498b4ec848f7"
            "e14c01c04883d2004801d84883d2004989c0498b46f84889f148f7e14c01c04883d2004989c44d89"
            "4ec04d8956c84d895ed04d8966d8"
        ),
    },
    {
        "name": 'live-register-rsi',
        "hex": (
            "498b46e0498b4ec048f7e14989c14889d3498b46e0498b4ec848f7e14801d84883d2004889c34889"
            "d7498b46e0498b4ed048f7e14801f84883d2004889c74989d0498b46e0498b4ed848f7e14c01c048"
            "83d2004989c0498b46e8498b4ec048f7e14801d84883d2004989c24889d3498b46e8498b4ec848f7"
            "e14801f84883d2004801d84883d2004889c74889d3498b46e8498b4ed048f7e14c01c04883d20048"
            "01d84883d2004989c0498b46f0498b4ec048f7e14801f84883d2004989c34889d3498b46f0498b4e"
            "c848f7e14c01c04883d2004801d84883d2004989c0498b46f8498b4ec048f7e14c01c04883d20049"
            "89c44d894ec04d8956c84d895ed04d8966d8"
        ),
    },
    {
        "name": 'q1-register-rdi',
        "hex": (
            "4889f8498b4ec048f7e14989c14889d34889f8498b4ec848f7e14801d84883d2004889c34889d648"
            "89f8498b4ed048f7e14801f04883d2004889c64989d04889f8498b4ed848f7e14c01c04883d20049"
            "89c0498b46e8498b4ec048f7e14801d84883d2004989c24889d3498b46e8498b4ec848f7e14801f0"
            "4883d2004801d84883d2004889c64889d3498b46e8498b4ed048f7e14c01c04883d2004801d84883"
            "d2004989c0498b46f0498b4ec048f7e14801f04883d2004989c34889d3498b46f0498b4ec848f7e1"
            "4c01c04883d2004801d84883d2004989c0498b46f8498b4ec048f7e14c01c04883d2004989c44d89"
            "4ec04d8956c84d895ed04d8966d8"
        ),
    },
    {
        "name": 'p1-register-rdi',
        "hex": (
            "498b46e04889f948f7e14989c14889d3498b46e0498b4ec848f7e14801d84883d2004889c34889d6"
            "498b46e0498b4ed048f7e14801f04883d2004889c64989d0498b46e0498b4ed848f7e14c01c04883"
            "d2004989c0498b46e84889f948f7e14801d84883d2004989c24889d3498b46e8498b4ec848f7e148"
            "01f04883d2004801d84883d2004889c64889d3498b46e8498b4ed048f7e14c01c04883d2004801d8"
            "4883d2004989c0498b46f04889f948f7e14801f04883d2004989c34889d3498b46f0498b4ec848f7"
            "e14c01c04883d2004801d84883d2004989c0498b46f84889f948f7e14c01c04883d2004989c44d89"
            "4ec04d8956c84d895ed04d8966d8"
        ),
    },
    {
        "name": 'live-register-rdi',
        "hex": (
            "498b46e0498b4ec048f7e14989c14889d3498b46e0498b4ec848f7e14801d84883d2004889c34889"
            "d6498b46e0498b4ed048f7e14801f04883d2004889c64989d0498b46e0498b4ed848f7e14c01c048"
            "83d2004989c0498b46e8498b4ec048f7e14801d84883d2004989c24889d3498b46e8498b4ec848f7"
            "e14801f04883d2004801d84883d2004889c64889d3498b46e8498b4ed048f7e14c01c04883d20048"
            "01d84883d2004989c0498b46f0498b4ec048f7e14801f04883d2004989c34889d3498b46f0498b4e"
            "c848f7e14c01c04883d2004801d84883d2004989c0498b46f8498b4ec048f7e14c01c04883d20049"
            "89c44d894ec04d8956c84d895ed04d8966d8"
        ),
    },
    {
        "name": 'q1-register-r8',
        "hex": (
            "4c89c0498b4ec048f7e14989c14889d34c89c0498b4ec848f7e14801d84883d2004889c34889d64c"
            "89c0498b4ed048f7e14801f04883d2004889c64889d74c89c0498b4ed848f7e14801f84883d20048"
            "89c7498b46e8498b4ec048f7e14801d84883d2004989c24889d3498b46e8498b4ec848f7e14801f0"
            "4883d2004801d84883d2004889c64889d3498b46e8498b4ed048f7e14801f84883d2004801d84883"
            "d2004889c7498b46f0498b4ec048f7e14801f04883d2004989c34889d3498b46f0498b4ec848f7e1"
            "4801f84883d2004801d84883d2004889c7498b46f8498b4ec048f7e14801f84883d2004989c44d89"
            "4ec04d8956c84d895ed04d8966d8"
        ),
    },
    {
        "name": 'p1-register-r8',
        "hex": (
            "498b46e04c89c148f7e14989c14889d3498b46e0498b4ec848f7e14801d84883d2004889c34889d6"
            "498b46e0498b4ed048f7e14801f04883d2004889c64889d7498b46e0498b4ed848f7e14801f84883"
            "d2004889c7498b46e84c89c148f7e14801d84883d2004989c24889d3498b46e8498b4ec848f7e148"
            "01f04883d2004801d84883d2004889c64889d3498b46e8498b4ed048f7e14801f84883d2004801d8"
            "4883d2004889c7498b46f04c89c148f7e14801f04883d2004989c34889d3498b46f0498b4ec848f7"
            "e14801f84883d2004801d84883d2004889c7498b46f84c89c148f7e14801f84883d2004989c44d89"
            "4ec04d8956c84d895ed04d8966d8"
        ),
    },
    {
        "name": 'live-register-r8',
        "hex": (
            "498b46e0498b4ec048f7e14989c14889d3498b46e0498b4ec848f7e14801d84883d2004889c34889"
            "d6498b46e0498b4ed048f7e14801f04883d2004889c64889d7498b46e0498b4ed848f7e14801f848"
            "83d2004889c7498b46e8498b4ec048f7e14801d84883d2004989c24889d3498b46e8498b4ec848f7"
            "e14801f04883d2004801d84883d2004889c64889d3498b46e8498b4ed048f7e14801f84883d20048"
            "01d84883d2004889c7498b46f0498b4ec048f7e14801f04883d2004989c34889d3498b46f0498b4e"
            "c848f7e14801f84883d2004801d84883d2004889c7498b46f8498b4ec048f7e14801f84883d20049"
            "89c44d894ec04d8956c84d895ed04d8966d8"
        ),
    },
    {
        "name": 'q1-register-r9',
        "hex": (
            "4c89c8498b4ec048f7e14989c04889d34c89c8498b4ec848f7e14801d84883d2004889c34889d64c"
            "89c8498b4ed048f7e14801f04883d2004889c64889d74c89c8498b4ed848f7e14801f84883d20048"
            "89c7498b46e8498b4ec048f7e14801d84883d2004989c24889d3498b46e8498b4ec848f7e14801f0"
            "4883d2004801d84883d2004889c64889d3498b46e8498b4ed048f7e14801f84883d2004801d84883"
            "d2004889c7498b46f0498b4ec048f7e14801f04883d2004989c34889d3498b46f0498b4ec848f7e1"
            "4801f84883d2004801d84883d2004889c7498b46f8498b4ec048f7e14801f84883d2004989c44d89"
            "46c04d8956c84d895ed04d8966d8"
        ),
    },
    {
        "name": 'p1-register-r9',
        "hex": (
            "498b46e04c89c948f7e14989c04889d3498b46e0498b4ec848f7e14801d84883d2004889c34889d6"
            "498b46e0498b4ed048f7e14801f04883d2004889c64889d7498b46e0498b4ed848f7e14801f84883"
            "d2004889c7498b46e84c89c948f7e14801d84883d2004989c24889d3498b46e8498b4ec848f7e148"
            "01f04883d2004801d84883d2004889c64889d3498b46e8498b4ed048f7e14801f84883d2004801d8"
            "4883d2004889c7498b46f04c89c948f7e14801f04883d2004989c34889d3498b46f0498b4ec848f7"
            "e14801f84883d2004801d84883d2004889c7498b46f84c89c948f7e14801f84883d2004989c44d89"
            "46c04d8956c84d895ed04d8966d8"
        ),
    },
    {
        "name": 'live-register-r9',
        "hex": (
            "498b46e0498b4ec048f7e14989c04889d3498b46e0498b4ec848f7e14801d84883d2004889c34889"
            "d6498b46e0498b4ed048f7e14801f04883d2004889c64889d7498b46e0498b4ed848f7e14801f848"
            "83d2004889c7498b46e8498b4ec048f7e14801d84883d2004989c24889d3498b46e8498b4ec848f7"
            "e14801f04883d2004801d84883d2004889c64889d3498b46e8498b4ed048f7e14801f84883d20048"
            "01d84883d2004889c7498b46f0498b4ec048f7e14801f04883d2004989c34889d3498b46f0498b4e"
            "c848f7e14801f84883d2004801d84883d2004889c7498b46f8498b4ec048f7e14801f84883d20049"
            "89c44d8946c04d8956c84d895ed04d8966d8"
        ),
    },
    {
        "name": 'q1-register-r10',
        "hex": (
            "4c89d0498b4ec048f7e14989c04889d34c89d0498b4ec848f7e14801d84883d2004889c34889d64c"
            "89d0498b4ed048f7e14801f04883d2004889c64889d74c89d0498b4ed848f7e14801f84883d20048"
            "89c7498b46e8498b4ec048f7e14801d84883d2004989c14889d3498b46e8498b4ec848f7e14801f0"
            "4883d2004801d84883d2004889c64889d3498b46e8498b4ed048f7e14801f84883d2004801d84883"
            "d2004889c7498b46f0498b4ec048f7e14801f04883d2004989c34889d3498b46f0498b4ec848f7e1"
            "4801f84883d2004801d84883d2004889c7498b46f8498b4ec048f7e14801f84883d2004989c44d89"
            "46c04d894ec84d895ed04d8966d8"
        ),
    },
    {
        "name": 'p1-register-r10',
        "hex": (
            "498b46e04c89d148f7e14989c04889d3498b46e0498b4ec848f7e14801d84883d2004889c34889d6"
            "498b46e0498b4ed048f7e14801f04883d2004889c64889d7498b46e0498b4ed848f7e14801f84883"
            "d2004889c7498b46e84c89d148f7e14801d84883d2004989c14889d3498b46e8498b4ec848f7e148"
            "01f04883d2004801d84883d2004889c64889d3498b46e8498b4ed048f7e14801f84883d2004801d8"
            "4883d2004889c7498b46f04c89d148f7e14801f04883d2004989c34889d3498b46f0498b4ec848f7"
            "e14801f84883d2004801d84883d2004889c7498b46f84c89d148f7e14801f84883d2004989c44d89"
            "46c04d894ec84d895ed04d8966d8"
        ),
    },
    {
        "name": 'live-register-r10',
        "hex": (
            "498b46e0498b4ec048f7e14989c04889d3498b46e0498b4ec848f7e14801d84883d2004889c34889"
            "d6498b46e0498b4ed048f7e14801f04883d2004889c64889d7498b46e0498b4ed848f7e14801f848"
            "83d2004889c7498b46e8498b4ec048f7e14801d84883d2004989c14889d3498b46e8498b4ec848f7"
            "e14801f04883d2004801d84883d2004889c64889d3498b46e8498b4ed048f7e14801f84883d20048"
            "01d84883d2004889c7498b46f0498b4ec048f7e14801f04883d2004989c34889d3498b46f0498b4e"
            "c848f7e14801f84883d2004801d84883d2004889c7498b46f8498b4ec048f7e14801f84883d20049"
            "89c44d8946c04d894ec84d895ed04d8966d8"
        ),
    },
    {
        "name": 'q1-register-r11',
        "hex": (
            "4c89d8498b4ec048f7e14989c04889d34c89d8498b4ec848f7e14801d84883d2004889c34889d64c"
            "89d8498b4ed048f7e14801f04883d2004889c64889d74c89d8498b4ed848f7e14801f84883d20048"
            "89c7498b46e8498b4ec048f7e14801d84883d2004989c14889d3498b46e8498b4ec848f7e14801f0"
            "4883d2004801d84883d2004889c64889d3498b46e8498b4ed048f7e14801f84883d2004801d84883"
            "d2004889c7498b46f0498b4ec048f7e14801f04883d2004989c24889d3498b46f0498b4ec848f7e1"
            "4801f84883d2004801d84883d2004889c7498b46f8498b4ec048f7e14801f84883d2004989c44d89"
            "46c04d894ec84d8956d04d8966d8"
        ),
    },
    {
        "name": 'p1-register-r11',
        "hex": (
            "498b46e04c89d948f7e14989c04889d3498b46e0498b4ec848f7e14801d84883d2004889c34889d6"
            "498b46e0498b4ed048f7e14801f04883d2004889c64889d7498b46e0498b4ed848f7e14801f84883"
            "d2004889c7498b46e84c89d948f7e14801d84883d2004989c14889d3498b46e8498b4ec848f7e148"
            "01f04883d2004801d84883d2004889c64889d3498b46e8498b4ed048f7e14801f84883d2004801d8"
            "4883d2004889c7498b46f04c89d948f7e14801f04883d2004989c24889d3498b46f0498b4ec848f7"
            "e14801f84883d2004801d84883d2004889c7498b46f84c89d948f7e14801f84883d2004989c44d89"
            "46c04d894ec84d8956d04d8966d8"
        ),
    },
    {
        "name": 'live-register-r11',
        "hex": (
            "498b46e0498b4ec048f7e14989c04889d3498b46e0498b4ec848f7e14801d84883d2004889c34889"
            "d6498b46e0498b4ed048f7e14801f04883d2004889c64889d7498b46e0498b4ed848f7e14801f848"
            "83d2004889c7498b46e8498b4ec048f7e14801d84883d2004989c14889d3498b46e8498b4ec848f7"
            "e14801f04883d2004801d84883d2004889c64889d3498b46e8498b4ed048f7e14801f84883d20048"
            "01d84883d2004889c7498b46f0498b4ec048f7e14801f04883d2004989c24889d3498b46f0498b4e"
            "c848f7e14801f84883d2004801d84883d2004889c7498b46f8498b4ec048f7e14801f84883d20049"
            "89c44d8946c04d894ec84d8956d04d8966d8"
        ),
    },
    {
        "name": 'q1-register-r12',
        "hex": (
            "4c89e0498b4ec048f7e14989c04889d34c89e0498b4ec848f7e14801d84883d2004889c34889d64c"
            "89e0498b4ed048f7e14801f04883d2004889c64889d74c89e0498b4ed848f7e14801f84883d20048"
            "89c7498b46e8498b4ec048f7e14801d84883d2004989c14889d3498b46e8498b4ec848f7e14801f0"
            "4883d2004801d84883d2004889c64889d3498b46e8498b4ed048f7e14801f84883d2004801d84883"
            "d2004889c7498b46f0498b4ec048f7e14801f04883d2004989c24889d3498b46f0498b4ec848f7e1"
            "4801f84883d2004801d84883d2004889c7498b46f8498b4ec048f7e14801f84883d2004989c34d89"
            "46c04d894ec84d8956d04d895ed8"
        ),
    },
    {
        "name": 'p1-register-r12',
        "hex": (
            "498b46e04c89e148f7e14989c04889d3498b46e0498b4ec848f7e14801d84883d2004889c34889d6"
            "498b46e0498b4ed048f7e14801f04883d2004889c64889d7498b46e0498b4ed848f7e14801f84883"
            "d2004889c7498b46e84c89e148f7e14801d84883d2004989c14889d3498b46e8498b4ec848f7e148"
            "01f04883d2004801d84883d2004889c64889d3498b46e8498b4ed048f7e14801f84883d2004801d8"
            "4883d2004889c7498b46f04c89e148f7e14801f04883d2004989c24889d3498b46f0498b4ec848f7"
            "e14801f84883d2004801d84883d2004889c7498b46f84c89e148f7e14801f84883d2004989c34d89"
            "46c04d894ec84d8956d04d895ed8"
        ),
    },
    {
        "name": 'live-register-r12',
        "hex": (
            "498b46e0498b4ec048f7e14989c04889d3498b46e0498b4ec848f7e14801d84883d2004889c34889"
            "d6498b46e0498b4ed048f7e14801f04883d2004889c64889d7498b46e0498b4ed848f7e14801f848"
            "83d2004889c7498b46e8498b4ec048f7e14801d84883d2004989c14889d3498b46e8498b4ec848f7"
            "e14801f04883d2004801d84883d2004889c64889d3498b46e8498b4ed048f7e14801f84883d20048"
            "01d84883d2004889c7498b46f0498b4ec048f7e14801f04883d2004989c24889d3498b46f0498b4e"
            "c848f7e14801f84883d2004801d84883d2004889c7498b46f8498b4ec048f7e14801f84883d20049"
            "89c34d8946c04d894ec84d8956d04d895ed8"
        ),
    },
    {
        "name": 'live-register-rax',
        "hex": (
            "498946b0498b46e0498b4ec048f7e14989c04889d3498b46e0498b4ec848f7e14801d84883d20048"
            "89c34889d6498b46e0498b4ed048f7e14801f04883d2004889c64889d7498b46e0498b4ed848f7e1"
            "4801f84883d2004889c7498b46e8498b4ec048f7e14801d84883d2004989c14889d3498b46e8498b"
            "4ec848f7e14801f04883d2004801d84883d2004889c64889d3498b46e8498b4ed048f7e14801f848"
            "83d2004801d84883d2004889c7498b46f0498b4ec048f7e14801f04883d2004989c24889d3498b46"
            "f0498b4ec848f7e14801f84883d2004801d84883d2004889c7498b46f8498b4ec048f7e14801f848"
            "83d2004989c34d8946c04d894ec84d8956d04d895ed8"
        ),
    },
    {
        "name": 'live-register-rdx',
        "hex": (
            "498956b0498b46e0498b4ec048f7e14989c04889d3498b46e0498b4ec848f7e14801d84883d20048"
            "89c34889d6498b46e0498b4ed048f7e14801f04883d2004889c64889d7498b46e0498b4ed848f7e1"
            "4801f84883d2004889c7498b46e8498b4ec048f7e14801d84883d2004989c14889d3498b46e8498b"
            "4ec848f7e14801f04883d2004801d84883d2004889c64889d3498b46e8498b4ed048f7e14801f848"
            "83d2004801d84883d2004889c7498b46f0498b4ec048f7e14801f04883d2004989c24889d3498b46"
            "f0498b4ec848f7e14801f84883d2004801d84883d2004889c7498b46f8498b4ec048f7e14801f848"
            "83d2004989c34d8946c04d894ec84d8956d04d895ed8"
        ),
    },
]


_COMPILER_MUL_BRANCHES = tuple(
    pytest.param(
        q2_zero,
        q3_zero,
        q4_zero,
        id=(
            f"q2={'zero' if q2_zero else 'full'}-"
            f"q3={'zero' if q3_zero else 'full'}-"
            f"q4={'zero' if q4_zero else 'full'}"
        ),
    )
    for q2_zero in (False, True)
    for q3_zero in (False, True)
    for q4_zero in (False, True)
)


def _prove_unsat(label: str, mismatches, *, timeout_ms: int = 10_000) -> None:
    """所有 lemma 都按“找反例”写；只有 UNSAT 才表示等价成立。"""
    mismatches = list(mismatches)
    if not mismatches:
        raise AssertionError(f"{label} has no proof obligations")
    solver = Solver()
    solver.set(timeout=timeout_ms)
    solver.add(Or(*mismatches))
    result = solver.check()
    assert result == unsat, f"{label}: solver returned {result}"


def _full_template_instruction_hex() -> list[str]:
    """取 canonical full MUL slice 作为生成分支变体的模板。"""
    # 这里只把 canonical full MUL 当作切片种子；证明目标是下方生成的 compiler 分支族。
    return [
        insn.bytes.hex()
        for insn in disassemble_hex(X86_MUL_CORE_HEX_SEQUENCE, 0)
    ]


def _compiler_mul_hex_variant(
    *,
    q2_zero: bool,
    q3_zero: bool,
    q4_zero: bool,
) -> str:
    """按 q2/q3/q4 零值分支拼出 compiler MUL 机器码变体。"""
    insns = _full_template_instruction_hex()
    q2_row = ["4989d9"] if q2_zero else insns[25:49]  # mov r9, rbx
    q3_row = ["4989f2"] if q3_zero else insns[49:64]  # mov r10, rsi
    q4_row = ["4989fb"] if q4_zero else insns[64:70]  # mov r11, rdi
    return "".join(insns[:25] + q2_row + q3_row + q4_row + insns[70:74])


def _compiler_mul_insns(
    *,
    q2_zero: bool = False,
    q3_zero: bool = False,
    q4_zero: bool = False,
) -> list[X86Instruction]:
    """反汇编指定零值分支形态的 compiler MUL 变体。"""
    return disassemble_hex(
        _compiler_mul_hex_variant(
            q2_zero=q2_zero,
            q3_zero=q3_zero,
            q4_zero=q4_zero,
        ),
        0,
    )


def _branch_id(q2_zero: bool, q3_zero: bool, q4_zero: bool) -> str:
    """生成 pytest id / 诊断信息里使用的分支名。"""
    return (
        f"q2={'zero' if q2_zero else 'full'}-"
        f"q3={'zero' if q3_zero else 'full'}-"
        f"q4={'zero' if q4_zero else 'full'}"
    )


def _mul_insns(insns: list[X86Instruction]) -> list[X86Instruction]:
    """筛出 slice 中所有 unsigned mul 指令。"""
    return [insn for insn in insns if insn.mnemonic.lower() == "mul"]


def _add_adc_pairs(insns: list[X86Instruction]):
    """收集 compiler 使用的 add-rax / adc-rdx carry pair。"""
    pairs = []
    for index, insn in enumerate(insns[:-1]):
        ops = parse_operands(insn)
        if insn.mnemonic.lower() != "add" or ops.get("dest_reg") != Register.RAX:
            continue
        adc = insns[index + 1]
        adc_ops = parse_operands(adc)
        assert adc.mnemonic.lower() == "adc"
        assert adc_ops.get("dest_reg") == Register.RDX
        assert adc_ops.get("immediate") == 0
        pairs.append((insn, adc, ops.get("src_reg")))
    return pairs


def _compiler_branch_mul_limbs(
    p,
    q,
    *,
    q2_zero: bool,
    q3_zero: bool,
    q4_zero: bool,
) -> Uint256:
    """手写 compiler 分支化 limb 乘法算法，作为 glue 的中间规格。"""
    carry0, z0 = _mul64(p[0], q[0])
    carry0, res1 = _umul_hop(carry0, p[1], q[0])
    carry0, res2 = _umul_hop(carry0, p[2], q[0])
    carry0, res3 = _umul_hop(carry0, p[3], q[0])

    if q2_zero:
        z1 = res1
    else:
        carry1, z1 = _umul_hop(res1, p[0], q[1])
        carry1, res2 = _umul_step(res2, p[1], q[1], carry1)
        carry1, res3 = _umul_step(res3, p[2], q[1], carry1)

    if q3_zero:
        z2 = res2
    else:
        carry2, z2 = _umul_hop(res2, p[0], q[2])
        carry2, res3 = _umul_step(res3, p[1], q[2], carry2)

    if q4_zero:
        z3 = res3
    else:
        _discarded_carry, z3 = _umul_hop(res3, p[0], q[3])
    return Uint256(z0, z1, z2, z3)


def _effective_q_limbs(
    q,
    *,
    q2_zero: bool,
    q3_zero: bool,
    q4_zero: bool,
):
    """把被编译期零值分支优化掉的 q limb 规范化为 0。"""
    return [
        q[0],
        _ZERO64 if q2_zero else q[1],
        _ZERO64 if q3_zero else q[2],
        _ZERO64 if q4_zero else q[3],
    ]


def _branch_z3_formula(
    p,
    q,
    carry0,
    carry1,
    carry2,
    *,
    q2_zero: bool,
    q3_zero: bool,
    q4_zero: bool,
):
    """构造 z3 最高 limb 的线性 partial-product 公式。"""
    formula = p[3] * q[0] + carry0
    if not q2_zero:
        formula = formula + p[2] * q[1] + carry1
    if not q3_zero:
        formula = formula + p[1] * q[2] + carry2
    if not q4_zero:
        formula = formula + p[0] * q[3]
    return formula


def _written_registers(insns: list[X86Instruction]) -> set[Register]:
    """保守收集 slice 会写到的普通寄存器。"""
    writes: set[Register] = set()
    for insn in insns:
        mnemonic = insn.mnemonic.lower()
        ops = parse_operands(insn)
        if mnemonic == "mul":
            writes.update({Register.RAX, Register.RDX})
            continue
        dest = ops.get("dest_reg")
        if dest is not None and mnemonic in {"mov", "movabs", "add", "adc"}:
            writes.add(dest)
    return writes


def _summary_and_slice(insns: list[X86Instruction]):
    """从一段指令里发现唯一 MUL summary，并返回它覆盖的 raw slice。"""
    blocks = identify_basic_blocks(insns)
    summaries = discover_mul_summaries(blocks, strict=True)

    assert len(summaries) == 1
    summary = next(iter(summaries.values()))
    block = next(block for block in blocks if block.start_addr == summary.start_block_addr)
    slice_insns = block.instructions[
        summary.start_instruction_index:summary.continuation_instruction_index
    ]
    return summary, slice_insns


def _assert_raw_primitives_match_limb_helpers(
    insns: list[X86Instruction],
    *,
    label: str,
) -> None:
    """证明 raw slice 里的基础算术指令和本文件的 limb helper 语义一致。

    这个 lemma 故意只看孤立的 ``mul`` 和 ``add/adc`` 原语，不证明整段
    compileEVMMul 数据流正确。它的作用是把 x86 symbolic executor 的底层
    指令建模与后续 composition/glue lemma 使用的 ``_mul64``、``_add64``
    对齐；如果端到端 glue 失败，可以先排除基础指令语义漂移的问题。
    """
    summary, slice_insns = _summary_and_slice(insns)
    _ = summary

    # x86 ``mul r/m64`` 隐式读取 RAX 和操作数，写回 RDX:RAX。
    # 这里给每条真实 slice 中出现的 mul 放入任意符号输入，证明其输出
    # 对所有 64-bit 输入都等于 helper 的 64x64 -> hi/lo 拆分。
    for index, insn in enumerate(_mul_insns(slice_insns)):
        ops = parse_operands(insn)
        param_reg = ops.get("dest_reg")
        assert param_reg is not None
        assert param_reg not in {Register.RAX, Register.RDX}

        rax = BitVec(f"mul_primitive_{index}_rax", 64)
        param = BitVec(f"mul_primitive_{index}_param", 64)
        state = SMTState()
        state.x86_registers.set_register(Register.RAX, rax)
        state.x86_registers.set_register(param_reg, param)

        state = _execute_insns(state, [insn])
        expected_hi, expected_lo = _mul64(rax, param)
        _prove_unsat(
            f"{label} mul primitive {index}",
            (
                state.x86_registers.get_register(Register.RAX) != expected_lo,
                state.x86_registers.get_register(Register.RDX) != expected_hi,
            ),
        )

    # compiler 的 partial-product 累加总是成对使用 ``add rax, src`` 和
    # ``adc rdx, 0``：低 64 位相加产生的 carry 必须继续加到高 64 位。
    # 这段只证明每个 pair 的局部算术，不关心这些 pair 在整段 slice 中
    # 连到哪个中间寄存器；真实 wiring 由 glue lemma 覆盖。
    for index, (add, adc, src_reg) in enumerate(_add_adc_pairs(slice_insns)):
        assert src_reg is not None
        assert src_reg not in {Register.RAX, Register.RDX}

        lo = BitVec(f"add_adc_{index}_lo", 64)
        hi = BitVec(f"add_adc_{index}_hi", 64)
        addend = BitVec(f"add_adc_{index}_addend", 64)
        state = SMTState()
        state.x86_registers.set_register(Register.RAX, lo)
        state.x86_registers.set_register(Register.RDX, hi)
        state.x86_registers.set_register(src_reg, addend)

        state = _execute_insns(state, [add, adc])
        expected_lo, carry = _add64(lo, addend)
        expected_hi, _ = _add64(hi, _ZERO64, carry)
        _prove_unsat(
            f"{label} add/adc primitive {index}",
            (
                state.x86_registers.get_register(Register.RAX) != expected_lo,
                state.x86_registers.get_register(Register.RDX) != expected_hi,
            ),
        )


def _assert_frame_and_clobbers_are_covered(
    insns: list[X86Instruction],
    *,
    label: str,
):
    """检查 raw slice 的内存写和寄存器写都被 summary contract 覆盖。"""
    summary, slice_insns = _summary_and_slice(insns)
    q2_zero, q3_zero, q4_zero = _zero_branch_flags(summary)

    mul_count = len(_mul_insns(slice_insns))
    add_adc_count = len(_add_adc_pairs(slice_insns))
    add_count = sum(1 for insn in slice_insns if insn.mnemonic.lower() == "add")
    adc_count = sum(1 for insn in slice_insns if insn.mnemonic.lower() == "adc")
    assert {insn.mnemonic.lower() for insn in slice_insns} <= {
        "mov",
        "movabs",
        "mul",
        "add",
        "adc",
    }, label
    assert mul_count == (
        10 - (3 if q2_zero else 0) - (2 if q3_zero else 0) - (1 if q4_zero else 0)
    ), label
    assert add_adc_count == (
        12 - (5 if q2_zero else 0) - (3 if q3_zero else 0) - (1 if q4_zero else 0)
    ), label
    # 每条 add/adc 都必须落在已配对的 add-rax/adc-rdx 模式里，
    # 不允许存在未被 pair 检查覆盖的散装 add 或 adc。
    assert add_count == add_adc_count, label
    assert adc_count == add_adc_count, label

    # Frame soundness：raw slice 只能写 summary 声明的 4 个 stack result limb。
    store_offsets = []
    for insn in slice_insns:
        ops = parse_operands(insn)
        if not _is_stack_store(insn):
            # 任何其它 memory-destination 指令都表示 summary 漏建模了内存效果。
            assert not (ops.get("is_memory") and ops.get("dest_reg") is None), label
            continue
        assert ops.get("base_reg") == Register.R14, label
        assert ops.get("memory_size") == 8, label
        store_offsets.append(ops.get("offset"))
    assert tuple(store_offsets) == summary.result_stack_offsets, label

    # Clobber soundness：raw slice 写过的普通寄存器必须都由 summary freshen。
    raw_writes = _written_registers(slice_insns)
    assert raw_writes <= set(summary.clobber_registers), label
    # 保留寄存器（R13/R14/R15）既不能被写，也不能被 summary havoc。
    reserved = {Register.R13, Register.R14, Register.R15}
    assert not (raw_writes & reserved), label
    assert not (set(summary.clobber_registers) & reserved), label


def _assert_raw_slice_refines_summary_semantics(
    insns: list[X86Instruction],
    *,
    label: str,
    timeout_ms: int = 120_000,
) -> None:
    """Glue lemma：raw slice 端到端符号执行 == compiler limb 算法。

    实现已提升为生产模块 x86_64/summaries/mul_proof.py（per-hit proof 用的
    同一份代码）；这里只保留 discover + 切片的薄 wrapper，保证测试证明的
    就是生产 verification 折叠前实际运行的证明逻辑。
    """
    summary, slice_insns = _summary_and_slice(insns)
    prove_mul_slice_refines_summary(
        summary,
        slice_insns,
        timeout_ms=timeout_ms,
        label=label,
    )


@pytest.mark.parametrize("q2_zero,q3_zero,q4_zero", _COMPILER_MUL_BRANCHES)
def test_compiler_mul_raw_slice_refines_summary_semantics(
    q2_zero: bool,
    q3_zero: bool,
    q4_zero: bool,
):
    """glue lemma：证明 raw x86 slice 的真实数据流等于分支化 limb 算法。"""
    insns = _compiler_mul_insns(
        q2_zero=q2_zero,
        q3_zero=q3_zero,
        q4_zero=q4_zero,
    )
    _assert_raw_slice_refines_summary_semantics(
        insns,
        label=f"manual {_branch_id(q2_zero, q3_zero, q4_zero)}",
    )


@pytest.mark.parametrize("q2_zero,q3_zero,q4_zero", _COMPILER_MUL_BRANCHES)
def test_compiler_mul_output_primitives_match_limb_helpers(
    q2_zero: bool,
    q3_zero: bool,
    q4_zero: bool,
):
    """primitive lemma：证明 slice 中的 mul/add/adc 原语等于 limb helper。"""
    insns = _compiler_mul_insns(
        q2_zero=q2_zero,
        q3_zero=q3_zero,
        q4_zero=q4_zero,
    )
    _assert_raw_primitives_match_limb_helpers(
        insns,
        label=f"q2_zero={q2_zero}, q3_zero={q3_zero}, q4_zero={q4_zero}",
    )


def test_x86_order_umul_step_matches_normalized_step():
    """证明 x86 加法顺序和 composition 使用的规范顺序等价。"""
    z = BitVec("umul_step_equiv_z", 64)
    x = BitVec("umul_step_equiv_x", 64)
    y = BitVec("umul_step_equiv_y", 64)
    carry = BitVec("umul_step_equiv_carry", 64)

    # x86 为了贴合指令流先加 z；composition 使用更利于 Z3 的规范顺序。
    x86_hi, x86_lo = _umul_step_x86_order(z, x, y, carry)
    norm_hi, norm_lo = _umul_step(z, x, y, carry)
    _prove_unsat(
        "x86-order umul_step matches normalized umul_step",
        (x86_hi != norm_hi, x86_lo != norm_lo),
    )


@pytest.mark.parametrize("q2_zero,q3_zero,q4_zero", _COMPILER_MUL_BRANCHES)
def test_compiler_mul_z3_accumulator_matches_branch_formula(
    q2_zero: bool,
    q3_zero: bool,
    q4_zero: bool,
):
    """证明 z3 的累加链可折叠成显式 partial-product 公式。"""
    p = [BitVec(f"z3_acc_p{index}", 64) for index in range(4)]
    q = [BitVec(f"z3_acc_q{index}", 64) for index in range(4)]
    carry0 = BitVec("z3_acc_carry0", 64)
    carry1 = BitVec("z3_acc_carry1", 64)
    carry2 = BitVec("z3_acc_carry2", 64)

    _, res3 = _umul_hop(carry0, p[3], q[0])
    if not q2_zero:
        _, res3 = _umul_step(res3, p[2], q[1], carry1)
    if not q3_zero:
        _, res3 = _umul_step(res3, p[1], q[2], carry2)
    if q4_zero:
        z3 = res3
    else:
        _, z3 = _umul_hop(res3, p[0], q[3])

    # z3 单独拆公式，避免整段 256-bit 乘法一次性展开导致 solver unknown。
    formula = _branch_z3_formula(
        p,
        q,
        carry0,
        carry1,
        carry2,
        q2_zero=q2_zero,
        q3_zero=q3_zero,
        q4_zero=q4_zero,
    )
    _prove_unsat(
        (
            f"z3 accumulator formula q2_zero={q2_zero}, "
            f"q3_zero={q3_zero}, q4_zero={q4_zero}"
        ),
        (z3 != formula,),
    )


@pytest.mark.parametrize("q2_zero,q3_zero,q4_zero", _COMPILER_MUL_BRANCHES)
def test_compiler_mul_z3_branch_formula_matches_uint256_semantics(
    q2_zero: bool,
    q3_zero: bool,
    q4_zero: bool,
):
    """证明 z3 显式公式等于 Uint256.mul_semantics 的最高 limb。"""
    p = [BitVec(f"z3_formula_p{index}", 64) for index in range(4)]
    q = [BitVec(f"z3_formula_q{index}", 64) for index in range(4)]
    effective_q = _effective_q_limbs(
        q,
        q2_zero=q2_zero,
        q3_zero=q3_zero,
        q4_zero=q4_zero,
    )

    carry0, _z0 = _mul64(p[0], effective_q[0])
    carry0, res1 = _umul_hop(carry0, p[1], effective_q[0])
    carry0, res2 = _umul_hop(carry0, p[2], effective_q[0])
    carry1, _z1 = _umul_hop(res1, p[0], effective_q[1])
    carry1, res2 = _umul_step(res2, p[1], effective_q[1], carry1)
    carry2, _z2 = _umul_hop(res2, p[0], effective_q[2])

    formula = _branch_z3_formula(
        p,
        effective_q,
        carry0,
        carry1,
        carry2,
        q2_zero=q2_zero,
        q3_zero=q3_zero,
        q4_zero=q4_zero,
    )
    expected = Uint256(*p).mul_semantics(Uint256(*effective_q))
    _prove_unsat(
        (
            f"z3 formula vs uint256 q2_zero={q2_zero}, "
            f"q3_zero={q3_zero}, q4_zero={q4_zero}"
        ),
        (formula != expected.z3,),
    )


@pytest.mark.parametrize("q2_zero,q3_zero,q4_zero", _COMPILER_MUL_BRANCHES)
def test_compiler_mul_limb_composition_matches_uint256_semantics(
    q2_zero: bool,
    q3_zero: bool,
    q4_zero: bool,
):
    """composition lemma：证明分支化 limb 算法等于 summary 乘法语义。"""
    p = [BitVec(f"mul_composition_p{index}", 64) for index in range(4)]
    q = [BitVec(f"mul_composition_q{index}", 64) for index in range(4)]

    # 这里证明 compiler 分支后的 partial products 仍等于 summary 乘法语义。
    composed = _compiler_branch_mul_limbs(
        p,
        q,
        q2_zero=q2_zero,
        q3_zero=q3_zero,
        q4_zero=q4_zero,
    )
    effective_q = _effective_q_limbs(
        q,
        q2_zero=q2_zero,
        q3_zero=q3_zero,
        q4_zero=q4_zero,
    )
    expected = Uint256(*p).mul_semantics(Uint256(*effective_q))
    for label, actual, expected_limb in (
        ("z0", composed.z0, expected.z0),
        ("z1", composed.z1, expected.z1),
        ("z2", composed.z2, expected.z2),
    ):
        _prove_unsat(
            (
                f"compiler branch q2_zero={q2_zero}, q3_zero={q3_zero}, "
                f"q4_zero={q4_zero} limb {label}"
            ),
            (actual != expected_limb,),
        )


@pytest.mark.parametrize("q2_zero,q3_zero,q4_zero", _COMPILER_MUL_BRANCHES)
def test_compiler_mul_output_frame_and_clobbers_are_covered_by_summary(
    q2_zero: bool,
    q3_zero: bool,
    q4_zero: bool,
):
    """frame/clobber lemma：证明 summary 没漏掉 raw slice 的副作用。"""
    insns = _compiler_mul_insns(
        q2_zero=q2_zero,
        q3_zero=q3_zero,
        q4_zero=q4_zero,
    )
    summary, slice_insns = _summary_and_slice(insns)
    _ = slice_insns

    assert summary.p_limb_locs == (
        StackLimbLocation(-64),
        StackLimbLocation(-56),
        StackLimbLocation(-48),
        StackLimbLocation(-40),
    )
    expected_q_locs = (
        StackLimbLocation(-32),
        ConstLimbLocation(0) if q2_zero else StackLimbLocation(-24),
        ConstLimbLocation(0) if q3_zero else StackLimbLocation(-16),
        ConstLimbLocation(0) if q4_zero else StackLimbLocation(-8),
    )
    assert summary.q_limb_locs == expected_q_locs
    assert summary.result_stack_offsets == (-64, -56, -48, -40)
    _assert_frame_and_clobbers_are_covered(
        insns,
        label=f"manual {_branch_id(q2_zero, q3_zero, q4_zero)}",
    )


def _go_compiler_mul_variants() -> list[dict[str, str]]:
    """返回固化的真实 compiler 输出 fixture。"""
    # 固化自 GOARCH=amd64 的 go-hpc-evm compileEVMMul 当前输出，避免测试运行时调用 Go。
    return list(_GO_COMPILER_MUL_VARIANTS)


def test_go_compiler_generated_mul_outputs_match_proven_summary_contract():
    """fixture guard：固化机器码必须满足同一套 summary proof contract。

    它不证明 MUL summary 的新逻辑（那是 parametrize 测试的职责），而是
    把 GOARCH=amd64 下固化的真实 compileEVMMul 机器码拉回来，验证它们仍精确
    落在本文件已证明的分支模型 + location grammar 之内。本测试直接对固化
    产物做结构断言（零分支 / 指令计数 / location 覆盖 / frame/clobber 边界）
    并逐 fixture 重跑三层 proof，闭合“产物没变 / 产物语义仍正确”的缝隙。
    """
    variants = _go_compiler_mul_variants()
    variants_by_name = {variant["name"]: variant["hex"] for variant in variants}

    # (1) 零分支自洽：固化的 8 个 branch-* 变体必须逐字节等于“从 full 模板按
    # q2/q3/q4 零值规则拼装”的结果。任一方（compiler 输出或拼装算法）漂移即失败。
    for q2_zero in (False, True):
        for q3_zero in (False, True):
            for q4_zero in (False, True):
                name = f"branch-{_branch_id(q2_zero, q3_zero, q4_zero)}"
                assert variants_by_name[name] == _compiler_mul_hex_variant(
                    q2_zero=q2_zero,
                    q3_zero=q3_zero,
                    q4_zero=q4_zero,
                )

    # (2) location 覆盖：matcher 抽象的来源空间（stack / constant / register）
    # 里每一个有代表性的形态都必须有对应固化产物。用子集断言——fixture 可以
    # 比最小集合多，但不能少；matcher 支持新寄存器/来源时这里会提醒补 fixture。
    required_representatives = {
        "positive-stack-offsets",
        "q1-constant-zero",
        "q2-nonzero-constant",
        "p1-nonzero-constant",
        "live-register-rax",
        "live-register-rdx",
    }
    required_representatives.update(
        f"{prefix}-{reg}"
        for prefix in ("q1-register", "p1-register", "live-register")
        for reg in ("rcx", "rbx", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12")
    )
    assert required_representatives <= set(variants_by_name)

    # (3) 逐变体重跑完整证明：每个固化产物反汇编后，用生产 matcher 切出 raw slice，
    # 再过 glue / primitive / frame 三层——和线上 per-hit proof 同一份代码。
    # 它守的是“真实产物经 matcher 切片后，语义、底层原语、副作用边界全部成立”。
    seen_hex = set()
    for variant in variants:
        label = variant["name"]
        hex_code = variant["hex"]
        seen_hex.add(hex_code)
        insns = disassemble_hex(hex_code, 0)
        summary, _slice_insns = _summary_and_slice(insns)

        # 端到端 glue：raw slice 数据流 == 分支化 limb 算法（生产 mul_proof 同款）。
        _assert_raw_slice_refines_summary_semantics(insns, label=label)
        # 原语级：每条 mul / add+adc pair 符合 _mul64/_add64，glue 失败时用于定位。
        _assert_raw_primitives_match_limb_helpers(insns, label=label)
        # 副作用边界：指令白名单、零分支计数、frame 写槽、clobber/保留寄存器。
        _assert_frame_and_clobbers_are_covered(insns, label=label)

    # (4) 多样性兜底：去重后不同 hex 必须 > 8（零分支数），证明 fixture 确实还
    # 包含常量/寄存器/stack 等额外形态；变体被删或意外撞重串会让这里失败。
    assert len(seen_hex) > len(_COMPILER_MUL_BRANCHES)
