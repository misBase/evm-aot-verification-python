#!/usr/bin/env python3
"""
翻译验证的精化检查器测试。

本模块包含使用RefinementChecker验证EVM字节码和AOT编译的x86-64机器码之间
精化关系的测试。这些测试专注于验证逻辑，包括符号证明和具体值测试。
"""

from __future__ import annotations

import os
import pytest
from typing import List, Dict
from z3 import BitVecVal, BitVec, Distinct, Solver, unsat
from common.uint256 import Uint256
from evm_ir.semantics import EVMIRSemantics
from evm_ir.json_parser import load_ir_from_json
from evm_ir.program import EVMProgram
from x86_64.program import X86Program
from verification.refinement_checker import RefinementChecker
from verification.program_verifier import ProgramEquivalenceChecker
from state.smt_state import SMTState


# ===========================
# x86-64 机器码常量
# ===========================
# 这些是从AOT编译器输出中提取的

# ADD裸核心（无 prologue/epilogue），用于符号等价性测试
# 假设 R14 已是有效栈指针，直接读写相对 R14 的内存：
#   mov rax, [r14-0x40]   ; 加载 a.z0
#   add rax, [r14-0x20]   ; rax += b.z0，设置 CF
#   mov rcx, [r14-0x38]   ; 加载 a.z1
#   adc rcx, [r14-0x18]   ; rcx += b.z1 + CF
#   mov rdx, [r14-0x30]   ; 加载 a.z2
#   adc rdx, [r14-0x10]   ; rdx += b.z2 + CF
#   mov rbx, [r14-0x28]   ; 加载 a.z3
#   adc rbx, [r14-0x08]   ; rbx += b.z3 + CF
#   mov [r14-0x40], rax   ; 写回 result.z0
#   mov [r14-0x38], rcx   ; 写回 result.z1
#   mov [r14-0x30], rdx   ; 写回 result.z2
#   mov [r14-0x28], rbx   ; 写回 result.z3
X86_ADD_CORE_HEX_SEQUENCE = "498b46c0490346e0498b4ec849134ee8498b56d0491356f0498b5ed849135ef8498946c049894ec8498956d049895ed8"
X86_ADD_CORE_BASE_ADDR = 0x6c

# ADD程序片段，AOT编译器输出，用于程序级等价性测试  对应 data/add_raw.json
# prologue：从 callEngine(R13) 恢复 R14/R15
#   mov r14, [r13+0x38]   ; 加载 stackBase
#   add r14, [r13+0x30]   ; stackBase += stackPointer offset → R14 指向当前栈顶
#   mov r15, [r13+0x10]   ; 加载 memoryBase
# 核心 256-bit ADD（同 X86_ADD_CORE_HEX_SEQUENCE）：
#   ADD裸核心
# epilogue：更新 callEngine 状态后返回
#   mov byte [r13+0xe0], 2        ; status = 2（正常返回）
#   mov qword [r13+0x28], -4      ; sp -= 4 limbs（弹出 b，a 原地更新为结果）
#   ret
X86_ADD_HEX_SEQUENCE = "4d8b75384d0375304d8b7d10498b46c0490346e0498b4ec849134ee8498b56d0491356f0498b5ed849135ef8498946c049894ec8498956d049895ed841c685e00000000249c74528fcffffffc3"
X86_ADD_BASE_ADDR = 0x0

# 完整的ADD程序序列，包含PUSH        对应 data/add_with_push.json
# 包括初始化、错误处理和ADD操作
X86_ADD_FULL_HEX_SEQUENCE = "4d8b75384d0375304d8b7d10498b45704883f80672214883e80649894570498b45304883f80072204883f841732b4d8b75384901c6eb3341c685e00000000c49c7452800000000c341c685e00000000e49c7452800000000c341c685e00000000f49c7452800000000c348c7c0600000004883c01048c7c1000000004883d10048c7c2000000004883d20048c7c3000000004883d30049890649894e084989561049895e1841c685e00000000249c7452804000000c3"
X86_ADD_FULL_BASE_ADDR = 0x0

# muti_block 程序级样本（文件中存放十六进制机器码）
X86_MUTI_BLOCK_BASE_ADDR = 0x0
X86_MUTI_BLOCK_08_BASE_ADDR = 0x0


# ===========================
# Pytest 测试夹具
# ===========================

@pytest.fixture
def evm_semantics() -> EVMIRSemantics:
    """提供EVM IR语义实例的测试夹具。"""
    return EVMIRSemantics()


@pytest.fixture
def x86_add_program() -> X86Program:
    """提供x86-64 ADD裸核心程序的测试夹具（无 prologue/epilogue，供符号测试用）。"""
    return X86Program.from_hex(X86_ADD_CORE_HEX_SEQUENCE, base_addr=X86_ADD_CORE_BASE_ADDR)


@pytest.fixture
def refinement_checker() -> RefinementChecker:
    """提供具有默认超时的精化检查器的测试夹具。"""
    return RefinementChecker(timeout_ms=10000, verbose=False)


@pytest.fixture
def refinement_checker_verbose() -> RefinementChecker:
    """提供具有详细输出的精化检查器的测试夹具，用于符号测试。"""
    return RefinementChecker(timeout_ms=60000, verbose=True)


# ===========================
# 测试辅助函数
# ===========================

def _build_memory_for_add_operation(
    val1_limbs: List[BitVec],
    val2_limbs: List[BitVec]
) -> Dict[int, BitVec]:
    """构建用于x86-64 ADD操作的初始内存映射。

    根据AOT编译器的调用约定，将256位操作数的limb映射到栈帧中。
    这是编译器特定的栈帧布局实现细节。

    Args:
        val1_limbs: 第一个操作数的 [z0, z1, z2, z3]（每个64位）
        val2_limbs: 第二个操作数的 [z0, z1, z2, z3]（每个64位）

    Returns:
        内存偏移量到BitVec值的字典
    """
    if len(val1_limbs) != 4 or len(val2_limbs) != 4:
        raise ValueError("Expected 4 limbs for each 256-bit value")

    return {
        -0x40: val1_limbs[0],  # val1.z0 (LSB)
        -0x38: val1_limbs[1],  # val1.z1
        -0x30: val1_limbs[2],  # val1.z2
        -0x28: val1_limbs[3],  # val1.z3 (MSB)
        -0x20: val2_limbs[0],  # val2.z0 (LSB)
        -0x18: val2_limbs[1],  # val2.z1
        -0x10: val2_limbs[2],  # val2.z2
        -0x08: val2_limbs[3],  # val2.z3 (MSB)
    }


# ===========================
# 测试函数
# ===========================

def test_verifier_import():
    """测试验证器模块是否可以导入。"""
    # 如果导入失败，将自动抛出异常
    pass


def test_verify_add_symbolic(
    evm_semantics: EVMIRSemantics,
    x86_add_program: X86Program
):
    """测试符号ADD验证 - 证明对所有输入的正确性。

    这是一个形式化证明，证明x86 ADD实现在语义上等价于EVM ADD操作，
    适用于所有可能的256位输入。

    此测试证明：∀ a, b ∈ Uint256. x86_ADD_Program(a, b) ≡ EVM_ADD_Program(a, b)
    """
    # 创建符号输入
    evm_val1 = Uint256.symbolic("evm_val1")
    evm_val2 = Uint256.symbolic("evm_val2")

    # 构建EVM ADD语义公式
    evm_a_bv = evm_val1.to_bv256()
    evm_b_bv = evm_val2.to_bv256()
    evm_result = evm_semantics.op_semantics.add_semantics(evm_a_bv, evm_b_bv)

    # 使用辅助函数构建x86程序的初始内存
    # 这是AOT编译器使用的栈帧布局（调用约定细节）
    initial_memory = _build_memory_for_add_operation(
        [evm_val1.z0, evm_val1.z1, evm_val1.z2, evm_val1.z3],
        [evm_val2.z0, evm_val2.z1, evm_val2.z2, evm_val2.z3]
    )

    # 构建x86程序语义
    x86_result_dict = x86_add_program.build_program_semantics(initial_memory)
    x86_result = x86_result_dict['semantic_formula']

    # 检查精化关系（证明对所有输入的等价性）：Distinct 应 UNSAT
    s = Solver()
    s.add(Distinct(evm_result, x86_result))
    verified = s.check() == unsat

    assert verified, (
        f"Symbolic ADD verification failed. "
        f"This should prove equivalence for all 256-bit inputs."
    )


def test_verify_add_program_pair():
    """使用JSON IR和x86十六进制序列测试程序级验证。
    
    此测试验证从JSON加载的EVM程序与从十六进制序列创建的x86-64程序之间的等价性，
    类似于main.py中的验证工作流。
    
    此测试使用：
    - add_raw.json: 包含ADD操作的EVM IR JSON文件
    - X86_ADD_HEX_SEQUENCE: ADD操作的x86-64机器码
    - ProgramEquivalenceChecker: 程序级验证器
    """
    # 获取测试数据目录路径
    test_dir = os.path.dirname(__file__)
    ir_path = os.path.join(test_dir, "..", "data", "add_raw.json")
    
    # 从JSON加载EVM程序
    compiler_result = load_ir_from_json(ir_path)
    evm_program = EVMProgram(compiler_result)
    
    # 从十六进制序列创建x86程序
    x86_program = X86Program.from_hex(X86_ADD_HEX_SEQUENCE, base_addr=X86_ADD_BASE_ADDR)
    
    # 使用ProgramEquivalenceChecker验证程序对
    checker = ProgramEquivalenceChecker(timeout_ms=60000, verbose=True)
    initial_state = SMTState.create_initial_state(2)
    verified, msg = checker.verify_program_pair(
        evm_program,
        x86_program,
        initial_state,
        stack_check=2,
    )
    
    assert verified, (
        f"Program pair verification failed. "
        f"EVM program from {ir_path} and x86 program should be equivalent. Error: {msg}"
    )


def test_verify_add_program_pair_full():
    """add_with_push.json和完整x86十六进制序列测试程序级验证。

    add_with_push.json加载的EVM程序（包含TAG、PUSH、PUSH、ADD、STOP操作）
    与包含控制流、错误处理和ADD操作的完整x86-64程序序列之间的等价性。

    此测试使用：
    - add_with_push.json: 包含TAG、PUSH、PUSH、ADD、STOP操作的EVM IR JSON文件
    - X86_ADD_FULL_HEX_SEQUENCE: 包含控制流的完整x86-64机器码
    - ProgramEquivalenceChecker: 程序级验证器
    """
    # 获取测试数据目录路径
    test_dir = os.path.dirname(__file__)
    ir_path = os.path.join(test_dir, "..", "data", "add_with_push.json")
    
    # 从JSON加载EVM程序
    compiler_result = load_ir_from_json(ir_path)
    evm_program = EVMProgram(compiler_result)
    
    # 从完整十六进制序列创建x86程序
    x86_program = X86Program.from_hex(X86_ADD_FULL_HEX_SEQUENCE, base_addr=X86_ADD_FULL_BASE_ADDR)

    # 使用ProgramEquivalenceChecker验证程序对。
    # 这里故意不预置输入槽位：stack_check=1 会从 fixed-slot 坐标系继续向上检查，
    # 允许比较执行过程中写入或仍保持为空理论的符号槽位。
    # 栈一致性检查（step 5）在字节级 Memory Array 上做符号别名分析，
    # 对于含 prologue/epilogue 的完整程序较慢，每个栈槽可能需要数分钟。
    # 这里显式给 step 5 单独的 600s 预算，避免污染主 refinement timeout 的语义。
    checker = ProgramEquivalenceChecker(timeout_ms=600000, verbose=True)
    initial_state = SMTState.create_initial_state()
    verified, msg = checker.verify_program_pair(
        evm_program,
        x86_program,
        initial_state,
        stack_check=1,
        stack_check_timeout_ms=600000,
    )

    assert verified, (
        f"Full program pair verification failed. "
        f"EVM program from {ir_path} and full x86 program should be equivalent. Error: {msg}"
    )


def test_verify_mstore_return_program_pair():
    """验证 mstore_return.json 与 mstore_return.hex 的 return 结果一致性。

    EVM IR 程序：PUSH 9, PUSH 0, MSTORE, PUSH 32, PUSH 0, RETURN
    将值 9 写入 memory[0:32]，然后返回 memory[0:32]（值 9 的 256 位表示）。
    所有值为具体常量，无符号输入。

    RefinementChecker 验证三项属性：
    1. Return 条件一致（双方都 return）
    2. Return 长度一致（都是 32 字节）
    3. Return 区域的内存内容一致
    """
    test_dir = os.path.dirname(__file__)
    ir_path = os.path.join(test_dir, "..", "data", "mstore_return.json")
    x86_hex_path = os.path.join(test_dir, "..", "data", "mstore_return.hex")

    compiler_result = load_ir_from_json(ir_path)
    evm_program = EVMProgram(compiler_result)

    with open(x86_hex_path, "r", encoding="utf-8") as f:
        x86_hex_sequence = f.read().strip()
    x86_program = X86Program.from_hex(x86_hex_sequence, base_addr=0)

    checker = ProgramEquivalenceChecker(timeout_ms=60000000, verbose=True)
    initial_state = SMTState.create_initial_state()
    verified, msg = checker.verify_program_pair(
        evm_program,
        x86_program,
        initial_state,
        stack_check=None,
    )

    assert verified, (
        f"mstore_return program pair verification failed. "
        f"EVM program from {ir_path} and x86 program from {x86_hex_path} "
        f"should produce equivalent return results. Error: {msg}"
    )


def test_verify_sstore_load_program_pair():
    """验证 sstore_load.json 与 sstore_load.hex 的 storage 和栈结果一致性。

    EVM IR 程序：PUSH 199, PUSH 10, SSTORE, PUSH 10, SLOAD, STOP
    将值 199 写入 storage[10]，再从 storage[10] 读回并保留在栈顶。

    RefinementChecker 验证 storage 等可观察状态一致，并额外检查 1 个栈元素。
    """
    test_dir = os.path.dirname(__file__)
    ir_path = os.path.join(test_dir, "..", "data", "sstore_load.json")
    x86_hex_path = os.path.join(test_dir, "..", "data", "sstore_load.hex")

    compiler_result = load_ir_from_json(ir_path)
    evm_program = EVMProgram(compiler_result)

    with open(x86_hex_path, "r", encoding="utf-8") as f:
        x86_hex_sequence = f.read().strip()
    x86_program = X86Program.from_hex(x86_hex_sequence, base_addr=0)

    checker = ProgramEquivalenceChecker(timeout_ms=600000, verbose=True)
    initial_state = SMTState.create_initial_state()
    verified, msg = checker.verify_program_pair(
        evm_program,
        x86_program,
        initial_state,
        stack_check=1,
        stack_check_timeout_ms=600000,
    )

    assert verified, (
        f"sstore_load program pair verification failed. "
        f"EVM program from {ir_path} and x86 program from {x86_hex_path} "
        f"should produce equivalent storage and stack results. Error: {msg}"
    )


@pytest.mark.skip(reason="Not impl well")
def test_verify_muti_block_program_pair_full():
    """使用 muti_block.json 与 muti_block.hex 进行全量程序等价验证。"""
    test_dir = os.path.dirname(__file__)
    ir_path = os.path.join(test_dir, "..", "data", "muti_block.json")
    x86_hex_path = os.path.join(test_dir, "..", "data", "muti_block.hex")

    compiler_result = load_ir_from_json(ir_path)
    evm_program = EVMProgram(compiler_result)

    with open(x86_hex_path, "r", encoding="utf-8") as f:
        x86_hex_sequence = f.read().strip()
    x86_program = X86Program.from_hex(x86_hex_sequence, base_addr=X86_MUTI_BLOCK_BASE_ADDR)

    checker = ProgramEquivalenceChecker(timeout_ms=180000, verbose=False)
    initial_state = SMTState.create_initial_state(0)
    verified, msg = checker.verify_program_pair(evm_program, x86_program, initial_state)

    assert verified, (
        f"muti_block program pair verification failed. "
        f"EVM program from {ir_path} and x86 program from {x86_hex_path} should be equivalent. Error: {msg}"
    )


@pytest.mark.skip(reason="Not impl well")
def test_verify_muti_block_08_program_pair_full():
    """使用 muti_block_08.json 与 muti_block_08.hex 进行全量程序等价验证。"""
    test_dir = os.path.dirname(__file__)
    ir_path = os.path.join(test_dir, "..", "data", "muti_block_08.json")
    x86_hex_path = os.path.join(test_dir, "..", "data", "muti_block_08.hex")

    compiler_result = load_ir_from_json(ir_path)
    evm_program = EVMProgram(compiler_result)

    with open(x86_hex_path, "r", encoding="utf-8") as f:
        x86_hex_sequence = f.read().strip()
    x86_program = X86Program.from_hex(x86_hex_sequence, base_addr=X86_MUTI_BLOCK_08_BASE_ADDR)

    checker = ProgramEquivalenceChecker(timeout_ms=180000, verbose=False)
    initial_state = SMTState.create_initial_state(0)
    verified, msg = checker.verify_program_pair(evm_program, x86_program, initial_state)

    assert verified, (
        f"muti_block_08 program pair verification failed. "
        f"EVM program from {ir_path} and x86 program from {x86_hex_path} should be equivalent. Error: {msg}"
    )
