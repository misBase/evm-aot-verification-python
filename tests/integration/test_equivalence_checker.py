#!/usr/bin/env python3
"""
翻译验证的等价性检查器测试。

本模块包含使用EquivalenceChecker验证EVM字节码和AOT编译的x86-64机器码之间
等价关系的测试。这些测试专注于验证逻辑，包括符号证明和具体值测试。
"""

from __future__ import annotations

import os
import pytest
from evm_ir.json_parser import load_ir_from_json
from evm_ir.program import EVMProgram
from x86_64.program import X86Program
from x86_64.summaries import TRUSTED_SUMMARY_CONFIG
from verification.equivalence_checker import EquivalenceChecker
from verification.program_verifier import ProgramEquivalenceChecker
from state.smt_state import SMTState


# ===========================
# x86-64 机器码常量
# ===========================
# 这些是从AOT编译器输出中提取的

# ADD程序片段，AOT编译器输出，用于程序级等价性测试  对应 data/add_raw.json
# prologue：从 callEngine(R13) 恢复 R14/R15
#   mov r14, [r13+0x38]   ; 加载 stackBase
#   add r14, [r13+0x30]   ; stackBase += stackPointer offset → R14 指向当前栈顶
#   mov r15, [r13+0x10]   ; 加载 memoryBase
# 核心 256-bit ADD：从两个 256-bit 栈 slot 逐 limb 相加，低位到高位传播 carry，
# 并把结果原地写回第一个 operand/result slot。
#   mov rax, [r14-0x40]   ; a.z0
#   add rax, [r14-0x20]   ; a.z0 + b.z0
#   mov rcx, [r14-0x38]   ; a.z1
#   adc rcx, [r14-0x18]   ; a.z1 + b.z1 + carry
#   mov rdx, [r14-0x30]   ; a.z2
#   adc rdx, [r14-0x10]   ; a.z2 + b.z2 + carry
#   mov rbx, [r14-0x28]   ; a.z3
#   adc rbx, [r14-0x08]   ; a.z3 + b.z3 + carry
#   mov [r14-0x40], rax   ; result.z0
#   mov [r14-0x38], rcx   ; result.z1
#   mov [r14-0x30], rdx   ; result.z2
#   mov [r14-0x28], rbx   ; result.z3
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
GO_AMD64_MAX_SLICE_LEN = (1 << 63) - 1


# ===========================
# Pytest 测试夹具
# ===========================

@pytest.fixture
def equivalence_checker() -> EquivalenceChecker:
    """提供具有默认超时的等价性检查器的测试夹具。"""
    return EquivalenceChecker(timeout_ms=10000, verbose=False)


@pytest.fixture
def equivalence_checker_verbose() -> EquivalenceChecker:
    """提供具有详细输出的等价性检查器的测试夹具，用于符号测试。"""
    return EquivalenceChecker(timeout_ms=60000, verbose=True)


def test_verifier_import():
    """测试验证器模块是否可以导入。"""
    # 如果导入失败，将自动抛出异常
    pass


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
    # 这里显式给 step 5 单独的 600s 预算，避免污染主 equivalence timeout 的语义。
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

    EquivalenceChecker 验证三项属性：
    1. 返回条件一致（双方都 return）
    2. 返回长度一致（都是 32 字节）
    3. 返回区域的内存内容一致
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

    EquivalenceChecker 验证 storage 等可观察状态一致，并额外检查 1 个栈元素。
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


def test_verify_two_block_program_pair():
    """验证 two_block.json 与 two_block.hex 的两块控制流 return 结果一致性。

    EVM IR 程序先写入 memory[100]，再通过静态目标 JUMPI 跳到返回块，
    返回 memory[100:132] 的 32 字节结果。
    """
    test_dir = os.path.dirname(__file__)
    ir_path = os.path.join(test_dir, "..", "data", "two_block.json")
    x86_hex_path = os.path.join(test_dir, "..", "data", "two_block.hex")

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
        stack_check=None,
    )

    assert verified, (
        f"two_block program pair verification failed. "
        f"EVM program from {ir_path} and x86 program from {x86_hex_path} "
        f"should produce equivalent return results. Error: {msg}"
    )


def test_verify_three_block_program_pair():
    """验证 three_block.json 与 three_block.hex 的三块控制流 return 结果一致性。

    EVM IR 程序先写入 memory[0x40] 和 memory[0x41]，再通过静态目标 JUMPI
    跳到第三个返回块，返回 memory[0x41:0x42] 的 1 字节结果。
    """
    test_dir = os.path.dirname(__file__)
    ir_path = os.path.join(test_dir, "..", "data", "three_block.json")
    x86_hex_path = os.path.join(test_dir, "..", "data", "three_block.hex")

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
        stack_check=None,
    )

    assert verified, (
        f"three_block program pair verification failed. "
        f"EVM program from {ir_path} and x86 program from {x86_hex_path} "
        f"should produce equivalent return results. Error: {msg}"
    )

def test_jumpi_2block_err_program_pair():
    """验证 jumpi_2block_err.json 与 jumpi_2block_err.hex 的 JUMPI return 结果一致性。

    EVM IR 程序根据 calldata 首字节决定静态 JUMPI 是否跳转，
    分别返回 memory[0x40:0x41] 或 memory[0x41:0x42] 的 1 字节结果。
    """
    test_dir = os.path.dirname(__file__)
    ir_path = os.path.join(test_dir, "..", "data", "jumpi_2block_err.json")
    x86_hex_path = os.path.join(test_dir, "..", "data", "jumpi_2block_err.hex")

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
        stack_check=None,
    )

    assert verified, (
        f"jumpi_2block_err program pair verification failed. "
        f"EVM program from {ir_path} and x86 program from {x86_hex_path} "
        f"should produce equivalent return results. Error: {msg}"
    )


def test_jumpi_2block_ok_program_pair():
    """验证修正后的 jumpi_2block_ok.json 与 jumpi_2block_ok.hex。

    EVM IR 程序根据 calldata 第 0 字节静态 JUMPI：
    条件非零返回 memory[0x41:0x42]，条件为零返回 memory[0x40:0x41]。
    该 fixture 由 Go 侧从同一段修正后的 EVM bytecode 生成 IR 和 x64 机器码。
    """
    test_dir = os.path.dirname(__file__)
    ir_path = os.path.join(test_dir, "..", "data", "jumpi_2block_ok.json")
    x86_hex_path = os.path.join(test_dir, "..", "data", "jumpi_2block_ok.hex")

    compiler_result = load_ir_from_json(ir_path)
    evm_program = EVMProgram(compiler_result)

    with open(x86_hex_path, "r", encoding="utf-8") as f:
        x86_hex_sequence = f.read().strip()
    x86_program = X86Program.from_hex(x86_hex_sequence, base_addr=0)

    checker = ProgramEquivalenceChecker(timeout_ms=600000, verbose=True)
    # The branch condition still depends on symbolic CallData[0], while this
    # fixture fixes the runtime calldata length to the single byte it inspects.
    initial_state = SMTState.create_initial_state(calldata_size_bytes=1)
    verified, msg = checker.verify_program_pair(
        evm_program,
        x86_program,
        initial_state,
        stack_check=None,
    )

    assert verified, (
        f"jumpi_2block_ok program pair verification failed. "
        f"EVM program from {ir_path} and x86 program from {x86_hex_path} "
        f"should produce equivalent return results. Error: {msg}"
    )


def test_verify_perf_erc20_lite_program_pair():
    """验证 perf_erc20_lite 原始 AOT 产物可通过全符号等价性检查。

    该 fixture 覆盖 dispatcher、selector 分支、SHA3 mapping key、SLOAD/SSTORE、
    RETURN/REVERT 等真实合约常见路径。全部输入保持符号化；RETURN 路径
    返回 32 字节，REVERT/错误路径返回空数据。

    这里作为正例 fixture：``perf_erc20_lite.hex`` 应与 IR 等价；
    ``perf_erc20_lite_bug.hex`` 则在相同 IR 下模拟一处 SBB->SUB 的 borrow
    传播 bug，并由负例测试验证 checker 能抓到反例。

    验证使用 path observations 保留终止路径，不先合并完整 memory Array；
    x86 CFG 开启合流点 merge，并用 TRUSTED_SUMMARY_CONFIG 覆盖
    CALLDATALOAD 等高成本片段。

    EVM CALLDATALOAD 处的 ``offset 高 192-bit == 0`` 假设通过 SMTState.assumptions
    在 to_z3 末尾收集，再由 program_verifier 注入到 等价性检查的 path
    condition，对 vacuous（两侧 overflow 都返 0）分支剪枝以避免 256-bit carry
    chain。详见 tests/support/calldataload_analysis/README.md。
    """
    test_dir = os.path.dirname(__file__)
    ir_path = os.path.join(test_dir, "..", "data", "perf_erc20_lite.json")
    x86_hex_path = os.path.join(test_dir, "..", "data", "perf_erc20_lite.hex")

    compiler_result = load_ir_from_json(ir_path)
    evm_program = EVMProgram(compiler_result)

    with open(x86_hex_path, "r", encoding="utf-8") as f:
        x86_hex_sequence = f.read().strip()
    x86_program = X86Program.from_hex(x86_hex_sequence, base_addr=0)

    checker = ProgramEquivalenceChecker(timeout_ms=1200000, verbose=False)
    initial_state = SMTState.create_initial_state()
    verified, msg = checker.verify_program_pair(
        evm_program,
        x86_program,
        initial_state,
        stack_check=None,
        path_observations=True,
        path_pair_workers=4,
        enable_merge=True,
        summary_config=TRUSTED_SUMMARY_CONFIG,
    )

    assert verified, (
        f"perf_erc20_lite program pair verification failed. "
        f"EVM program from {ir_path} and x86 program from {x86_hex_path} "
        f"should produce equivalent observable results. Error: {msg}"
    )
    calldataload_stats = x86_program.last_summary_stats["calldataload"]
    assert calldataload_stats["discovered"] == 5
    assert calldataload_stats["hits"] == 5


def test_detects_perf_erc20_lite_sbb_to_sub_bug():
    """验证 perf_erc20_lite 中的 256-bit SUB borrow 传播错误可被检测。

    perf_erc20_lite_bug.hex 仅把 0x318b 处的 ``sbb rdi, rcx`` 改为
    ``sub rdi, rcx``，模拟编译器漏传播 borrow 的微小机器码 bug。
    """
    test_dir = os.path.dirname(__file__)
    ir_path = os.path.join(test_dir, "..", "data", "perf_erc20_lite.json")
    x86_hex_path = os.path.join(test_dir, "..", "data", "perf_erc20_lite_bug.hex")

    compiler_result = load_ir_from_json(ir_path)
    evm_program = EVMProgram(compiler_result)

    with open(x86_hex_path, "r", encoding="utf-8") as f:
        x86_hex_sequence = f.read().strip()
    x86_program = X86Program.from_hex(x86_hex_sequence, base_addr=0)

    checker = ProgramEquivalenceChecker(timeout_ms=1200000, verbose=False)
    initial_state = SMTState.create_initial_state()
    verified, msg = checker.verify_program_pair(
        evm_program,
        x86_program,
        initial_state,
        stack_check=None,
        path_observations=True,
        path_pair_workers=4,
        enable_merge=True,
        summary_config=TRUSTED_SUMMARY_CONFIG,
    )

    assert not verified
    assert msg is not None
    assert "COUNTEREXAMPLE" in msg


def test_verify_muti_block_program_pair_full():
    """使用 muti_block.json 与 muti_block.hex 进行 path observation 等价验证。"""
    test_dir = os.path.dirname(__file__)
    ir_path = os.path.join(test_dir, "..", "data", "muti_block.json")
    x86_hex_path = os.path.join(test_dir, "..", "data", "muti_block.hex")

    compiler_result = load_ir_from_json(ir_path)
    evm_program = EVMProgram(compiler_result)

    with open(x86_hex_path, "r", encoding="utf-8") as f:
        x86_hex_sequence = f.read().strip()
    x86_program = X86Program.from_hex(x86_hex_sequence, base_addr=X86_MUTI_BLOCK_BASE_ADDR)

    checker = ProgramEquivalenceChecker(timeout_ms=1200000, verbose=False)
    initial_state = SMTState.create_initial_state(
        calldata_size_max_bytes=GO_AMD64_MAX_SLICE_LEN,
    )
    initial_state.abstract_calldataload_words = True
    verified, msg = checker.verify_program_pair(
        evm_program,
        x86_program,
        initial_state,
        stack_check=None,
        path_observations=True,
        # 并行 pair checker 现在按 EVM terminal path 分组；实际 worker 数会受
        # EVM path 数限制，同时每个 worker 保留本 fixture 需要的 aggregate
        # x86-memory fallback。
        path_pair_workers=4,
        # 对这个样本，merge 只把 x86 终止路径从 30 条降到 26 条，
        # 却会把大的 path-conditioned ITE 注入 stack/storage 表达式。
        enable_merge=False,
        summary_config=TRUSTED_SUMMARY_CONFIG,
        x86_reachability_timeout_ms=250,
    )

    assert verified, (
        f"muti_block program pair verification failed. "
        f"EVM program from {ir_path} and x86 program from {x86_hex_path} "
        f"should produce equivalent observable results. Error: {msg}"
    )
    calldataload_stats = x86_program.last_summary_stats["calldataload"]
    assert calldataload_stats["discovered"] == 8
    assert calldataload_stats["hits"] == 8


@pytest.mark.slow
def test_verify_muti_block_08_program_pair_full():
    """使用 muti_block_08.json 与 muti_block_08.hex 进行 path observation 等价验证。"""
    test_dir = os.path.dirname(__file__)
    ir_path = os.path.join(test_dir, "..", "data", "muti_block_08.json")
    x86_hex_path = os.path.join(test_dir, "..", "data", "muti_block_08.hex")

    compiler_result = load_ir_from_json(ir_path)
    evm_program = EVMProgram(compiler_result)

    with open(x86_hex_path, "r", encoding="utf-8") as f:
        x86_hex_sequence = f.read().strip()
    x86_program = X86Program.from_hex(x86_hex_sequence, base_addr=X86_MUTI_BLOCK_08_BASE_ADDR)

    checker = ProgramEquivalenceChecker(timeout_ms=1200000, verbose=False)
    initial_state = SMTState.create_initial_state(
        calldata_size_max_bytes=GO_AMD64_MAX_SLICE_LEN,
    )
    initial_state.abstract_calldataload_words = True
    verified, msg = checker.verify_program_pair(
        evm_program,
        x86_program,
        initial_state,
        stack_check=None,
        path_observations=True,
        path_pair_workers=4,
        enable_merge=False,
        summary_config=TRUSTED_SUMMARY_CONFIG,
        x86_reachability_timeout_ms=250,
    )

    assert verified, (
        f"muti_block_08 program pair verification failed. "
        f"EVM program from {ir_path} and x86 program from {x86_hex_path} "
        f"should produce equivalent observable results. Error: {msg}"
    )
    calldataload_stats = x86_program.last_summary_stats["calldataload"]
    assert calldataload_stats["discovered"] == 3
    assert calldataload_stats["hits"] == 8
