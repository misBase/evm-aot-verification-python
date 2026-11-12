#!/usr/bin/env python3
"""测试EVM和x86-64操作语义。"""

from common.uint256 import Uint256
from evm_ir.semantics import EVMIRSemantics, EVMOperationSemantics, evm_operator_to_z3
from evm_ir.models import EvmOperator
from evm_ir.status_code import EvmStatusCode, get_status_message, set_terminal_status
from x86_64.semantics import X86SemanticsModel
from x86_64.aot_profile import AOT_COMPILER_PROFILE
from x86_64.models import Register, X86Instruction
from verification.equivalence_checker import EquivalenceChecker
from state.smt_state import SMTState, EVMMemoryState, MemoryDomain
from z3 import And, BitVec, BitVecVal, Not, Select, Store, simplify, is_bv, is_true, Solver, sat, unsat

# x86-64 ADD操作十六进制序列（来自AOT编译器输出）
X86_ADD_HEX_SEQUENCE = "498b46c0490346e0498b4ec849134ee8498b56d0491356f0498b5ed849135ef8498946c049894ec8498956d049895ed8"
X86_ADD_BASE_ADDR = 0x6c


def test_basic_imports():
    """测试所有模块是否可以导入。"""
    # 如果导入失败，将自动抛出异常
    pass


def test_evm_memory_default_zero_initialized():
    """测试 EVM 内存默认是全 0，且 MSize 初始为 0。"""
    mem = EVMMemoryState()

    solver = Solver()
    solver.add(mem.get_byte(BitVecVal(0, 64)) == BitVecVal(0, 8))
    solver.add(mem.get_byte(BitVecVal(123, 64)) == BitVecVal(0, 8))
    solver.add(mem.MSize == BitVecVal(0, 64))
    assert solver.check() == sat


def test_add_semantics():
    """测试EVM和x86-64的ADD语义。"""
    # 测试EVM ADD语义
    evm_op = EVMOperationSemantics()
    val1 = Uint256.from_int(0x60)
    val2 = Uint256.from_int(0x10)
    
    result = evm_op.add_semantics(val1.to_bv256(), val2.to_bv256())
    expected = BitVecVal(0x70, 256)
    
    assert simplify(result == expected), \
        f"EVM ADD failed: expected {expected}, got {simplify(result)}"
    
    # 测试x86 ADD语义
    x86_model = X86SemanticsModel()
    val1_limbs = [BitVecVal(0x60, 64), BitVecVal(0, 64), BitVecVal(0, 64), BitVecVal(0, 64)]
    val2_limbs = [BitVecVal(0x10, 64), BitVecVal(0, 64), BitVecVal(0, 64), BitVecVal(0, 64)]
    
    x86_result = x86_model.build_sequence_from_limbs(
        X86_ADD_HEX_SEQUENCE,
        val1_limbs, 
        val2_limbs,
        base_addr=X86_ADD_BASE_ADDR,
        result_registers=[Register.RBX, Register.RDX, Register.RCX, Register.RAX]
    )
    assert simplify(x86_result == expected), \
        f"x86 ADD failed: expected {expected}, got {simplify(x86_result)}"


def test_equivalence_checker():
    """使用具体值测试等价性检查器。"""
    from z3 import Distinct, Solver

    # 使用等价值测试
    evm_result = BitVecVal(0x70, 256)
    x86_result = BitVecVal(0x70, 256)

    s = Solver()
    s.add(Distinct(evm_result, x86_result))
    assert s.check() == unsat, "Equivalent values should be unsat for Distinct"

    # 使用不同值测试
    evm_result2 = BitVecVal(0x70, 256)
    x86_result2 = BitVecVal(0x71, 256)

    s2 = Solver()
    s2.add(Distinct(evm_result2, x86_result2))
    assert s2.check() == sat, \
        f"Different values should be sat for Distinct (0x70 != 0x71)"


def _to_bv256(value: int):
    """将Python整数转换为256位补码BitVec值。"""
    return BitVecVal(value % (1 << 256), 256)


def test_sdiv_semantics():
    """测试SDIV语义（有符号除法 + 除0）。"""
    evm_op = EVMOperationSemantics()
    cases = [
        (-7, 3, -2),
        (7, -3, -2),
        (-7, -3, 2),
        (7, 0, 0),
    ]
    for a, b, expected in cases:
        result = evm_op.sdiv_semantics(_to_bv256(a), _to_bv256(b))
        assert is_true(simplify(result == _to_bv256(expected)))


def test_smod_semantics():
    """测试SMOD语义（符号跟随被除数 + 除0）。"""
    evm_op = EVMOperationSemantics()
    cases = [
        (-7, 3, -1),
        (7, -3, 1),
        (-7, -3, -1),
        (7, 0, 0),
    ]
    for a, b, expected in cases:
        result = evm_op.smod_semantics(_to_bv256(a), _to_bv256(b))
        assert is_true(simplify(result == _to_bv256(expected)))


def test_slt_sgt_semantics():
    """测试SLT/SGT跨符号比较。"""
    evm_op = EVMOperationSemantics()
    neg_one = _to_bv256(-1)
    pos_one = _to_bv256(1)
    assert is_true(simplify(evm_op.slt_semantics(neg_one, pos_one) == BitVecVal(1, 256)))
    assert is_true(simplify(evm_op.sgt_semantics(pos_one, neg_one) == BitVecVal(1, 256)))


def test_signextend_semantics():
    """测试SIGNEXTEND边界行为。"""
    evm_op = EVMOperationSemantics()

    # index=0：0x80 -> ...ff80
    result0 = evm_op.signextend_semantics(BitVecVal(0, 256), BitVecVal(0x80, 256))
    assert is_true(simplify(result0 == _to_bv256(-128)))

    # index=31：应保持不变
    v31 = _to_bv256(-1)
    result31 = evm_op.signextend_semantics(BitVecVal(31, 256), v31)
    assert is_true(simplify(result31 == v31))

    # index>=32：应保持不变
    v32 = BitVecVal(0x123456, 256)
    result32 = evm_op.signextend_semantics(BitVecVal(32, 256), v32)
    assert is_true(simplify(result32 == v32))


def test_byte_semantics():
    """测试BYTE取高位/低位/越界行为。"""
    evm_op = EVMOperationSemantics()
    value = int.from_bytes(bytes(range(1, 33)), byteorder="big")

    # index=0 -> 最高字节 0x01
    byte0 = evm_op.byte_semantics(BitVecVal(0, 256), BitVecVal(value, 256))
    assert is_true(simplify(byte0 == BitVecVal(1, 256)))

    # index=31 -> 最低字节 0x20
    byte31 = evm_op.byte_semantics(BitVecVal(31, 256), BitVecVal(value, 256))
    assert is_true(simplify(byte31 == BitVecVal(32, 256)))

    # index=32 -> 越界返回0
    byte32 = evm_op.byte_semantics(BitVecVal(32, 256), BitVecVal(value, 256))
    assert is_true(simplify(byte32 == BitVecVal(0, 256)))


def test_exp_semantics_folds_zero_and_one_exponents():
    evm_op = EVMOperationSemantics()
    symbolic_base = BitVec("exp_base", 256)

    exp_zero = evm_op.exp_semantics(symbolic_base, BitVecVal(0, 256))
    assert is_true(simplify(exp_zero == BitVecVal(1, 256)))

    exp_one = evm_op.exp_semantics(symbolic_base, BitVecVal(1, 256))
    assert is_true(simplify(exp_one == symbolic_base))


def test_addmod_mulmod_semantics():
    """测试ADDMOD/MULMOD（含大数场景与mod=0）。"""
    evm_op = EVMOperationSemantics()

    addmod_simple = evm_op.addmod_semantics(BitVecVal(5, 256), BitVecVal(7, 256), BitVecVal(10, 256))
    assert is_true(simplify(addmod_simple == BitVecVal(2, 256)))

    a = (1 << 256) - 1
    b = 2
    m = 17
    expected_addmod = (a + b) % m
    addmod_big = evm_op.addmod_semantics(BitVecVal(a, 256), BitVecVal(b, 256), BitVecVal(m, 256))
    assert is_true(simplify(addmod_big == BitVecVal(expected_addmod, 256)))

    mul_a = (1 << 255) + 1
    mul_b = 3
    mul_m = 19
    expected_mulmod = (mul_a * mul_b) % mul_m
    mulmod_big = evm_op.mulmod_semantics(BitVecVal(mul_a, 256), BitVecVal(mul_b, 256), BitVecVal(mul_m, 256))
    assert is_true(simplify(mulmod_big == BitVecVal(expected_mulmod, 256)))

    addmod_zero = evm_op.addmod_semantics(BitVecVal(1, 256), BitVecVal(2, 256), BitVecVal(0, 256))
    mulmod_zero = evm_op.mulmod_semantics(BitVecVal(1, 256), BitVecVal(2, 256), BitVecVal(0, 256))
    assert is_true(simplify(addmod_zero == BitVecVal(0, 256)))
    assert is_true(simplify(mulmod_zero == BitVecVal(0, 256)))


def test_shift_semantics():
    """测试SHL/SHR/SAR边界位移。"""
    evm_op = EVMOperationSemantics()

    # SHL
    shl_255 = evm_op.shl_semantics(BitVecVal(1, 256), BitVecVal(255, 256))
    assert is_true(simplify(shl_255 == BitVecVal(1 << 255, 256)))
    shl_256 = evm_op.shl_semantics(BitVecVal(1, 256), BitVecVal(256, 256))
    assert is_true(simplify(shl_256 == BitVecVal(0, 256)))

    # SHR
    shr_255 = evm_op.shr_semantics(BitVecVal(1 << 255, 256), BitVecVal(255, 256))
    assert is_true(simplify(shr_255 == BitVecVal(1, 256)))
    shr_256 = evm_op.shr_semantics(BitVecVal(1 << 255, 256), BitVecVal(256, 256))
    assert is_true(simplify(shr_256 == BitVecVal(0, 256)))

    # SAR
    sar_neg = evm_op.sar_semantics(_to_bv256(-2), BitVecVal(1, 256))
    assert is_true(simplify(sar_neg == _to_bv256(-1)))
    sar_neg_big_shift = evm_op.sar_semantics(_to_bv256(-2), BitVecVal(300, 256))
    assert is_true(simplify(sar_neg_big_shift == _to_bv256(-1)))
    sar_pos_big_shift = evm_op.sar_semantics(BitVecVal(2, 256), BitVecVal(300, 256))
    assert is_true(simplify(sar_pos_big_shift == BitVecVal(0, 256)))


def _make_state_with_stack(*values):
    """创建一个将values依次push到栈上的SMTState（最后一个值在栈顶）。"""
    state = SMTState()
    for v in values:
        state.evm_stack = state.evm_stack.push(BitVecVal(v, 256))
    return state


def test_sub_opcode_stack_order():
    """测试SUB从栈的弹出顺序：栈顶为被减数，次顶为减数。result = top - second"""
    op = EvmOperator(kind="SUB", pc=0)
    # 栈: [10(次顶), 3(栈顶)] -> 3 - 10 = ... 不对，应是 top - second = 3 - 10
    # EVM SUB: a=pop(栈顶)=3, b=pop(次顶)=10, result=a-b=3-10 -> underflow
    # 换: top=10, second=3 -> result=10-3=7
    state = _make_state_with_stack(3, 10)  # 3先push，10后push（10在栈顶）
    result_state = evm_operator_to_z3(op, state)
    top, _ = result_state.evm_stack.pop()
    assert is_true(simplify(top == BitVecVal(7, 256))), f"SUB: 10-3 should be 7, got {simplify(top)}"

    # 反向验证：top=3, second=10 -> 3-10 underflow = 2^256-7
    state2 = _make_state_with_stack(10, 3)
    result_state2 = evm_operator_to_z3(op, state2)
    top2, _ = result_state2.evm_stack.pop()
    expected2 = BitVecVal((1 << 256) - 7, 256)
    assert is_true(simplify(top2 == expected2)), f"SUB: 3-10 should wrap, got {simplify(top2)}"


def test_div_opcode_stack_order():
    """测试DIV从栈的弹出顺序：result = top / second"""
    op = EvmOperator(kind="DIV", pc=0)
    # top=10, second=3 -> 10/3=3
    state = _make_state_with_stack(3, 10)
    result_state = evm_operator_to_z3(op, state)
    top, _ = result_state.evm_stack.pop()
    assert is_true(simplify(top == BitVecVal(3, 256))), f"DIV: 10/3 should be 3, got {simplify(top)}"

    # top=3, second=10 -> 3/10=0
    state2 = _make_state_with_stack(10, 3)
    result_state2 = evm_operator_to_z3(op, state2)
    top2, _ = result_state2.evm_stack.pop()
    assert is_true(simplify(top2 == BitVecVal(0, 256))), f"DIV: 3/10 should be 0, got {simplify(top2)}"


def test_mod_opcode_stack_order():
    """测试MOD从栈的弹出顺序：result = top % second"""
    op = EvmOperator(kind="MOD", pc=0)
    # top=10, second=3 -> 10%3=1
    state = _make_state_with_stack(3, 10)
    result_state = evm_operator_to_z3(op, state)
    top, _ = result_state.evm_stack.pop()
    assert is_true(simplify(top == BitVecVal(1, 256))), f"MOD: 10%3 should be 1, got {simplify(top)}"

    # top=3, second=10 -> 3%10=3
    state2 = _make_state_with_stack(10, 3)
    result_state2 = evm_operator_to_z3(op, state2)
    top2, _ = result_state2.evm_stack.pop()
    assert is_true(simplify(top2 == BitVecVal(3, 256))), f"MOD: 3%10 should be 3, got {simplify(top2)}"


def test_addmod_opcode_stack_order():
    """测试ADDMOD从栈的弹出顺序：result = (top + second) % third"""
    op = EvmOperator(kind="ADDMOD", pc=0)
    # bottom-to-top: modulus=6, b=4, a=5 -> (5+4)%6 = 3
    state = _make_state_with_stack(6, 4, 5)
    result_state = evm_operator_to_z3(op, state)
    top, _ = result_state.evm_stack.pop()

    solver = Solver()
    solver.add(top != BitVecVal(3, 256))
    assert solver.check() == unsat, f"ADDMOD: (5+4)%6 should be 3, got {simplify(top)}"


def test_mulmod_opcode_stack_order():
    """测试MULMOD从栈的弹出顺序：result = (top * second) % third"""
    op = EvmOperator(kind="MULMOD", pc=0)
    # bottom-to-top: modulus=7, b=4, a=5 -> (5*4)%7 = 6
    state = _make_state_with_stack(7, 4, 5)
    result_state = evm_operator_to_z3(op, state)
    top, _ = result_state.evm_stack.pop()

    solver = Solver()
    solver.add(top != BitVecVal(6, 256))
    assert solver.check() == unsat, f"MULMOD: (5*4)%7 should be 6, got {simplify(top)}"


def test_lt_opcode_stack_order():
    """测试LT从栈的弹出顺序：result = (top < second) ? 1 : 0"""
    op = EvmOperator(kind="LT", pc=0)
    # top=3, second=10 -> 3 < 10 = 1
    state = _make_state_with_stack(10, 3)
    result_state = evm_operator_to_z3(op, state)
    top, _ = result_state.evm_stack.pop()
    assert is_true(simplify(top == BitVecVal(1, 256))), f"LT: 3<10 should be 1, got {simplify(top)}"

    # top=10, second=3 -> 10 < 3 = 0
    state2 = _make_state_with_stack(3, 10)
    result_state2 = evm_operator_to_z3(op, state2)
    top2, _ = result_state2.evm_stack.pop()
    assert is_true(simplify(top2 == BitVecVal(0, 256))), f"LT: 10<3 should be 0, got {simplify(top2)}"


def test_gt_opcode_stack_order():
    """测试GT从栈的弹出顺序：result = (top > second) ? 1 : 0"""
    op = EvmOperator(kind="GT", pc=0)
    # top=10, second=3 -> 10 > 3 = 1
    state = _make_state_with_stack(3, 10)
    result_state = evm_operator_to_z3(op, state)
    top, _ = result_state.evm_stack.pop()
    assert is_true(simplify(top == BitVecVal(1, 256))), f"GT: 10>3 should be 1, got {simplify(top)}"

    # top=3, second=10 -> 3 > 10 = 0
    state2 = _make_state_with_stack(10, 3)
    result_state2 = evm_operator_to_z3(op, state2)
    top2, _ = result_state2.evm_stack.pop()
    assert is_true(simplify(top2 == BitVecVal(0, 256))), f"GT: 3>10 should be 0, got {simplify(top2)}"


def test_mstore_mload_opcode():
    """测试MSTORE/MLOAD的栈顺序：MSTORE top=offset, second=value。"""
    from state.smt_state import EVMMemoryState
    mstore_op = EvmOperator(kind="MSTORE", pc=0)
    mload_op = EvmOperator(kind="MLOAD", pc=0)

    state = SMTState()
    state.evm_memory = EVMMemoryState(msize=BitVecVal(0, 64))
    # MSTORE: top=offset=32, second=value=0xDEADBEEF
    state.evm_stack = state.evm_stack.push(BitVecVal(0xDEADBEEF, 256))  # value（先push）
    state.evm_stack = state.evm_stack.push(BitVecVal(32, 256))           # offset（后push，栈顶）
    state = evm_operator_to_z3(mstore_op, state)

    # MLOAD: top=offset=32，应读回 0xDEADBEEF
    state.evm_stack = state.evm_stack.push(BitVecVal(32, 256))
    state = evm_operator_to_z3(mload_op, state)
    loaded, _ = state.evm_stack.pop()

    solver = Solver()
    solver.add(loaded == BitVecVal(0xDEADBEEF, 256))
    assert solver.check() == sat, "MSTORE/MLOAD round-trip failed"


def test_sstore_sload_opcode():
    """测试SSTORE/SLOAD的栈顺序：SSTORE top=key, second=value。"""
    sstore_op = EvmOperator(kind="SSTORE", pc=0)
    sload_op = EvmOperator(kind="SLOAD", pc=0)

    state = SMTState()
    # SSTORE: top=key=0xAA, second=value=0x1234
    state.evm_stack = state.evm_stack.push(BitVecVal(0x1234, 256))  # value（先push）
    state.evm_stack = state.evm_stack.push(BitVecVal(0xAA, 256))    # key（后push，栈顶）
    state = evm_operator_to_z3(sstore_op, state)

    # SLOAD: top=key=0xAA，应读回 0x1234
    state.evm_stack = state.evm_stack.push(BitVecVal(0xAA, 256))
    state = evm_operator_to_z3(sload_op, state)
    loaded, _ = state.evm_stack.pop()

    solver = Solver()
    solver.add(loaded == BitVecVal(0x1234, 256))
    assert solver.check() == sat, "SSTORE/SLOAD round-trip failed"


def test_return_opcode_stack_order():
    """测试RETURN的栈顺序：top=offset, second=length。"""
    from state.smt_state import EVMMemoryState
    return_op = EvmOperator(kind="RETURN", pc=0)

    state = SMTState()
    state.evm_memory = EVMMemoryState(msize=BitVecVal(0, 64))
    # RETURN: top=offset=64, second=length=32
    state.evm_stack = state.evm_stack.push(BitVecVal(32, 256))   # length（先push）
    state.evm_stack = state.evm_stack.push(BitVecVal(64, 256))   # offset（后push，栈顶）
    state = evm_operator_to_z3(return_op, state)

    solver = Solver()
    solver.add(state.return_offset == BitVecVal(64, 64))
    solver.add(state.return_length == BitVecVal(32, 64))
    assert solver.check() == sat, "RETURN: offset/length stack order wrong"


def test_revert_opcode_stack_order():
    """测试REVERT的栈顺序：top=offset, second=length。"""
    revert_op = EvmOperator(kind="REVERT", pc=0)

    state = SMTState()
    state.evm_stack = state.evm_stack.push(BitVecVal(32, 256))   # length（先push）
    state.evm_stack = state.evm_stack.push(BitVecVal(64, 256))   # offset（后push，栈顶）
    state = evm_operator_to_z3(revert_op, state)

    solver = Solver()
    solver.add(state.return_offset == BitVecVal(64, 64))
    solver.add(state.return_length == BitVecVal(32, 64))
    assert solver.check() == sat, "REVERT: offset/length stack order wrong"


def test_revert_sets_reverted_status():
    """REVERT 的权威结果是 error_code，不是字符串。"""
    op = EvmOperator(kind="REVERT", pc=0)
    state = SMTState()
    state.evm_stack = state.evm_stack.push(BitVecVal(32, 256))
    state.evm_stack = state.evm_stack.push(BitVecVal(64, 256))
    state = evm_operator_to_z3(op, state)

    assert is_true(simplify(state.error_code == BitVecVal(EvmStatusCode.REVERTED, 8)))


def test_invalid_sets_invalid_status():
    """INVALID 的权威结果是 error_code，不是字符串。"""
    op = EvmOperator(kind="INVALID", pc=0)
    state = SMTState()
    state = evm_operator_to_z3(op, state)

    assert is_true(simplify(state.error_code == BitVecVal(EvmStatusCode.INVALID, 8)))


def test_set_terminal_status_projects_string_from_code():
    """error_string 是 error_code 的投影。

    这是唯一该断言字符串的地方：验证投影关系本身没有失效。
    """
    for code in (
        EvmStatusCode.RETURNED,
        EvmStatusCode.REVERTED,
        EvmStatusCode.STOPPED,
        EvmStatusCode.INVALID,
        EvmStatusCode.INVALID_JUMP,
        EvmStatusCode.RETURN_DATA_OUT_OF_BOUNDS,
        EvmStatusCode.STACK_UNDERFLOW,
    ):
        state = SMTState()
        set_terminal_status(state, code)
        assert is_true(simplify(state.error_code == BitVecVal(code, 8)))
        assert state.error_string == get_status_message(code)

    # STOP 曾经写成 RETURNED 的字面量 "stop token"，守住它不再回来。
    stopped = SMTState()
    set_terminal_status(stopped, EvmStatusCode.STOPPED)
    assert stopped.error_string == "execution stopped"


def _returndatacopy_state(data_offset, length, return_data_size: int) -> SMTState:
    """按 EVM 栈序压入 RETURNDATACOPY 的三个参数并执行。

    gas 给具体大常量：本组测试的主题是 ReturnDataOutOfBounds 那三条分支，而 IR 侧
    的 gas 状态语义是无条件建模的，符号 gas 会额外挂一条 dynamicCost > gas 的
    OUT_OF_GAS 分支、干扰 `_sole_error_branch` 的计数。gas 充足时它静态判死。
    """
    from state.evm_gas_state import EVMGasState

    state = SMTState()
    state.evm_gas = EVMGasState(initial_gas=BitVecVal(100_000, 64))
    state.callengine_return_data_size_bytes = BitVecVal(return_data_size, 64)
    for value in (length, data_offset, 0):   # length, returnDataOffset, memOffset
        state.evm_stack = state.evm_stack.push(
            value if is_bv(value) else BitVecVal(value, 256)
        )
    return evm_operator_to_z3(EvmOperator(kind="RETURNDATACOPY", pc=0), state)


def _sole_error_branch(state: SMTState):
    assert len(state.pending_errors) == 1, (
        f"expected exactly one pending error branch, got {len(state.pending_errors)}"
    )
    return state.pending_errors[0]


# RETURNDATACOPY 的三条错误分支镜像 compileEVMRETURNDATACOPY
# (impl_amd64.go:3143-3178)，都发射 evmNativeCallStatusCodeReturnDataOutOfBounds。

def test_returndatacopy_size_too_small_is_out_of_bounds():
    """returnDataSize < dataOffset + length —— CMPQ/JCS 那一支。"""
    state = _returndatacopy_state(10, 4, 8)
    branch = _sole_error_branch(state)
    assert branch.status_code == EvmStatusCode.RETURN_DATA_OUT_OF_BOUNDS
    assert is_true(simplify(branch.condition)), "具体越界输入应当化简成恒真"


def test_returndatacopy_in_bounds_has_no_error_branch():
    """安全输入不应产生错误分支。"""
    state = _returndatacopy_state(1, 4, 8)
    assert state.pending_errors == []


def test_returndatacopy_data_offset_above_uint64_is_out_of_bounds():
    """dataOffset 高 192 位非零 —— compileLocIsUint64 那一支。

    注意 x86 只检查 dataOffset 是否 uint64，不检查 length（codegen 只加载 l1）。
    """
    state = _returndatacopy_state(BitVecVal(1 << 64, 256), 0, 8)
    assert is_true(simplify(_sole_error_branch(state).condition))


def test_returndatacopy_64bit_carry_is_out_of_bounds():
    """dataOffset.z0 + length.z0 的 64 位进位 —— ADDQ+ADCQ+TESTQ/JNE 那一支。"""
    state = _returndatacopy_state(BitVecVal((1 << 64) - 1, 256), 2, 8)
    assert is_true(simplify(_sole_error_branch(state).condition))


def test_returndatacopy_symbolic_offset_splits_paths():
    """符号 dataOffset 必须分裂出可满足的越界路径。

    旧实现只在三个操作数都具体时才判越界，符号 offset 直接走正常 copy。
    """
    data_offset = BitVec("rdc_data_offset", 256)
    state = _returndatacopy_state(data_offset, 4, 8)
    condition = _sole_error_branch(state).condition

    oob = Solver()
    oob.add(condition, data_offset == BitVecVal(10, 256))
    assert oob.check() == sat, "dataOffset=10, length=4, size=8 必须判越界"

    safe = Solver()
    safe.add(condition, data_offset == BitVecVal(1, 256))
    assert safe.check() == unsat, "dataOffset=1, length=4, size=8 不应判越界"


def test_returndatacopy_error_snapshot_is_taken_before_memory_write():
    """错误终态必须是"已弹栈、未写内存"的快照，对齐 x86 的 exit-before-copy。

    取 post-state 会让错误路径带上本不该发生的内存写入，与 x86 侧不一致。
    """
    data_offset = BitVec("rdc_snapshot_offset", 256)
    state = _returndatacopy_state(data_offset, 4, 8)
    snapshot = _sole_error_branch(state).terminal_state

    # 未写内存：快照的 memory 与全 0 初值一致。
    probe = BitVec("probe_addr", 64)
    solver = Solver()
    solver.add(Select(snapshot.evm_memory.Memory, probe) != BitVecVal(0, 8))
    assert solver.check() == unsat, "错误快照不应包含任何内存写入"

    # 已弹栈：三个操作数都已弹出，SP 回到初始值。
    assert is_true(simplify(snapshot.evm_stack.SP == state.evm_stack.SP))


def test_sstore_never_produces_native_write_protection_status():
    """AOT 的 SSTORE 不产生 native status 6。

    写保护在 Go host 函数里以 error 返回（engine_evm.go:652），codegen 从不
    发射 WRITE_PROTECTION；守住照解释器抄的 read_only 分支不再回来。
    """
    op = EvmOperator(kind="SSTORE", pc=0)
    state = SMTState()
    state.evm_stack = state.evm_stack.push(BitVecVal(0x1234, 256))
    state.evm_stack = state.evm_stack.push(BitVecVal(0xAA, 256))
    state = evm_operator_to_z3(op, state)

    assert state.pending_errors == []
    assert is_true(simplify(state.error_code == BitVecVal(EvmStatusCode.RETURNED, 8)))


def test_jump_sets_invalid_jump_error_when_destination_is_not_jumpdest():
    """目标不在合法集合内时产生一条恒真的 INVALID_JUMP 错误分支。"""
    op = EvmOperator(kind="JUMP", pc=0)
    state = SMTState()
    state.valid_jump_targets = {6}
    state.evm_stack = state.evm_stack.push(BitVecVal(1, 256))
    state = evm_operator_to_z3(op, state)

    branch = _sole_error_branch(state)
    assert branch.status_code == EvmStatusCode.INVALID_JUMP
    assert is_true(simplify(branch.condition)), "dest=1 不在 {6} 内，错误条件应恒真"


def test_jump_to_valid_target_leaves_error_code_untouched():
    """目标在合法集合内时不应产生 INVALID_JUMP。"""
    op = EvmOperator(kind="JUMP", pc=0)
    state = SMTState()
    state.valid_jump_targets = {6}
    state.evm_stack = state.evm_stack.push(BitVecVal(6, 256))
    state = evm_operator_to_z3(op, state)

    assert state.pending_errors == []
    assert is_true(simplify(state.error_code == BitVecVal(EvmStatusCode.RETURNED, 8)))


def test_jump_without_target_set_stays_silent():
    """未预填充合法目标集合时保持沉默，避免用部分集合产生假反例。"""
    op = EvmOperator(kind="JUMP", pc=0)
    state = SMTState()
    state.evm_stack = state.evm_stack.push(BitVecVal(1, 256))
    state = evm_operator_to_z3(op, state)

    assert state.pending_errors == []


def test_jump_with_empty_jumpdest_set_is_always_invalid():
    """一个 JUMPDEST 都没有时任何跳转都非法。

    对齐 codegen：c.jumpTable 为空 ⇒ 比较链为空 ⇒ 直接 exit(InvalidJump)。
    """
    op = EvmOperator(kind="JUMP", pc=0)
    state = SMTState()
    state.valid_jump_targets = set()
    state.evm_stack = state.evm_stack.push(BitVec("any_dest", 256))
    state = evm_operator_to_z3(op, state)

    branch = _sole_error_branch(state)
    assert branch.status_code == EvmStatusCode.INVALID_JUMP
    assert is_true(simplify(branch.condition)), "无 JUMPDEST 时错误条件应恒真"


def test_jump_with_immediate_set_uses_candidate_targets():
    """多目标跳转按 immediate_set 判定：符号 dest 得到符号化的错误条件。"""
    op = EvmOperator(kind="JUMP", pc=0, immediate_set=[6, 20])
    state = SMTState()
    dest = BitVec("dest", 256)
    state.evm_stack = state.evm_stack.push(dest)
    state = evm_operator_to_z3(op, state)

    condition = _sole_error_branch(state).condition

    solver = Solver()
    solver.add(dest == BitVecVal(20, 256), condition)
    assert solver.check() == unsat, "dest 命中 immediate_set 时不应报 INVALID_JUMP"

    solver = Solver()
    solver.add(dest == BitVecVal(7, 256), Not(condition))
    assert solver.check() == unsat, "dest 未命中 immediate_set 时应报 INVALID_JUMP"


def test_jumpi_not_taken_does_not_report_invalid_jump():
    """JUMPI 未跳转的路径上不施加目标校验（codegen 直接 fallthrough）。"""
    op = EvmOperator(kind="JUMPI", pc=0, immediate_set=[6])
    state = SMTState()
    cond = BitVec("cond", 256)
    # 压栈顺序：先 dest 后 cond，使 cond 位于栈顶（JUMPI 先 pop cond）。
    state.evm_stack = state.evm_stack.push(BitVecVal(99, 256))
    state.evm_stack = state.evm_stack.push(cond)
    state = evm_operator_to_z3(op, state)

    condition = _sole_error_branch(state).condition

    solver = Solver()
    solver.add(cond == BitVecVal(0, 256), condition)
    assert solver.check() == unsat, "cond=0 未跳转，不应报 INVALID_JUMP"

    solver = Solver()
    solver.add(cond == BitVecVal(1, 256), Not(condition))
    assert solver.check() == unsat, "cond!=0 且 dest=99 不在集合内，应报 INVALID_JUMP"


def _make_x86_ret_state(status_code: int, stack_values, sp: int = 0,
                        r13_base: int = 0x10000, r14_base: int = 0x20000) -> SMTState:
    """创建一个用于测试 x86 RET 的状态。

    stack_values 按压栈顺序给出，最后一个元素是逻辑栈顶。
    """
    state = SMTState()
    state.x86_registers.set_register(Register.R13, BitVecVal(r13_base, 64))
    state.x86_registers.set_register(Register.R14, BitVecVal(r14_base, 64))

    status_addr = r13_base + AOT_COMPILER_PROFILE.offsets["status_code"]
    sp_addr = r13_base + AOT_COMPILER_PROFILE.offsets["stack_pointer"]
    state.x86_memory = state.x86_memory.store_byte(
        BitVecVal(status_addr, 64), BitVecVal(status_code, 8), domain=MemoryDomain.CALLENGINE,
    )
    state.x86_memory = state.x86_memory.store_64bit(
        BitVecVal(sp_addr, 64), BitVecVal(sp % (1 << 64), 64), domain=MemoryDomain.CALLENGINE,
    )
    # 同步 callEngine side-channel —— 生产 ret/_extract_stack_pointer 直接读 BitVec 字段
    state.callengine_status_code = BitVecVal(status_code, 8)
    state.callengine_stack_pointer_limbs = BitVecVal(sp % (1 << 64), 64)

    stack_depth = len(stack_values)
    for push_index, value in enumerate(stack_values):
        stack_index = stack_depth - 1 - push_index
        addr = r14_base - (stack_index + 1) * 0x20
        state.x86_memory = state.x86_memory.store_256bit(
            BitVecVal(addr, 64), BitVecVal(value, 256), domain=MemoryDomain.STACK,
        )

    return state


def test_x86_ret_reverted_extracts_return_data():
    """x86 RET 在 REVERTED 状态下也应提取 offset/length。"""
    ret_insn = X86Instruction(addr=0, mnemonic="ret", op_str="", bytes=b"\xc3", size=1)
    state = _make_x86_ret_state(
        AOT_COMPILER_PROFILE.status_codes["reverted"],
        [32, 64],
    )

    state = ret_insn.to_z3(state)

    solver = Solver()
    solver.add(state.return_offset == BitVecVal(64, 64))
    solver.add(state.return_length == BitVecVal(32, 64))
    assert solver.check() == sat, "x86 RET(REVERTED) should expose revert data"


def test_x86_ret_invalid_has_no_return_data():
    """x86 RET 在 INVALID 状态下不应设置返回数据。"""
    ret_insn = X86Instruction(addr=0, mnemonic="ret", op_str="", bytes=b"\xc3", size=1)
    state = _make_x86_ret_state(
        AOT_COMPILER_PROFILE.status_codes["invalid"],
        [0xFE],
    )

    state = ret_insn.to_z3(state)

    solver = Solver()
    solver.add(state.return_offset == BitVecVal(0, 64))
    solver.add(state.return_length == BitVecVal(0, 64))
    assert solver.check() == sat, "x86 RET(INVALID) should not expose return data"


def test_msize_returns_word_rounded_length():
    """MSTORE8(0) 将 mem.Len() 扩展到 32，后续 MSIZE 必须返回 32。"""
    from evm_ir.models import EVMBlock

    block = EVMBlock(pc=0, stack_depth=0, min_depth=0, max_depth=1024,
                     static_gas=0, is_jump_target=False,
                     is_inner_block=False, is_stop=False)
    state = SMTState.create_initial_state()

    # MSTORE8(offset=0, value=0xab)：requested=1 → 1 word → mem.Len()=32
    state.evm_stack = state.evm_stack.push(BitVecVal(0xab, 256))
    state.evm_stack = state.evm_stack.push(BitVecVal(0, 256))
    state = evm_operator_to_z3(EvmOperator(kind="MSTORE8", pc=0, block=block), state)
    state.pending_errors = []
    state.pending_constraints = []

    assert simplify(state.evm_memory.MSize).eq(BitVecVal(32, 64)), (
        "MSTORE8(0) 后 mem.Len() 应为 32（1 word），不是字节数 1"
    )

    state = evm_operator_to_z3(EvmOperator(kind="MSIZE", pc=1, block=block), state)
    pushed, _ = state.evm_stack.pop()
    assert simplify(pushed).eq(BitVecVal(32, 256)), (
        "MSIZE 必须压 32；压 1 说明按字节记高水位的旧模型被改回来了"
    )


def test_zero_length_mcopy_does_not_grow_msize():
    """MCOPY(dst=64, length=0) 不扩展内存，后续 MSIZE 必须返回 0。"""
    from evm_ir.models import EVMBlock

    block = EVMBlock(pc=0, stack_depth=0, min_depth=0, max_depth=1024,
                     static_gas=0, is_jump_target=False,
                     is_inner_block=False, is_stop=False)
    state = SMTState.create_initial_state()

    # 栈：length, srcOffset, memOffset(栈顶)
    for value in (0, 0, 64):
        state.evm_stack = state.evm_stack.push(BitVecVal(value, 256))
    state = evm_operator_to_z3(EvmOperator(kind="MCOPY", pc=0, block=block), state)
    state.pending_errors = []
    state.pending_constraints = []

    assert simplify(state.evm_memory.MSize).eq(BitVecVal(0, 64)), (
        "MCOPY(dst=64, len=0) 不得扩内存；MSize=64 说明 charge_dynamic_gas 之外又有人写它"
    )

    state = evm_operator_to_z3(EvmOperator(kind="MSIZE", pc=1, block=block), state)
    pushed, _ = state.evm_stack.pop()
    assert simplify(pushed).eq(BitVecVal(0, 256)), "MSIZE 必须压 0"


def test_mstore8_opcode():
    """测试MSTORE8写低8位 + 256位offset截断。"""
    op = EvmOperator(kind="MSTORE8", pc=0)

    # case1: 常规写入
    state = SMTState()
    state.evm_memory = EVMMemoryState(msize=BitVecVal(0, 64))
    state.evm_stack = state.evm_stack.push(BitVecVal(0x1234, 256))  # value
    state.evm_stack = state.evm_stack.push(BitVecVal(5, 256))       # offset (栈顶)
    result_state = evm_operator_to_z3(op, state)

    solver = Solver()
    solver.add(result_state.evm_memory.get_byte(BitVecVal(5, 64)) == BitVecVal(0x34, 8))
    # MSize = mem.Len()，按 32 字节字取整：requested=6 → 1 word → 32
    solver.add(result_state.evm_memory.MSize == BitVecVal(32, 64))
    assert solver.check() == sat

    # case2: 256位offset截断到64位
    state2 = SMTState()
    state2.evm_memory = EVMMemoryState(msize=BitVecVal(0, 64))
    state2.evm_stack = state2.evm_stack.push(BitVecVal(0xABCD, 256))          # value
    state2.evm_stack = state2.evm_stack.push(BitVecVal((1 << 64) + 3, 256))   # offset
    result_state2 = evm_operator_to_z3(op, state2)

    solver2 = Solver()
    solver2.add(result_state2.evm_memory.get_byte(BitVecVal(3, 64)) == BitVecVal(0xCD, 8))
    # requested=4 → 1 word → 32
    solver2.add(result_state2.evm_memory.MSize == BitVecVal(32, 64))
    assert solver2.check() == sat


def test_calldatacopy_zero_padding_and_stack_order():
    """测试 CALLDATACOPY 的弹栈顺序和越界零填充。"""
    op = EvmOperator(kind="CALLDATACOPY", pc=0)

    state = SMTState()
    state.evm_memory = EVMMemoryState(msize=BitVecVal(0, 64))
    state.calldatasize = BitVecVal(1, 64)
    state.calldata = Store(state.calldata, BitVecVal(0, 64), BitVecVal(0xAA, 8))

    # Go / EVM 语义：top=memOffset, second=dataOffset, third=length
    state.evm_stack = state.evm_stack.push(BitVecVal(2, 256))   # length
    state.evm_stack = state.evm_stack.push(BitVecVal(0, 256))   # dataOffset
    state.evm_stack = state.evm_stack.push(BitVecVal(10, 256))  # memOffset (栈顶)

    result_state = evm_operator_to_z3(op, state)

    solver = Solver()
    solver.add(Select(result_state.evm_memory.Memory, BitVecVal(10, 64)) == BitVecVal(0xAA, 8))
    solver.add(Select(result_state.evm_memory.Memory, BitVecVal(11, 64)) == BitVecVal(0, 8))
    # requested=10+2=12 → 1 word → 32
    solver.add(result_state.evm_memory.MSize == BitVecVal(32, 64))
    assert solver.check() == sat


def test_calldataload_zero_padding():
    """测试 CALLDATALOAD 会对超出 calldata 的部分补 0。"""
    op = EvmOperator(kind="CALLDATALOAD", pc=0)

    state = SMTState()
    state.calldatasize = BitVecVal(2, 64)
    state.calldata = Store(state.calldata, BitVecVal(0, 64), BitVecVal(0xAA, 8))
    state.calldata = Store(state.calldata, BitVecVal(1, 64), BitVecVal(0xBB, 8))
    state.evm_stack = state.evm_stack.push(BitVecVal(0, 256))

    result_state = evm_operator_to_z3(op, state)
    loaded, _ = result_state.evm_stack.pop()

    expected = (0xAA << 248) | (0xBB << 240)
    solver = Solver()
    solver.add(loaded == BitVecVal(expected, 256))
    assert solver.check() == sat


def test_calldatasize_zero_extends_context_size():
    """测试 CALLDATASIZE 对齐 Go 的 uint256.SetUint64(len(input))。"""
    op = EvmOperator(kind="CALLDATASIZE", pc=0)

    state = SMTState()
    state.calldatasize = BitVecVal(5, 64)

    result_state = evm_operator_to_z3(op, state)
    loaded, _ = result_state.evm_stack.pop()

    solver = Solver()
    solver.add(loaded != BitVecVal(5, 256))
    assert solver.check() == unsat


def test_calldataload_offset_overflow_returns_zero():
    """测试 CALLDATALOAD 的 offset 超过 uint64 时返回 0。

    默认的 ``assume_calldata_offset_no_overflow=True`` 会 drop overflow
    分支（程序级 perf 优化），这个单测显式关闭该 hint，保留完整建模。
    """
    op = EvmOperator(kind="CALLDATALOAD", pc=1)

    state = SMTState()
    state.assume_calldata_offset_no_overflow = False
    state.calldatasize = BitVecVal(32, 64)
    state.calldata = Store(state.calldata, BitVecVal(0, 64), BitVecVal(0xAA, 8))
    state.evm_stack = state.evm_stack.push(BitVecVal((1 << 64), 256))

    result_state = evm_operator_to_z3(op, state)
    loaded, _ = result_state.evm_stack.pop()

    solver = Solver()
    solver.add(loaded == BitVecVal(0, 256))
    assert solver.check() == sat


def test_calldataload_max_uint64_offset_uses_go_getdata_clamp():
    """测试 uint64 内的大 offset 会按 Go getData clamp 到末尾而不是回绕读取。"""
    op = EvmOperator(kind="CALLDATALOAD", pc=2)

    state = SMTState()
    state.calldatasize = BitVecVal(1, 64)
    state.calldata = Store(state.calldata, BitVecVal(0, 64), BitVecVal(0xAA, 8))
    state.evm_stack = state.evm_stack.push(BitVecVal((1 << 64) - 1, 256))

    result_state = evm_operator_to_z3(op, state)
    loaded, _ = result_state.evm_stack.pop()

    solver = Solver()
    solver.add(loaded != BitVecVal(0, 256))
    assert solver.check() == unsat


def test_calldataload_near_max_uint64_offset_does_not_wrap_to_calldata_start():
    """测试 offset+31 回绕时仍不会误读 calldata 低地址。"""
    op = EvmOperator(kind="CALLDATALOAD", pc=3)

    state = SMTState()
    state.calldatasize = BitVecVal(1, 64)
    state.calldata = Store(state.calldata, BitVecVal(0, 64), BitVecVal(0xAA, 8))
    state.evm_stack = state.evm_stack.push(BitVecVal((1 << 64) - 31, 256))

    result_state = evm_operator_to_z3(op, state)
    loaded, _ = result_state.evm_stack.pop()

    solver = Solver()
    solver.add(loaded != BitVecVal(0, 256))
    assert solver.check() == unsat


def test_calldatacopy_symbolic_length_writes_memory():
    """测试 CALLDATACOPY 在符号长度下不会错误地保持内存不变。"""
    op = EvmOperator(kind="CALLDATACOPY", pc=1)

    state = SMTState()
    state.calldatasize = BitVecVal(1, 64)
    state.calldata = Store(state.calldata, BitVecVal(0, 64), BitVecVal(0xAB, 8))

    symbolic_length = BitVec("calldatacopy_len", 256)
    old_mem = Select(state.evm_memory.Memory, BitVecVal(5, 64))

    state.evm_stack = state.evm_stack.push(symbolic_length)     # length
    state.evm_stack = state.evm_stack.push(BitVecVal(0, 256))   # dataOffset
    state.evm_stack = state.evm_stack.push(BitVecVal(5, 256))   # memOffset
    result_state = evm_operator_to_z3(op, state)

    solver = Solver()
    solver.add(symbolic_length == BitVecVal(1, 256))
    solver.add(old_mem != BitVecVal(0xAB, 8))
    solver.add(Select(result_state.evm_memory.Memory, BitVecVal(5, 64)) == old_mem)
    assert solver.check() == unsat


def test_calldatacopy_overflow_offset_uses_go_getdata_clamp():
    """测试 CALLDATACOPY dataOffset 溢出钳到 MaxUint64 后不会回绕读取。"""
    op = EvmOperator(kind="CALLDATACOPY", pc=4)

    state = SMTState()
    state.calldatasize = BitVecVal(1, 64)
    state.calldata = Store(state.calldata, BitVecVal(0, 64), BitVecVal(0xAA, 8))
    state.evm_memory = state.evm_memory.set_byte(BitVecVal(10, 64), BitVecVal(0x11, 8))
    state.evm_memory = state.evm_memory.set_byte(BitVecVal(11, 64), BitVecVal(0x22, 8))

    state.evm_stack = state.evm_stack.push(BitVecVal(2, 256))       # length
    state.evm_stack = state.evm_stack.push(BitVecVal(1 << 64, 256)) # dataOffset -> MaxUint64
    state.evm_stack = state.evm_stack.push(BitVecVal(10, 256))      # memOffset
    result_state = evm_operator_to_z3(op, state)

    for addr in (10, 11):
        solver = Solver()
        solver.add(Select(result_state.evm_memory.Memory, BitVecVal(addr, 64)) != BitVecVal(0, 8))
        assert solver.check() == unsat


def test_calldatacopy_zero_length_does_not_grow_memory():
    """测试 CALLDATACOPY length=0 时不写内存也不增长 MSize。"""
    op = EvmOperator(kind="CALLDATACOPY", pc=5)

    state = SMTState()
    state.evm_memory = EVMMemoryState(msize=BitVecVal(3, 64))
    state.calldatasize = BitVecVal(1, 64)
    state.calldata = Store(state.calldata, BitVecVal(0, 64), BitVecVal(0xAA, 8))
    old_dest = Select(state.evm_memory.Memory, BitVecVal(10, 64))

    state.evm_stack = state.evm_stack.push(BitVecVal(0, 256))   # length
    state.evm_stack = state.evm_stack.push(BitVecVal(0, 256))   # dataOffset
    state.evm_stack = state.evm_stack.push(BitVecVal(10, 256))  # memOffset
    result_state = evm_operator_to_z3(op, state)

    solver_mem = Solver()
    solver_mem.add(Select(result_state.evm_memory.Memory, BitVecVal(10, 64)) != old_dest)
    assert solver_mem.check() == unsat

    solver_msize = Solver()
    solver_msize.add(result_state.evm_memory.MSize != BitVecVal(3, 64))
    assert solver_msize.check() == unsat


def test_codecopy_max_uint64_offset_uses_go_getdata_clamp():
    """测试 CODECOPY codeOffset 接近 uint64 上界时不会回绕读取 code[0]。"""
    op = EvmOperator(kind="CODECOPY", pc=6)

    state = SMTState()
    state.callengine_code_size_bytes = BitVecVal(1, 64)
    state.code = Store(state.code, BitVecVal(0, 64), BitVecVal(0xAA, 8))
    state.evm_memory = state.evm_memory.set_byte(BitVecVal(10, 64), BitVecVal(0x11, 8))
    state.evm_memory = state.evm_memory.set_byte(BitVecVal(11, 64), BitVecVal(0x22, 8))

    state.evm_stack = state.evm_stack.push(BitVecVal(2, 256))              # length
    state.evm_stack = state.evm_stack.push(BitVecVal((1 << 64) - 1, 256))  # codeOffset
    state.evm_stack = state.evm_stack.push(BitVecVal(10, 256))             # memOffset
    result_state = evm_operator_to_z3(op, state)

    for addr in (10, 11):
        solver = Solver()
        solver.add(Select(result_state.evm_memory.Memory, BitVecVal(addr, 64)) != BitVecVal(0, 8))
        assert solver.check() == unsat


def test_extcodecopy_symbolically_writes_memory():
    """测试 EXTCODECOPY 会符号化写入目标内存区间。"""
    op = EvmOperator(kind="EXTCODECOPY", pc=7)

    state = SMTState()
    state.evm_memory = EVMMemoryState(msize=BitVecVal(0, 64))
    old_inside = Select(state.evm_memory.Memory, BitVecVal(0x20, 64))
    old_outside = Select(state.evm_memory.Memory, BitVecVal(0x1F, 64))

    # top=addr, then destOffset, offset, size
    state.evm_stack = state.evm_stack.push(BitVecVal(2, 256))        # size
    state.evm_stack = state.evm_stack.push(BitVecVal(0x10, 256))     # offset
    state.evm_stack = state.evm_stack.push(BitVecVal(0x20, 256))     # destOffset
    state.evm_stack = state.evm_stack.push(BitVecVal(0x1234, 256))   # addr

    result_state = evm_operator_to_z3(op, state)

    solver_inside_can_change = Solver()
    solver_inside_can_change.add(
        Select(result_state.evm_memory.Memory, BitVecVal(0x20, 64)) != old_inside
    )
    assert solver_inside_can_change.check() == sat

    solver_outside = Solver()
    solver_outside.add(
        Select(result_state.evm_memory.Memory, BitVecVal(0x1F, 64)) != old_outside
    )
    assert solver_outside.check() == unsat

    solver_msize = Solver()
    # requested=0x20+2=0x22 → 2 words → 0x40
    solver_msize.add(result_state.evm_memory.MSize == BitVecVal(0x40, 64))
    assert solver_msize.check() == sat


def test_extcodecopy_zero_size_leaves_memory_unchanged():
    """测试 EXTCODECOPY 在 size=0 时不修改内存或 MSize。"""
    op = EvmOperator(kind="EXTCODECOPY", pc=8)

    state = SMTState()
    state.evm_memory = EVMMemoryState(msize=BitVecVal(0x33, 64))
    old_inside = Select(state.evm_memory.Memory, BitVecVal(0x20, 64))

    state.evm_stack = state.evm_stack.push(BitVecVal(0, 256))        # size
    state.evm_stack = state.evm_stack.push(BitVecVal(0x10, 256))     # offset
    state.evm_stack = state.evm_stack.push(BitVecVal(0x20, 256))     # destOffset
    state.evm_stack = state.evm_stack.push(BitVecVal(0x1234, 256))   # addr

    result_state = evm_operator_to_z3(op, state)

    solver_mem = Solver()
    solver_mem.add(
        Select(result_state.evm_memory.Memory, BitVecVal(0x20, 64)) != old_inside
    )
    assert solver_mem.check() == unsat

    solver_msize = Solver()
    solver_msize.add(result_state.evm_memory.MSize != BitVecVal(0x33, 64))
    assert solver_msize.check() == unsat


def test_extcodecopy_same_args_different_pc_are_independent():
    """不同 pc 的 EXTCODECOPY 应该生成不同的结构化 UF。"""
    state1 = SMTState()
    state2 = SMTState()

    for state in (state1, state2):
        state.evm_stack = state.evm_stack.push(BitVecVal(2, 256))
        state.evm_stack = state.evm_stack.push(BitVecVal(0x10, 256))
        state.evm_stack = state.evm_stack.push(BitVecVal(0x20, 256))
        state.evm_stack = state.evm_stack.push(BitVecVal(0x1234, 256))

    result_state1 = evm_operator_to_z3(EvmOperator(kind="EXTCODECOPY", pc=7), state1)
    result_state2 = evm_operator_to_z3(EvmOperator(kind="EXTCODECOPY", pc=9), state2)

    solver = Solver()
    solver.add(
        Select(result_state1.evm_memory.Memory, BitVecVal(0x20, 64)) !=
        Select(result_state2.evm_memory.Memory, BitVecVal(0x20, 64))
    )
    assert solver.check() == sat


def test_staticcall_result_is_constrained_boolean_and_writes_return_data():
    """测试 STATICCALL 返回值被约束为 {0, 1}，并符号写回返回数据。 

    Go runtime 的 CALL 系列函数只 push 0（失败）或 1（成功）。
    UF 原始结果通过 If(raw == 0, 0, 1) 映射到 {0, 1}。
    """
    op = EvmOperator(kind="STATICCALL", pc=2)

    state = SMTState()
    old_inside = Select(state.evm_memory.Memory, BitVecVal(20, 64))
    old_outside = Select(state.evm_memory.Memory, BitVecVal(19, 64))

    # top=gas, then addr, inOffset, inSize, retOffset, retSize
    state.evm_stack = state.evm_stack.push(BitVecVal(2, 256))       # retSize
    state.evm_stack = state.evm_stack.push(BitVecVal(20, 256))      # retOffset
    state.evm_stack = state.evm_stack.push(BitVecVal(4, 256))       # inSize
    state.evm_stack = state.evm_stack.push(BitVecVal(0, 256))       # inOffset
    state.evm_stack = state.evm_stack.push(BitVecVal(0x1234, 256))  # addr
    state.evm_stack = state.evm_stack.push(BitVecVal(1000, 256))    # gas

    result_state = evm_operator_to_z3(op, state)
    success, _ = result_state.evm_stack.pop()

    # success 是 256-bit 值，被约束为 {0, 1}
    assert success.size() == 256

    # 验证 success 只能取 0 或 1（不能取 2 或其他值）
    solver_check = Solver()
    solver_check.add(success != BitVecVal(0, 256))
    solver_check.add(success != BitVecVal(1, 256))
    assert solver_check.check() == unsat, "STATICCALL result should be constrained to {0, 1}"

    solver_inside = Solver()
    solver_inside.add(Select(result_state.evm_memory.Memory, BitVecVal(20, 64)) == old_inside)
    assert solver_inside.check() == sat

    solver_inside_can_change = Solver()
    solver_inside_can_change.add(Select(result_state.evm_memory.Memory, BitVecVal(20, 64)) != old_inside)
    assert solver_inside_can_change.check() == sat

    solver_outside = Solver()
    solver_outside.add(Select(result_state.evm_memory.Memory, BitVecVal(19, 64)) != old_outside)
    assert solver_outside.check() == unsat


def test_staticcall_same_args_different_pc_are_independent():
    """不同 pc 的 STATICCALL 应该生成不同的结构化 UF。"""
    state1 = SMTState()
    state2 = SMTState()
    for state in (state1, state2):
        state.evm_stack = state.evm_stack.push(BitVecVal(2, 256))
        state.evm_stack = state.evm_stack.push(BitVecVal(20, 256))
        state.evm_stack = state.evm_stack.push(BitVecVal(4, 256))
        state.evm_stack = state.evm_stack.push(BitVecVal(0, 256))
        state.evm_stack = state.evm_stack.push(BitVecVal(0x1234, 256))
        state.evm_stack = state.evm_stack.push(BitVecVal(1000, 256))

    result_state1 = evm_operator_to_z3(EvmOperator(kind="STATICCALL", pc=2), state1)
    result_state2 = evm_operator_to_z3(EvmOperator(kind="STATICCALL", pc=3), state2)
    success1, _ = result_state1.evm_stack.pop()
    success2, _ = result_state2.evm_stack.pop()

    solver = Solver()
    solver.add(success1 == BitVecVal(1, 256))
    solver.add(success2 == BitVecVal(0, 256))
    assert solver.check() == sat
