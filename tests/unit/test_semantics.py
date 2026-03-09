#!/usr/bin/env python3
"""测试EVM和x86-64操作语义。"""

from common.uint256 import Uint256
from evm_ir.semantics import EVMIRSemantics, EVMOperationSemantics, evm_operator_to_z3
from evm_ir.models import EvmOperator
from x86_64.semantics import X86SemanticsModel
from x86_64.models import Register
from verification.refinement_checker import RefinementChecker
from state.smt_state import SMTState, EVMMemoryState
from z3 import BitVecVal, simplify, is_true, Solver, sat

# x86-64 ADD操作十六进制序列（来自AOT编译器输出）
X86_ADD_HEX_SEQUENCE = "498b46c0490346e0498b4ec849134ee8498b56d0491356f0498b5ed849135ef8498946c049894ec8498956d049895ed8"
X86_ADD_BASE_ADDR = 0x6c


def test_basic_imports():
    """测试所有模块是否可以导入。"""
    # 如果导入失败，将自动抛出异常
    pass


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


def test_refinement_checker():
    """使用具体值测试精化检查器。"""
    checker = RefinementChecker(timeout_ms=5000, verbose=False)
    
    # 使用等价值测试
    evm_result = BitVecVal(0x70, 256)
    x86_result = BitVecVal(0x70, 256)
    
    verified, msg = checker.check_refinement(evm_result, x86_result)
    assert verified, f"Equivalent values should verify, but got: {msg}"
    
    # 使用不同值测试
    evm_result2 = BitVecVal(0x70, 256)
    x86_result2 = BitVecVal(0x71, 256)
    
    verified2, msg2 = checker.check_refinement(evm_result2, x86_result2)
    assert not verified2, \
        f"Different values should not verify (0x70 != 0x71), but verification passed: {msg2}"


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
    solver.add(result_state.evm_memory.MSize == BitVecVal(6, 64))
    assert solver.check() == sat

    # case2: 256位offset截断到64位
    state2 = SMTState()
    state2.evm_memory = EVMMemoryState(msize=BitVecVal(0, 64))
    state2.evm_stack = state2.evm_stack.push(BitVecVal(0xABCD, 256))          # value
    state2.evm_stack = state2.evm_stack.push(BitVecVal((1 << 64) + 3, 256))   # offset
    result_state2 = evm_operator_to_z3(op, state2)

    solver2 = Solver()
    solver2.add(result_state2.evm_memory.get_byte(BitVecVal(3, 64)) == BitVecVal(0xCD, 8))
    solver2.add(result_state2.evm_memory.MSize == BitVecVal(4, 64))
    assert solver2.check() == sat


