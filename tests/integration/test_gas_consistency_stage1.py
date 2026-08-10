"""阶段1 gas 一致性:内存扩展动态 gas 端到端（MSTORE + RETURN）。

mstore_return:单 block，MSTORE(offset=0) 扩内存到 32B 扣 gas，RETURN 同范围
不再扩容（lastGasCost 增量为 0）。验证 EVM 侧 memoryGasCost 建模与真实 x86
codegen(mul/mul/div + lastGasCost 增量)逐路径终值一致;div_bridge 让 Z3 收敛。
"""

import os

import pytest

from verification.program_verifier import GasCheck, ProgramEquivalenceChecker
from evm_ir.json_parser import load_ir_from_json
from evm_ir.program import EVMProgram
from x86_64.program import X86Program
from state.smt_state import SMTState


def _load_mstore_return_pair():
    test_dir = os.path.dirname(__file__)
    ir_path = os.path.join(test_dir, "..", "data", "mstore_return.json")
    hex_path = os.path.join(test_dir, "..", "data", "mstore_return.hex")
    evm_program = EVMProgram(load_ir_from_json(ir_path))
    x86_program = X86Program.from_hex(
        open(hex_path, encoding="utf-8").read().strip(), base_addr=0
    )
    return evm_program, x86_program


def test_mstore_return_memory_gas_consistency_passes():
    """MSTORE+RETURN 内存扩展动态 gas:EVM memoryGasCost == x86 mul/mul/div 链。"""
    evm_program, x86_program = _load_mstore_return_pair()

    checker = ProgramEquivalenceChecker(timeout_ms=120000, gas_check=GasCheck.FIXED_BUDGET)
    initial_state = SMTState.create_initial_state()
    verified, msg = checker.verify_program_pair(
        evm_program, x86_program, initial_state, stack_check=None
    )

    assert verified, f"memory expansion gas consistency should hold, got: {msg}"


def test_mstore_return_tampered_memory_gas_caught(monkeypatch):
    """防假绿:篡改 EVM 侧 MemoryGas 常量(3→9) → gas 检查必须 SAT。"""
    import state.evm_gas_state as gas_state
    monkeypatch.setattr(gas_state, "_MEMORY_GAS", 9)

    evm_program, x86_program = _load_mstore_return_pair()
    checker = ProgramEquivalenceChecker(timeout_ms=120000, gas_check=GasCheck.FIXED_BUDGET)
    initial_state = SMTState.create_initial_state()
    verified, msg = checker.verify_program_pair(
        evm_program, x86_program, initial_state, stack_check=None
    )

    assert not verified, "tampered MemoryGas must be caught (false green otherwise)"
    assert "gas" in msg.lower(), f"expected gas counterexample, got: {msg}"


def test_mstore_return_gas_check_off_unaffected():
    """check_gas 默认关时,mstore_return 功能等价不受 gas 建模影响(回归保护)。"""
    evm_program, x86_program = _load_mstore_return_pair()
    checker = ProgramEquivalenceChecker(timeout_ms=120000)  # check_gas 默认 False
    initial_state = SMTState.create_initial_state()  # symbolic_gas 默认 False
    verified, msg = checker.verify_program_pair(
        evm_program, x86_program, initial_state, stack_check=None
    )
    assert verified, f"functional equivalence should hold with gas off: {msg}"


def _load_pair(name):
    test_dir = os.path.dirname(__file__)
    ir_path = os.path.join(test_dir, "..", "data", f"{name}.json")
    hex_path = os.path.join(test_dir, "..", "data", f"{name}.hex")
    if not (os.path.exists(ir_path) and os.path.exists(hex_path)):
        pytest.skip(f"fixture {name} not generated (run Go TestGenGasFixtures)")
    evm = EVMProgram(load_ir_from_json(ir_path))
    x86 = X86Program.from_hex(open(hex_path, encoding="utf-8").read().strip(), base_addr=0)
    return evm, x86


def test_mload_memory_gas_consistency_passes():
    """纯 MLOAD 内存扩展动态 gas(gas_mload fixture,Go 编译器生成)。"""
    evm, x86 = _load_pair("gas_mload")
    verified, msg = ProgramEquivalenceChecker(
        timeout_ms=120000, gas_check=GasCheck.FIXED_BUDGET
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(), stack_check=None
    )
    assert verified, f"MLOAD memory gas consistency should hold, got: {msg}"


def test_mload_tampered_memory_gas_caught(monkeypatch):
    """防假绿:篡改 MemoryGas → gas_mload 应 SAT。"""
    import state.evm_gas_state as gas_state
    monkeypatch.setattr(gas_state, "_MEMORY_GAS", 9)
    evm, x86 = _load_pair("gas_mload")
    verified, msg = ProgramEquivalenceChecker(
        timeout_ms=120000, gas_check=GasCheck.FIXED_BUDGET
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(), stack_check=None
    )
    assert not verified and "gas" in msg.lower()


def test_sha3_word_gas_consistency_passes():
    """SHA3 内存扩展 + word gas(每 word 6)+ host bridge(gas_sha3 fixture)。"""
    evm, x86 = _load_pair("gas_sha3")
    verified, msg = ProgramEquivalenceChecker(
        timeout_ms=180000, gas_check=GasCheck.FIXED_BUDGET
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(), stack_check=None
    )
    assert verified, f"SHA3 word+memory gas consistency should hold, got: {msg}"


def test_sha3_tampered_word_gas_caught(monkeypatch):
    """防假绿:篡改 SHA3 word gas(6→9)→ gas_sha3 应 SAT。"""
    import state.evm_gas_state as gas_state
    orig = gas_state.word_fee
    monkeypatch.setattr(
        gas_state, "word_fee",
        lambda word_len, _const: orig(word_len, 9),
    )
    evm, x86 = _load_pair("gas_sha3")
    verified, msg = ProgramEquivalenceChecker(
        timeout_ms=180000, gas_check=GasCheck.FIXED_BUDGET
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(), stack_check=None
    )
    assert not verified and "gas" in msg.lower()


def test_calldatacopy_word_gas_consistency_passes():
    """CALLDATACOPY 内存扩展 + copy word gas(每 word 3)(gas_calldatacopy fixture)。"""
    evm, x86 = _load_pair("gas_calldatacopy")
    verified, msg = ProgramEquivalenceChecker(
        timeout_ms=180000, gas_check=GasCheck.FIXED_BUDGET
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(), stack_check=None
    )
    assert verified, f"CALLDATACOPY copy+memory gas consistency should hold, got: {msg}"


# 阶段 1d 全系列内存扩展动态 gas（Go 生成器 fixture）。
@pytest.mark.parametrize("name", [
    "gas_codecopy",    # 内存扩展 + copy word gas(3)
    "gas_mstore8",     # 内存扩展(access_size=1)
    "gas_revert",      # 内存扩展(仅, 同 RETURN)
    "gas_mcopy",       # 内存扩展 max(dst,src)+len + copy word gas(3)
])
def test_stage1d_memory_dynamic_gas_consistency(name):
    """逐指令内存扩展动态 gas 一致性(CODECOPY/MSTORE8/REVERT/MCOPY)。"""
    evm, x86 = _load_pair(name)
    verified, msg = ProgramEquivalenceChecker(
        timeout_ms=180000, gas_check=GasCheck.FIXED_BUDGET
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(), stack_check=None
    )
    assert verified, f"{name} memory gas consistency should hold, got: {msg}"


# --- RETURNDATACOPY 动态 gas（内存扩展 + copy word gas）---
#
# x86 侧是 makeCalcCopyIns(0, 2, 2)（gas_dynamic_amd64.go:153），与 CALLDATACOPY(:135)/
# CODECOPY(:141) 逐字相同——第三个参数是**栈位置**不是 gas 系数，系数固定 CopyGas=3。
#
# 两条终止路径都要验：gas 前言（impl_amd64.go:3124）排在 popUint256 与越界 errPoint
# （:3148）**之前**，EVM 侧扣费同样排在越界判断之前，故越界退出时 gas 也已扣过。
# 两格只差 return data 长度：默认 0 时 length=4 必越界(7)，给 0x100 才走到复制 + STOP(2)。

_RDC_STATE_KWARGS = [
    pytest.param({}, id="oob"),                                # returndatasize=0
    pytest.param({"return_data_size_bytes": 0x100}, id="ok"),  # 足够长
]


@pytest.mark.parametrize("state_kwargs", _RDC_STATE_KWARGS)
def test_returndatacopy_gas_consistency_passes(state_kwargs):
    """RETURNDATACOPY 内存扩展 + copy word gas 一致，越界与正常两条终止路径都验。"""
    evm, x86 = _load_pair("gas_returndatacopy")
    verified, msg = ProgramEquivalenceChecker(
        timeout_ms=180000, gas_check=GasCheck.FIXED_BUDGET
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(**state_kwargs), stack_check=None
    )
    assert verified, f"RETURNDATACOPY gas consistency should hold, got: {msg}"


@pytest.mark.parametrize("state_kwargs", _RDC_STATE_KWARGS)
def test_returndatacopy_tampered_copy_word_gas_caught(monkeypatch, state_kwargs):
    """防假绿:RETURNDATACOPY 的 copy word gas 3→9 在**两条**终止路径上都必须 SAT。

    越界那格是 gas 前言早于越界退出的可执行证据——若不然那格根本不扣 word gas、篡改
    无差别、会假绿。`3` 是字面量没有具名常量，改 gas_state.word_fee（同 EXTCODECOPY）。"""
    import state.evm_gas_state as gas_state
    orig = gas_state.word_fee
    monkeypatch.setattr(
        gas_state, "word_fee", lambda word_len, _const: orig(word_len, 9)
    )

    evm, x86 = _load_pair("gas_returndatacopy")
    verified, msg = ProgramEquivalenceChecker(
        timeout_ms=180000, gas_check=GasCheck.FIXED_BUDGET
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(**state_kwargs), stack_check=None
    )
    assert not verified, "tampered RETURNDATACOPY copy word gas must be caught"
    assert "COUNTEREXAMPLE FOUND" in msg, f"expected a counterexample, got: {msg}"
    assert "gas differs" in msg, f"expected the gas observable to differ, got: {msg}"


@pytest.mark.parametrize("state_kwargs", _RDC_STATE_KWARGS)
def test_returndatacopy_visible_fee_actually_charged(monkeypatch, state_kwargs):
    """正例非 vacuous:word gas 真的被扣了，且常量确实是 CopyGas(3)。

    断言实参而非调用次数——常量传错但仍被调用的情形照样"非 vacuous"。"""
    import evm_ir.semantics_gas as gas_sem

    seen = []
    orig = gas_sem.charge_memory_and_word_gas

    def spy(state, offset_bv, length_bv, const):
        seen.append(const)
        return orig(state, offset_bv, length_bv, const)

    monkeypatch.setattr(gas_sem, "charge_memory_and_word_gas", spy)

    evm, x86 = _load_pair("gas_returndatacopy")
    verified, msg = ProgramEquivalenceChecker(
        timeout_ms=180000, gas_check=GasCheck.FIXED_BUDGET
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(**state_kwargs), stack_check=None
    )
    assert verified, f"RETURNDATACOPY should verify, got: {msg}"
    assert seen, "RETURNDATACOPY 的 word gas 从未被扣 —— 指令没被执行到，正例是 vacuous 的"
    assert set(seen) == {3}, f"copy word gas 常量应为 CopyGas(3)，实际 {sorted(set(seen))}"


# --- A 类 LOG gas（内存扩展 + LogGas + n*TopicGas + size*DataGas，x86 全程可见）---

def test_log_gas_consistency_passes():
    """LOG1 动态 gas:EVM charge_log_gas == x86 memoryLogGas codegen 链。

    A 类真证明:LogGas(375)+TopicGas(375)+size*DataGas(8) + 内存扩展，全部在
    x86 checkMemoryAndCalcDynamicGasLog/memoryLogGas 机器码可见。"""
    evm, x86 = _load_pair("gas_log1")
    verified, msg = ProgramEquivalenceChecker(
        timeout_ms=180000, gas_check=GasCheck.FIXED_BUDGET
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(), stack_check=None
    )
    assert verified, f"LOG gas consistency should hold, got: {msg}"


def test_log_tampered_data_gas_caught(monkeypatch):
    """防假绿:篡改 LOG **每字节** data gas(8→99) → gas 检查必须 SAT。"""
    import state.evm_gas_state as gas_state
    monkeypatch.setattr(gas_state, "_LOG_DATA_GAS", 99)

    evm, x86 = _load_pair("gas_log1")
    verified, msg = ProgramEquivalenceChecker(
        timeout_ms=180000, gas_check=GasCheck.FIXED_BUDGET
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(), stack_check=None
    )
    assert not verified, "tampered LOG data gas must be caught (false green otherwise)"
    assert "gas" in msg.lower(), f"expected gas counterexample, got: {msg}"


def test_log_tampered_flat_gas_caught(monkeypatch):
    """防假绿:篡改 LOG 常量 gas(LogGas 375→111) → gas 检查必须 SAT。"""
    import state.evm_gas_state as gas_state
    monkeypatch.setattr(gas_state, "_LOG_GAS", 111)

    evm, x86 = _load_pair("gas_log1")
    verified, msg = ProgramEquivalenceChecker(
        timeout_ms=180000, gas_check=GasCheck.FIXED_BUDGET
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(), stack_check=None
    )
    assert not verified, "tampered LogGas must be caught (false green otherwise)"
    assert "gas" in msg.lower(), f"expected gas counterexample, got: {msg}"


def test_log_tampered_topic_gas_caught(monkeypatch):
    """防假绿:篡改 LOG 每 topic gas(TopicGas 375→111) → gas 检查必须 SAT。

    gas_log1 是 LOG1（1 个 topic），独立验证 n*TopicGas 项;_LOG_TOPIC_GAS 与
    _LOG_GAS 同为 375，单独篡改 TopicGas 可抓出把两者混淆/常量折叠的 bug。"""
    import state.evm_gas_state as gas_state
    monkeypatch.setattr(gas_state, "_LOG_TOPIC_GAS", 111)

    evm, x86 = _load_pair("gas_log1")
    verified, msg = ProgramEquivalenceChecker(
        timeout_ms=180000, gas_check=GasCheck.FIXED_BUDGET
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(), stack_check=None
    )
    assert not verified, "tampered LogTopicGas must be caught (false green otherwise)"
    assert "gas" in msg.lower(), f"expected gas counterexample, got: {msg}"


# --- LOG 的 topic 数（n=0/1/4 三点钉死 gas = 常量 + n*TopicGas 的线性项）---
#
# gas_log1 单点验不到 topic 数**读取链**：把 EVM 侧 n 写死成常量 1 这类错误在 n=1 上
# 没有任何差别。补上 n=0（topic 项消失）与 n=4（最大值）两个边界即可检出。

@pytest.mark.parametrize("name", ["gas_log0", "gas_log4"])
def test_log_topic_count_gas_consistency_passes(name):
    """LOG0/LOG4 的 n*TopicGas 与 x86 memoryLogGas 的 MOVQ n*LogTopicGas 一致。"""
    evm, x86 = _load_pair(name)
    verified, msg = ProgramEquivalenceChecker(
        timeout_ms=180000, gas_check=GasCheck.FIXED_BUDGET
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(), stack_check=None
    )
    assert verified, f"{name} gas consistency should hold, got: {msg}"


@pytest.mark.parametrize("name", ["gas_log0", "gas_log4"])
def test_log_topic_count_read_as_constant_caught(monkeypatch, name):
    """防假绿:EVM 侧把 topic 数当成常量 1 读 → LOG0(0→1)、LOG4(4→1) 都必须 SAT。
    这是这两条 fixture 的核心增量，gas_log1 结构上抓不到（n 本来就是 1）。

    篡改点必须落在 **gas 公式**上，不能改 IR 的 op.immediate——go_function_semantics.py
    的 LOG bridge 会拿 evm_immediate 与 x86 栈上的 n_topics 比对，不一致时抛
    GoFunctionSemanticsError，那个守卫比 gas 比较更早，会让这条以错误的理由变红。"""
    import evm_ir.semantics_gas as gas_sem
    orig = gas_sem.charge_log_gas
    monkeypatch.setattr(
        gas_sem, "charge_log_gas",
        lambda state, offset_bv, size_bv, _n_topics: orig(state, offset_bv, size_bv, 1),
    )

    evm, x86 = _load_pair(name)
    verified, msg = ProgramEquivalenceChecker(
        timeout_ms=180000, gas_check=GasCheck.FIXED_BUDGET
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(), stack_check=None
    )
    assert not verified, f"{name}: topic 数被当成常量 1 必须被抓到"
    assert "COUNTEREXAMPLE FOUND" in msg, f"expected a counterexample, got: {msg}"
    assert "gas differs" in msg, f"expected the gas observable to differ, got: {msg}"


def test_log4_tampered_topic_gas_caught(monkeypatch):
    """防假绿:TopicGas 375→111 在 LOG4 上必须 SAT（delta 是 LOG1 那条的 4 倍）。"""
    import state.evm_gas_state as gas_state
    monkeypatch.setattr(gas_state, "_LOG_TOPIC_GAS", 111)

    evm, x86 = _load_pair("gas_log4")
    verified, msg = ProgramEquivalenceChecker(
        timeout_ms=180000, gas_check=GasCheck.FIXED_BUDGET
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(), stack_check=None
    )
    assert not verified, "tampered LogTopicGas must be caught on LOG4"
    assert "COUNTEREXAMPLE FOUND" in msg, f"expected a counterexample, got: {msg}"
    assert "gas differs" in msg, f"expected the gas observable to differ, got: {msg}"


@pytest.mark.parametrize("name,expected_topics", [
    ("gas_log0", 0),
    ("gas_log1", 1),
    ("gas_log4", 4),
])
def test_log_fee_actually_charged_with_expected_topic_count(
    monkeypatch, name, expected_topics
):
    """正例非 vacuous:LOG fee 真的被扣了，且 n_topics 确实是各 fixture 的那个值。

    断言实参而非调用次数——n 传错但仍被调用的情形照样"非 vacuous"。"""
    import evm_ir.semantics_gas as gas_sem

    seen = []
    orig = gas_sem.charge_log_gas

    def spy(state, offset_bv, size_bv, n_topics):
        seen.append(n_topics)
        return orig(state, offset_bv, size_bv, n_topics)

    monkeypatch.setattr(gas_sem, "charge_log_gas", spy)

    evm, x86 = _load_pair(name)
    verified, msg = ProgramEquivalenceChecker(
        timeout_ms=180000, gas_check=GasCheck.FIXED_BUDGET
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(), stack_check=None
    )
    assert verified, f"{name} should verify, got: {msg}"
    assert seen, f"{name}: LOG fee 从未被扣 —— 指令没被执行到，正例是 vacuous 的"
    assert set(seen) == {expected_topics}, (
        f"{name}: n_topics 应为 {expected_topics}，实际 {sorted(set(seen))}"
    )


def test_log_gas_check_off_unaffected():
    """check_gas 默认关时,LOG 功能等价不受 gas 建模影响(回归保护)。"""
    evm, x86 = _load_pair("gas_log1")
    verified, msg = ProgramEquivalenceChecker(timeout_ms=180000).verify_program_pair(
        evm, x86, SMTState.create_initial_state(), stack_check=None
    )
    assert verified, f"functional equivalence should hold with gas off: {msg}"


# --- 并行 path_observations 模式回归（worker 私有 solver 未 reset → gas 假绿 bug）---

def test_memory_gas_parallel_pathobs_passes():
    """阶段1 内存扩展 gas 在并行 path_observations 模式下正确通过。"""
    evm, x86 = _load_pair("gas_mload")
    verified, msg = ProgramEquivalenceChecker(
        timeout_ms=180000, gas_check=GasCheck.FIXED_BUDGET
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(),
        stack_check=None, path_observations=True, path_pair_workers=2,
    )
    assert verified, f"MLOAD gas should verify in parallel mode, got: {msg}"


def test_memory_gas_parallel_pathobs_tamper_caught(monkeypatch):
    """**核心回归**:篡改内存 gas 常量后，并行 path_observations 模式**必须** SAT。

    曾有 bug:worker 私有 solver 在 gas 检查处不 reset，继承前序 memory 检查的累积
    UNSAT 断言 → gas 查询 vacuous UNSAT → 假绿。此测试覆盖既有 stage1 路径（非仅
    B 类 host UF），确保根因修复对所有 gas 检查生效。"""
    import state.evm_gas_state as gas_state
    monkeypatch.setattr(gas_state, "_MEMORY_GAS", 9)

    evm, x86 = _load_pair("gas_mload")
    verified, msg = ProgramEquivalenceChecker(
        timeout_ms=180000, gas_check=GasCheck.FIXED_BUDGET
    ).verify_program_pair(
        evm, x86, SMTState.create_initial_state(),
        stack_check=None, path_observations=True, path_pair_workers=2,
    )
    assert not verified, "parallel-mode memory-gas mismatch must be caught (false green bug)"
    assert "gas" in msg.lower(), f"expected gas counterexample, got: {msg}"
