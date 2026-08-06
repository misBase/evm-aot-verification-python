"""合约级 gas 一致性:真实完整合约规模的端到端验证。

stage0/1/3/host_uf 的被验对象都是单指令级或极小 fixture（gas_*.json、add_with_push、
mstore_return），本文件是 gas 检查在**真实合约规模**上的唯一覆盖:13~723 个 block、
完整 dispatcher、SHA3 mapping key、SLOAD/SSTORE/CALL 的 host UF、多条 RETURN/REVERT
终止路径。

为什么这块单独立文件:program_verifier 的 GasCheck 注释预警过，开 gas 会打开 host gas
UF，使后继 block 的 `ULT(gas, static_gas)` 不再折得掉、OOG 分支全部存活（合成 12 block
+ 1 SLOAD 实测 EVM 终止路径 1→12、候选 pair 1→144），而"大合约上的实际膨胀"当时未实测。
下表是本文件建立时的实测值:

    fixture(规模)                     模式            耗时    路径(EVM/x86)
    perf_erc20_lite(13 block)         FIXED_BUDGET    8.7s    7 / 8
    perf_erc20_lite                   FULL            12.7s   24 / 29
    CErc20 decimals()(723 block)      FIXED_BUDGET    4.9s    5 / 5
    CErc20 decimals()                 FULL            7.6s    18 / 18
    ENSRegistry owner()(127 block)    FIXED_BUDGET    9.3s    11 / 11
    muti_block(40 block)              FIXED_BUDGET    41s     30 / 30（上界生效后）

结论:膨胀远小于预警量级，FULL（对所有初始 gas 量化 + OOG 路径）在 723 block 的
CErc20 上也只要 7.6s。muti_block 曾是唯一例外（输入形态本就撑开路径，再乘 OOG 分支后
30→102+、>25min 未跑完），host-gas 协议上界把 OOG 分支压死后回到 30 条 / 41s。

强度边界与 stage0/1/3 相同:正例只说明两侧一致，不排除 gas 根本没进比较，故每条正例
都断言 message 带 gas scope 后缀，另有三条篡改用例（静态 gas / host UF / 功能 bug）
作为非 vacuous 的证据。
"""

import os

import pytest

from evm_ir.json_parser import load_ir_from_json
from evm_ir.program import EVMProgram
from state.smt_state import SMTState
from verification.program_verifier import (
    GasCheck,
    ProgramEquivalenceChecker,
    _find_unsupported_dynamic_gas_ops,
)
from x86_64.program import X86Program
from x86_64.summaries import TRUSTED_SUMMARY_CONFIG

# 合约 fixture 的加载与 selector 构造与功能等价测试完全一致，直接复用，
# 避免两处各写一份 selector 写入逻辑而悄悄漂移。
from tests.integration.test_ext_contract_verification import (
    _load_ext_contract_pair,
    _selector_state,
)

# 成功消息里的 gas 结论范围（_annotate_gas_scope 写入）。断言它才能区分
# "gas 验过了" 与 "gas_check 被静默降级成 OFF 仍全绿"。
FIXED_BUDGET_SCOPE = "gas equivalent for the fixed initial budget"
FULL_SCOPE = "gas and OOG paths equivalent over all initial gas values"


def _load_data_pair(name, hex_name=None):
    """加载 tests/data 下的 <name>.json + <hex_name or name>.hex。"""
    test_dir = os.path.dirname(__file__)
    ir_path = os.path.join(test_dir, "..", "data", f"{name}.json")
    hex_path = os.path.join(test_dir, "..", "data", f"{hex_name or name}.hex")
    evm_program = EVMProgram(load_ir_from_json(ir_path))
    x86_program = X86Program.from_hex(
        open(hex_path, encoding="utf-8").read().strip(), base_addr=0
    )
    return evm_program, x86_program


def _verify_with_gas(evm_program, x86_program, initial_state, *, mode, **kwargs):
    """按 mode 跑一次带 gas 检查的程序对验证。

    path_observations 由 verify_program_pair 在 gas 模式下强制打开（merged-result
    模式会把 path-local 的动态 gas scope assumption 泄漏成全局条件），这里显式传上
    保持调用点自解释。
    """
    kwargs.setdefault("path_observations", True)
    kwargs.setdefault("path_pair_workers", 4)
    return ProgramEquivalenceChecker(
        timeout_ms=600_000, gas_check=mode
    ).verify_program_pair(
        evm_program, x86_program, initial_state, stack_check=None, **kwargs
    )


def _erc20_lite_kwargs():
    """perf_erc20_lite 的验证参数（与功能等价测试同一组）。"""
    return dict(enable_merge=True, summary_config=TRUSTED_SUMMARY_CONFIG)


def _ext_contract_kwargs():
    """ext_contracts 的验证参数：CFG 更深，且 merge 会注入大的 path-conditioned ITE。"""
    return dict(
        enable_merge=False,
        summary_config=TRUSTED_SUMMARY_CONFIG,
        x86_reachability_timeout_ms=250,
        max_depth=100_000,
    )


# ---------------------------------------------------------------- 正例


def test_perf_erc20_lite_gas_fixed_budget():
    """真实 ERC20（全符号 calldata）在固定预算下 gas 终值两侧一致。

    13 个 block 覆盖 dispatcher、selector 分支、SHA3 mapping key、SLOAD/SSTORE 的
    host UF、MSTORE 内存扩展、RETURN/REVERT 多终止路径——即三类 gas（静态 / 可见动态 /
    host UF）在同一个程序里混合。
    """
    evm_program, x86_program = _load_data_pair("perf_erc20_lite")

    verified, msg = _verify_with_gas(
        evm_program,
        x86_program,
        SMTState.create_initial_state(),
        mode=GasCheck.FIXED_BUDGET,
        **_erc20_lite_kwargs(),
    )

    assert verified, f"perf_erc20_lite gas consistency should hold, got: {msg}"
    assert FIXED_BUDGET_SCOPE in msg, f"gas scope missing from message: {msg}"


def test_perf_erc20_lite_gas_full():
    """同一合约在 FULL（符号 gas）下 gas + OOG 路径对所有初始预算量化成立。

    符号 gas 让每个 block 的 OOG 分支都存活:EVM 终止路径 7→24、x86 8→29，仍在秒级。
    """
    evm_program, x86_program = _load_data_pair("perf_erc20_lite")

    verified, msg = _verify_with_gas(
        evm_program,
        x86_program,
        SMTState.create_initial_state(symbolic_gas=True),
        mode=GasCheck.FULL,
        **_erc20_lite_kwargs(),
    )

    assert verified, f"perf_erc20_lite FULL gas consistency should hold, got: {msg}"
    assert FULL_SCOPE in msg, f"gas scope missing from message: {msg}"


@pytest.mark.parametrize("mode,scope", [
    (GasCheck.FIXED_BUDGET, FIXED_BUDGET_SCOPE),
    (GasCheck.FULL, FULL_SCOPE),
])
def test_cerc20_decimals_gas(mode, scope):
    """723 block 的 Compound CErc20，固定 selector 进 decimals()。

    合约整体含 154 SLOAD / 68 SSTORE / 14 CALL / 12 STATICCALL，是 host UF 覆盖面
    最广的 fixture；固定 selector 是为了不进生成的 string 循环（与功能等价测试同因）。
    """
    evm_program, x86_program = _load_ext_contract_pair("compound_cerc20", "CErc20")
    initial_state = _selector_state(  # decimals()
        0x313CE567, calldata_size=4, symbolic_gas=mode is GasCheck.FULL
    )

    verified, msg = _verify_with_gas(
        evm_program, x86_program, initial_state, mode=mode, **_ext_contract_kwargs()
    )

    assert verified, f"CErc20 decimals() gas consistency should hold, got: {msg}"
    assert scope in msg, f"gas scope missing from message: {msg}"


def test_ens_registry_owner_gas_fixed_budget():
    """ENSRegistry.owner(bytes32):SHA3 mapping key 的 word gas 与 SLOAD host UF 混合。

    127 block，合约整体 28 处 SHA3 / 21 SLOAD——可见动态 gas（SHA3 word cost + 内存
    扩展）与不可见 host gas 在同一条路径上叠加，是 stage1 单指令 fixture 覆盖不到的组合。
    """
    evm_program, x86_program = _load_ext_contract_pair("ens_registry", "ENSRegistry")
    # 4 字节 selector + 32 字节 bytes32 参数
    initial_state = _selector_state(0x02571BE3, calldata_size=36)

    verified, msg = _verify_with_gas(
        evm_program,
        x86_program,
        initial_state,
        mode=GasCheck.FIXED_BUDGET,
        **_ext_contract_kwargs(),
    )

    assert verified, f"ENSRegistry owner() gas consistency should hold, got: {msg}"
    assert FIXED_BUDGET_SCOPE in msg, f"gas scope missing from message: {msg}"


# ---------------------------------------------------------------- 防假绿


def test_perf_erc20_lite_tampered_static_gas_caught():
    """篡改入口 block 的 static_gas（+1）→ 必须抓到 gas 反例。

    只动 1 个 block、只差 1 gas:比整体改成常数更小的扰动，不改变路径结构，
    因此抓到反例只能来自 gas 比较本身。
    """
    evm_program, x86_program = _load_data_pair("perf_erc20_lite")
    evm_program.blocks[0].static_gas += 1

    verified, msg = _verify_with_gas(
        evm_program,
        x86_program,
        SMTState.create_initial_state(),
        mode=GasCheck.FIXED_BUDGET,
        **_erc20_lite_kwargs(),
    )

    assert not verified, "tampered static_gas must be caught (false green otherwise)"
    # 必须断言到**反例**，不能只查 "gas" 子串——`GAS CHECK INCOMPLETE`、配置错误等
    # 非目标失败同样含 "gas"，会让这条测试被它没在验的东西满足。
    assert "COUNTEREXAMPLE FOUND" in msg, f"expected a counterexample, got: {msg}"
    assert "gas differs" in msg, f"expected the gas observable to differ, got: {msg}"


def test_perf_erc20_lite_tampered_host_gas_uf_caught(monkeypatch):
    """x86 侧 SLOAD 的 host UF 用错 opcode → 两侧不相消 → 抓到 gas 反例。

    证明真实合约里的 host gas UF 确实进了 gas 比较，而不是被功能等价的路径条件
    化简掉。monkeypatch 不跨 worker 进程传播，故 path_pair_workers=1。
    """
    import x86_64.go_function_semantics as gfs
    orig = gfs.GoFunctionSemantics._deduct_host_gas_uf

    def tampered(self, mstate, opcode, args):
        return orig(self, mstate, "WRONGOP" if opcode == "SLOAD" else opcode, args)

    monkeypatch.setattr(gfs.GoFunctionSemantics, "_deduct_host_gas_uf", tampered)

    evm_program, x86_program = _load_data_pair("perf_erc20_lite")
    verified, msg = _verify_with_gas(
        evm_program,
        x86_program,
        SMTState.create_initial_state(),
        mode=GasCheck.FIXED_BUDGET,
        path_pair_workers=1,
        **_erc20_lite_kwargs(),
    )

    assert not verified, "tampered x86 host-gas UF must be caught"
    assert "COUNTEREXAMPLE FOUND" in msg, f"expected a counterexample, got: {msg}"
    assert "gas differs" in msg, f"expected the gas observable to differ, got: {msg}"


def test_perf_erc20_lite_sbb_bug_still_caught_with_gas():
    """开 gas 后功能 bug 仍被抓:SBB→SUB 的 borrow 传播错误 → storage 反例。

    gas 模式会新增大量 OOG 分支与 path-local assumption，这条确认它们没有把原本可见的
    功能反例约束掉（assumption 泄漏成全局条件就会出现这种假绿）。
    """
    evm_program, x86_program = _load_data_pair(
        "perf_erc20_lite", hex_name="perf_erc20_lite_bug"
    )

    verified, msg = _verify_with_gas(
        evm_program,
        x86_program,
        SMTState.create_initial_state(),
        mode=GasCheck.FIXED_BUDGET,
        **_erc20_lite_kwargs(),
    )

    assert not verified, "SBB->SUB bug must still be caught with gas check on"
    assert "COUNTEREXAMPLE" in msg, f"expected counterexample, got: {msg}"


# ---------------------------------------------------------------- fail-closed


def test_safe_no_longer_rejected_by_gas_scope():
    """Safe（含 1 处 EXTCODECOPY@pc=0x2366）不再被 gas scope 守卫拒绝受理。

    这条曾是「拒绝集在真实合约上生效」的证据。EXTCODECOPY 解禁后语义反转：守卫必须
    **放行**它。

    直接对真实合约调用守卫函数，而不是跑 verify_program_pair 再看消息里有没有那句
    拒绝文案——后者会被任何其它预检失败（IR 不变量、gas 配置、超时）弄成假绿。
    """
    evm_program, _ = _load_ext_contract_pair("safe", "Safe")

    assert _find_unsupported_dynamic_gas_ops(evm_program) == [], (
        "Safe 不应再被 gas scope 守卫拒绝"
    )
    # 前提校验：这个合约确实含 EXTCODECOPY，否则上面那条断言是 vacuous 的。
    kinds = {
        (getattr(op, "kind", "") or "").upper()
        for block in evm_program.blocks
        for op in block.operations
    }
    assert "EXTCODECOPY" in kinds, "fixture 变了：Safe 不再含 EXTCODECOPY"


@pytest.mark.skip(reason=(
    "Safe 全合约端到端在 gas 模式下未跑通：无 selector 约束时 742 block 的 dispatcher "
    "撑开路径，实测 >6.5min 仍停在符号执行阶段。**这不是本次 EXTCODECOPY 解禁引入的**"
    "——Safe 在本仓库从来没有任何端到端覆盖，连 GasCheck.OFF 的功能等价测试都不存在"
    "（tests/integration/test_ext_contract_verification.py 里没有 Safe）。启用前需要先"
    "定位一个能到达 block pc=0x235f（EXTCODECOPY 所在块）的 selector 并压下路径规模。"
    "EXTCODECOPY 自身的 gas 覆盖由 gas_extcodecopy / gas_extcodecopy_sym 提供，其可达性"
    "由 test_gas_consistency_host_uf.py 的 *_visible_fee_actually_charged 用 spy 计数坐实。"
))
def test_safe_extcodecopy_gas_consistency():
    """Safe 的 EXTCODECOPY 端到端 gas 一致性（待路径规模压下来后启用）。"""
    evm_program, x86_program = _load_ext_contract_pair("safe", "Safe")

    verified, msg = _verify_with_gas(
        evm_program,
        x86_program,
        SMTState.create_initial_state(),
        mode=GasCheck.FIXED_BUDGET,
    )

    assert verified, f"Safe gas consistency should hold, got: {msg}"
    assert FIXED_BUDGET_SCOPE in msg, f"gas scope missing from message: {msg}"


# ------------------------------------------------ 曾经的规模瓶颈（上界生效后已解）


def test_muti_block_gas_fixed_budget():
    """muti_block（40 block，全符号 calldata 长度）的 gas 一致性。

    这条曾长期 skip：开 gas 后 host UF 无约束 → 后继 block 的 `ULT(gas, static_gas)`
    折不掉、OOG 分支全部存活，x86 终止路径从 30 涨到 102+，>25min 仍停在 pair
    feasibility。`HOST_GAS_UPPER_BOUNDS`（见 state/host_gas.py）把这批分支重新压死后
    实测 **41s / 16 EVM × 30 x86 路径 / 30 个可行 pair**，路径数回到与 OFF 相同的 30。

    它同时是"上界确实在剪枝"的端到端凭证——单元测试只能证明约束进了求解器，压不出
    这个量级的差别。
    """
    evm_program, x86_program = _load_data_pair("muti_block")
    initial_state = SMTState.create_initial_state(
        calldata_size_max_bytes=(1 << 63) - 1,
    )
    initial_state.abstract_calldataload_words = True

    verified, msg = _verify_with_gas(
        evm_program,
        x86_program,
        initial_state,
        mode=GasCheck.FIXED_BUDGET,
        enable_merge=False,
        summary_config=TRUSTED_SUMMARY_CONFIG,
        x86_reachability_timeout_ms=250,
    )

    assert verified, f"muti_block gas consistency should hold, got: {msg}"
    assert FIXED_BUDGET_SCOPE in msg, f"gas scope missing from message: {msg}"
