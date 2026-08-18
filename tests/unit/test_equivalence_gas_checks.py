"""`GasEquivalenceChecks` 的直接单测——防假绿分支在此集中。

这些分支此前只有端到端的间接覆盖：`tests/unit/test_path_observation_gas.py` 只测
`PathObservation` 这个 dataclass（键存在、必填、None 往返），碰不到 checker 本身。而
`GAS CHECK INCOMPLETE` 与 UNKNOWN 两条 fail-closed 正是防假绿的关键路径。

`_EquivalenceContext` 无外部依赖，可直接构造，所以这里真调 checker，不用 mock。
"""

import pytest
from z3 import BitVec, BitVecSort, BitVecVal, BoolVal, K, Solver

from verification.equivalence_checker import EquivalenceChecker
from verification.equivalence_context import _EquivalenceContext
from verification.equivalence_gas import GasEquivalenceChecks


def _checks(timeout_ms: int = 5000) -> GasEquivalenceChecks:
    return GasEquivalenceChecks(_EquivalenceContext(timeout_ms=timeout_ms))


def _check(checks: GasEquivalenceChecks, evm_gas, x86_gas, solver=None):
    """按生产调用点（equivalence_outputs.py）的形状调用。"""
    return checks._check_gas_equivalence_with_solver(
        solver if solver is not None else checks._ctx.solver,
        evm_gas,
        x86_gas,
    )


# --- gas 观测缺失：一律 fail-closed ---


def test_both_sides_missing_gas_is_fail_closed():
    """两侧都没有 gas 观测**不是** skip，是失败。

    走到 checker 就意味着 gas 检查已启用（`EquivalenceChecker` 只在 check_gas 为真时
    构造它，`OutputEquivalenceChecks` 用 `if self._gas is not None` 挡住关闭态）。所以
    这个形态不是"本次没建模 gas"，而是观测本该有却丢了——`_PATH_RESULT_KEYS` 漏键、
    并行 worker 跨 Context 翻译丢失、aggregate fallback 掉字段。静默 True 就是假绿。
    """
    verified, msg = _check(_checks(), None, None)

    assert not verified, "两侧缺 gas 必须 fail-closed，不能 skip 成通过"
    assert "GAS CHECK INCOMPLETE" in msg
    assert "neither side" in msg


@pytest.mark.parametrize("missing_side,evm_gas,x86_gas", [
    ("EVM", None, BitVecVal(100, 64)),
    ("x86", BitVecVal(100, 64), None),
])
def test_one_side_missing_gas_is_fail_closed(missing_side, evm_gas, x86_gas):
    """单侧缺 gas 时消息要点名是哪一侧——否则排查时无从下手。"""
    verified, msg = _check(_checks(), evm_gas, x86_gas)

    assert not verified
    assert "GAS CHECK INCOMPLETE" in msg
    assert missing_side in msg


# --- 正常判定 ---


def test_equal_gas_verifies():
    verified, msg = _check(_checks(), BitVecVal(100, 64), BitVecVal(100, 64))

    assert verified, msg
    assert "Gas equivalent" in msg


def test_differing_gas_yields_counterexample():
    verified, msg = _check(_checks(), BitVecVal(100, 64), BitVecVal(200, 64))

    assert not verified
    assert "COUNTEREXAMPLE FOUND" in msg
    assert "gas differs" in msg


def test_symbolically_differing_gas_yields_counterexample():
    """符号形态：`g` vs `g-1` 恒不等，必须给出反例而不是相消。"""
    g = BitVec("g", 64)
    verified, msg = _check(_checks(), g, g - BitVecVal(1, 64))

    assert not verified
    assert "gas differs" in msg


# --- reset 语义：不得继承前序 UNSAT 基底 ---


def test_inherited_unsat_base_does_not_vacuously_pass():
    """solver 带着 UNSAT 基底进来时，gas 查询必须照常判定。

    这是 [[gas_parallel_pathobs_false_green]] 的单元级回归：并行 worker 的私有 solver
    在同一次 check_observables 里已被前序 memory/storage 子检查累积成 UNSAT 基底（等价
    查询本就是"找不到反例 → unsat"）。若这里只 push/pop 而不 reset，gas 查询会叠在该
    基底上恒 UNSAT → 一律"通过"。

    构造：预置 `False`，再喂一对**必然不等**的 gas。没有 reset 就会返回 True。
    """
    checks = _checks()
    solver = Solver()
    solver.add(BoolVal(False))

    verified, msg = _check(checks, BitVecVal(1, 64), BitVecVal(2, 64), solver=solver)

    assert not verified, "继承 UNSAT 基底导致 vacuous 通过——reset 丢了"
    assert "gas differs" in msg


# --- UNKNOWN：fail-closed ---


class _UnknownSolver:
    """`check()` 恒返回 unknown 的替身。

    比"1ms 超时 + 一个 bit-blast 爆炸的表达式"稳定：后者是否真的 unknown 取决于机器
    速度与 Z3 版本，会变成 flaky 测试。
    """

    def __init__(self):
        self.assertions = []

    def reset(self):
        self.assertions = []

    def set(self, *_args, **_kwargs):
        pass

    def add(self, *exprs):
        self.assertions.extend(exprs)

    def check(self, *_assumptions):
        from z3 import unknown
        return unknown

    def reason_unknown(self):
        return "test-stub"


def test_unknown_result_is_fail_closed():
    """求解器给不出结论时按失败处理——unknown 不等于等价。"""
    checks = _checks()

    verified, msg = _check(
        checks, BitVecVal(1, 64), BitVecVal(2, 64), solver=_UnknownSolver(),
    )

    assert not verified, "UNKNOWN 必须 fail-closed"
    assert "UNKNOWN" in msg
    assert "test-stub" in msg


# --- gas 漏键在四条编排路径上都要 fail-closed ---
#
# 漏键的成因分布在不同路径上（_PATH_RESULT_KEYS 白名单、worker 跨 Context 翻译、
# aggregate fallback 另走一套入口），所以四条各钉一次。它们最终都汇到
# OutputEquivalenceChecks._check_state_observables_with_solver，但"汇得到"正是要验的。


def _result_with_gas(gas):
    """一个能走完 return-data / status 检查、停在 gas 上的最小 result。

    gas=None 模拟 producer 漏键（`.get('gas')` 拿不到）。
    """
    from evm_ir.status_code import EvmStatusCode

    return {
        "offset": BitVecVal(0, 64),
        "length": BitVecVal(0, 64),
        "memory": K(BitVecSort(64), BitVecVal(0, 8)),
        "base_addr": None,
        "has_return_data": BoolVal(False),
        "status_code": BitVecVal(EvmStatusCode.STOPPED, 8),
        "gas": gas,
    }


def _gas_checker() -> EquivalenceChecker:
    return EquivalenceChecker(timeout_ms=10000, verbose=False, check_gas=True)


def _assert_gas_incomplete(verified, msg, where):
    assert not verified, f"{where}: gas 漏键必须 fail-closed，实际通过了"
    assert "GAS CHECK INCOMPLETE" in msg, f"{where}: 消息未点明 gas 缺失：{msg}"


def test_merged_path_fails_closed_on_missing_gas():
    """merged 模式（check_equivalence 顶层入口），**两侧同时**缺。

    两侧同缺是白名单/翻译漏键的真实形态（同一套 producer，丢就一起丢），也正是旧代码
    skip 成 True 的那条。单侧缺的形态由 serial / aggregate 两条覆盖。
    """
    checker = _gas_checker()
    verified, msg = checker.check_equivalence(
        _result_with_gas(None), _result_with_gas(None),
    )
    _assert_gas_incomplete(verified, msg, "merged")


def test_serial_path_pair_fails_closed_on_missing_gas():
    """逐路径串行（equivalence_paths.py 的 check_observables 调用点）。"""
    checker = _gas_checker()
    verified, msg = checker._outputs.check_observables(
        _result_with_gas(BitVecVal(100, 64)), _result_with_gas(None),
    )
    _assert_gas_incomplete(verified, msg, "serial")


def test_parallel_worker_fails_closed_on_missing_gas():
    """并行 worker 的私有 solver 入口（check_observables_with_solver）。

    并行是漏键最容易发生的地方：worker 私有 Context 只翻译 `_PATH_RESULT_KEYS`
    列出的键。
    """
    checker = _gas_checker()
    verified, msg = checker._outputs.check_observables_with_solver(
        Solver(), _result_with_gas(None), _result_with_gas(None),
    )
    _assert_gas_incomplete(verified, msg, "parallel")


def test_aggregate_fallback_fails_closed_on_missing_gas():
    """aggregate fallback 命中后接管的那条分支（另走
    `_check_path_pair_status_and_state_observables`，不经 check_observables）。"""
    checker = _gas_checker()
    verified, msg = checker._paths._check_path_pair_status_and_state_observables(
        _result_with_gas(BitVecVal(100, 64)),
        _result_with_gas(None),
        None,
        # 这条入口在生产里总是拿到 pair 的 path condition；`_check_status_code_with_solver`
        # 也没有 None 守卫（`solver.add(path_condition)` 直接加），所以传真实形态。
        BoolVal(True),
        "aggregate-fallback",
    )
    _assert_gas_incomplete(verified, msg, "aggregate fallback")


def test_gas_is_in_parallel_translation_whitelist():
    """`gas` 必须在 `_PATH_RESULT_KEYS` 里——漏了会让并行路径的 gas 恒为 None。

    有了上面的 fail-closed 收口，漏键不再假绿而是全量报 GAS CHECK INCOMPLETE；这条锁在
    这里是为了让失败原因一眼可辨，而不是让人去猜为什么每条路径都缺 gas。
    """
    from verification.equivalence_paths import _PATH_RESULT_KEYS

    assert "gas" in _PATH_RESULT_KEYS
    assert "status_code" in _PATH_RESULT_KEYS
