"""阶段0 gas 一致性:PathObservation 携带 gas 字段。"""

import pytest
from z3 import BitVec, BitVecVal, BoolVal

from common.path_observation import PathObservation, OBSERVATION_KEYS


def _obs(**overrides):
    base = dict(
        condition=BoolVal(True),
        offset=BitVecVal(0, 64),
        length=BitVecVal(0, 64),
        memory=None,
        base_addr=None,
        has_return_data=BoolVal(False),
        storage=None,
        transient_storage=None,
        status_code=BitVecVal(0, 8),
        gas=None,
    )
    base.update(overrides)
    return PathObservation(**base)


def test_gas_in_observation_keys():
    assert "gas" in OBSERVATION_KEYS


def test_gas_is_required_not_defaulted():
    """gas 必填：漏传在构造处就 TypeError，不会漂到 gas 检查里变成静默 skip。

    与 status_code 同规格。给默认值会让漏传的 producer 一路静默到 refinement
    检查——两侧都缺 gas 时检查直接跳过，那是假绿。
    """
    base = dict(
        condition=BoolVal(True),
        offset=BitVecVal(0, 64),
        length=BitVecVal(0, 64),
        memory=None,
        base_addr=None,
        has_return_data=BoolVal(False),
        storage=None,
        transient_storage=None,
        status_code=BitVecVal(0, 8),
    )
    with pytest.raises(TypeError):
        PathObservation(**base)


def test_gas_none_round_trips():
    """显式传 None（= 本次运行未建模 gas）仍是合法值，各访问器一致。"""
    obs = _obs()
    assert obs.gas is None
    assert obs.get("gas") is None
    assert obs["gas"] is None
    assert obs.as_dict()["gas"] is None


def test_gas_round_trips():
    g = BitVec("GasRemaining", 64)
    obs = _obs(gas=g)
    assert obs.gas is g
    assert obs["gas"] is g
    assert obs.get("gas") is g
    assert obs.as_dict()["gas"] is g
