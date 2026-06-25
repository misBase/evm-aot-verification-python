"""阶段0 gas 一致性:PathObservation 携带 gas 字段。"""

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
    )
    base.update(overrides)
    return PathObservation(**base)


def test_gas_in_observation_keys():
    assert "gas" in OBSERVATION_KEYS


def test_gas_defaults_none_for_legacy_construction():
    """不传 gas 的旧式构造 → gas 为 None（gas 检查会被跳过，不报错）。"""
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
