from pathlib import Path

from evm_ir.json_parser import load_ir_from_json


FIXTURE = Path(__file__).resolve().parents[1] / "data" / "perf_erc20_lite.json"


def test_perf_erc20_lite_fixture_shape():
    result = load_ir_from_json(str(FIXTURE))
    blocks = result.blocks
    ops = [op for block in blocks for op in block.operations]

    assert len(blocks) == 13
    assert len(ops) == 144
    assert {160, 190, 230, 300}.issubset({block.pc for block in blocks})


def test_perf_erc20_lite_fixture_has_realistic_erc20_paths():
    result = load_ir_from_json(str(FIXTURE))
    ops = [op for block in result.blocks for op in block.operations]

    function_selectors = {
        404098525,   # totalSupply()
        1889567281,  # balanceOf(address)
        2835717307,  # transfer(address,uint256)
        157198259,   # approve(address,uint256)
    }
    immediates = {op.immediate for op in ops if op.immediate is not None}
    op_kinds = {op.kind for op in ops}

    assert function_selectors.issubset(immediates)
    assert {"CALLDATALOAD", "SHA3", "SLOAD", "SSTORE", "RETURN", "REVERT"}.issubset(op_kinds)
