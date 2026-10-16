"""tools/discovery_stats: diagnostic counts only (no proof, no certificate)."""
from evm_ir.models import EVMBlock, EvmOperator
from tools.discovery_stats import analyze, recursive
from verification.block_specialization import BlockSpecialization


def _block(pc, kinds):
    b = EVMBlock(pc, 0, 0, 1024, 0, True, False, False)
    b.operations = [EvmOperator(k, pc + i) for i, k in enumerate(["TAG", *kinds])]
    return b


def test_recursive_means_a_repeated_return_tag():
    tags = {0x20, 0x30}
    assert not recursive(BlockSpecialization(1, 4, None, None, ((0, 0x20), (1, 7), (2, 0x30))), tags)
    assert recursive(BlockSpecialization(1, 4, None, None, ((0, 0x20), (1, 7), (3, 0x20))), tags)
    assert not recursive(BlockSpecialization(1, 4, None, None, ((0, 7), (1, 7))), tags)  # data, not tags


def test_analyze_counts_dimension_projections():
    blocks = [_block(1, ["POP", "STOP"]), _block(2, ["JUMP"])]
    specs = [
        BlockSpecialization(1, 3, None, None, ((0, 5), (2, 0x20))),
        BlockSpecialization(1, 3, None, None, ((0, 6), (2, 0x20))),
        BlockSpecialization(1, 4, 96, 128, ((3, 0x20),)),
        BlockSpecialization(2, 2, None, None, ((0, 0x20),)),
    ]
    stats = analyze(specs, blocks, {0x20})
    d = stats["distinct"]
    assert stats["instances"] == d["full"] == 4 and d["pc"] == 2
    assert d["no_constants"] == 3 and d["no_extra_constants"] == 3 and d["pc_depth"] == 3
    # block 1 is terminal (STOP) and its POP discards slot 0: one context per depth/parameters
    assert d["instances_at_terminal_blocks"] == 3 and d["terminal_projected"] == 3
    assert stats["top_blocks"][0]["pc"] == 1 and stats["top_blocks"][0]["instances"] == 3
    assert stats["return_tags_per_instance"] == {1: 4}
