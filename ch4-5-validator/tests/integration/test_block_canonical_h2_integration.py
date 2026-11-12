"""High-fanout H2 regression against the complete frozen muti_block fixture.

The existing full-program acceptance test remains
 test_block_constant_insensitive::test_muti_block_verifies_with_fewer_proofs.
This focused regression retains all its discovered targets and one entire
98-edge proof group, using exactly its original local/H2/global budgets.
"""
from pathlib import Path
import runpy
from time import monotonic, time

import pytest

from verification import block_parallel as bp
from verification.block_program import BlockProgramResult
from verification.block_specialization import BlockSpecialization


@pytest.mark.slow
def test_muti_block_all_original_cutpoint_edges_close():
    options = dict(runpy.run_path(str(Path(__file__).with_name("test_block_constant_insensitive.py")))["ON"])
    assert (options["node_seconds"], options["wall_seconds"]) == (300, 900)
    start = monotonic()
    until = time() + options["wall_seconds"]
    stem = "tests/data/muti_block"
    evm, x86, initial, verifier = bp.build_inputs(stem, options)
    setup = verifier._setup(evm, x86, initial, BlockProgramResult(), start, [])

    def budget():
        assert time() < until, "original integration global wall exhausted"

    ordered, defects = bp.discover(verifier, setup, budget)
    groups = bp.proof_groups(ordered, setup.evm, True)
    assert len(ordered) == 47 and len(groups) == 46 and not defects
    spec = BlockSpecialization(385, 1, 96, 96)
    bp.load_worker(stem, options, ordered)
    node = bp.prove_instance(spec, options["node_seconds"], until, groups[spec])
    assert bp.final_status(node) == "proved", node["reasons"]
    assert node["theorem"].complete
    assert len(node["theorem"].cutpoint_manifest) == len(node["expected"]) == 98
    assert len(node["edges"]) == 98 * len(groups[spec])
    for context in groups[spec]:
        edges = [edge for edge in node["edges"] if edge.source == context]
        assert {edge.pair for edge in edges} == set(node["expected"])
        assert all(edge.obligation.proved and edge.targets == tuple(s for s in ordered if s.pc == edge.target_pc)
                   for edge in edges)
