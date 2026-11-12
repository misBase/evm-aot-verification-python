"""Discover-first parallel schedule agrees with the worklist and its consumer
rejects missing evidence."""
from dataclasses import replace

import pytest

from verification.block_parallel import verify_parallel

OPTIONS = dict(gas_check="full", gas_budget=1_000_000_000, num_inputs=0, timeout_ms=3000, node_seconds=300,
               first_pass_node_seconds=None, max_parameter_values=8, max_depth=400, max_instances=2048,
               wall_seconds=900, summaries=False)


@pytest.fixture(scope="module")
def closed():
    r = verify_parallel("tests/data/three_block", OPTIONS, workers=2)
    assert r.verified, r.message
    return r


def test_parallel_schedule_verifies_like_the_worklist(closed):
    c = closed.certificate
    assert c.entry.edges and c.specializations and len(c.nodes) == len(c.specializations)
    assert any(n["edges"] for n in c.nodes)  # real H2 edges were closed in workers


@pytest.mark.parametrize("name", ["mstore_return", "gas_sstore"])
def test_other_programs(name):
    r = verify_parallel(f"tests/data/{name}", OPTIONS, workers=2)
    assert r.verified, r.message


@pytest.mark.parametrize("missing", ["node", "edge", "entry", "identity"])
def test_consumer_rejects_missing_evidence(closed, missing):
    c = closed.certificate
    prover, initial = closed._prover, closed._initial
    if missing == "node":
        changed = replace(c, nodes=c.nodes[1:])
    elif missing == "edge":
        k = next(i for i, n in enumerate(c.nodes) if n["edges"])
        node = dict(c.nodes[k], edges=c.nodes[k]["edges"][1:])
        changed = replace(c, nodes=c.nodes[:k] + (node,) + c.nodes[k + 1:])
    elif missing == "entry":
        changed = replace(c, entry=replace(c.entry, edges=c.entry.edges[1:]))
    else:
        changed = replace(c, identity="0" * 64)
    prover._issued_program_certificate = changed
    try:
        assert not changed.valid(prover, initial)
    finally:
        prover._issued_program_certificate = c
