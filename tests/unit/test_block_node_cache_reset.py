"""3D: term-keyed caches are dropped between nodes so long-lived workers keep bounded memory."""
from z3 import BitVec

import common.store_forwarding as sf
import verification.block_equivalence as be
from verification.block_equivalence import BlockEquivalenceProver
from verification.block_parallel import reset_node_caches


def _populate():
    sf.linearize_address(BitVec("nc_a", 64) + 8)
    assert sf._MEMO


def test_reset_node_caches_drops_memo_and_lemma_cache():
    prover = BlockEquivalenceProver([], [], {})
    _populate()
    prover._lemma_cache[(1, 2)] = [((), [], ())]
    reset_node_caches(prover)
    assert not sf._MEMO and not prover._lemma_cache


def test_pair_worker_clears_memo_only_when_the_node_changes(monkeypatch):
    monkeypatch.setattr(be, "_WORKER_PROVER", {})
    be._worker_prover("node-a", 1000, None)
    _populate()
    be._worker_prover("node-a", 1000, None)
    assert sf._MEMO  # same node: sibling pairs keep sharing the memo
    be._worker_prover("node-b", 1000, None)
    assert not sf._MEMO
