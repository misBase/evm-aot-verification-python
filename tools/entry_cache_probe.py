"""What BLOCK_PROOF_CACHE holds for a node's entry_nonempty query (diagnostics only).

Usage: BLOCK_PROOF_CACHE=/path/cache.sqlite PYTHONPATH=. poetry run python tools/entry_cache_probe.py \
           PC:DEPTH:MSIZE:FMP [...]        (MSIZE / FMP: an integer or None)

Prints, per node, the cached record of the simplified entry premise (the query
BlockEquivalenceProver._check solves for entry_nonempty) and its answer in a fresh
solver. A record {"unknown": N} with a fresh "sat" is a timeout cached under load;
before the trust_unknown fix every later node whose entry premise is alpha-equal
(any pc/depth with the same MSIZE/FMP) failed at once with "entry predicate empty
or unknown". Reads the cache only.
"""
import sys

from z3 import And, simplify

from verification import proof_cache
from verification.block_equivalence import _solve_query
from verification.block_relation import BlockRelationSchema
from verification.block_specialization import BlockSpecialization


def entry_premise(spec):
    context = BlockRelationSchema().build_havoc(
        prefix=f"blk{spec.pc}_{spec.stack_depth}_{spec.memory_size}_{spec.free_memory_pointer}",
        host_gas_uf_enabled=True, assume_calldata_offset_no_overflow=False,
        abstract_calldataload_words=False, **spec.as_havoc_kwargs())
    return And(*(context.state.assumptions or []))


def main(argv):
    if not proof_cache.enabled():
        print("BLOCK_PROOF_CACHE is not set")
        return 2
    for item in argv:
        pc, depth, msize, fmp = (None if v == "None" else int(v) for v in item.split(":"))
        query = simplify(entry_premise(BlockSpecialization(pc, depth, msize, fmp, ())))
        cached = proof_cache.lookup(proof_cache.query_key("check", query))
        print(item, "cached:", cached, "fresh:", _solve_query(query, 30000))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
