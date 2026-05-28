"""Storage-specific refinement checker regressions."""

from z3 import Array, BitVecSort, BitVecVal, Bool, If, Not, Store

from verification.refinement_checker import RefinementChecker


def _storage_array(name: str):
    return Array(name, BitVecSort(256), BitVecSort(256))


def test_storage_path_aware_fast_path_resolves_merged_if():
    checker = RefinementChecker(timeout_ms=1000)
    storage = _storage_array("Storage_path_fast")
    cond = Bool("storage_path_cond")
    written = Store(storage, BitVecVal(0, 256), BitVecVal(1, 256))
    merged = If(cond, written, storage)

    verified, msg = checker._check_storage_equivalence(
        written,
        merged,
        path_condition=cond,
    )

    assert verified
    assert msg == "Storage equivalent (path-aware structural)"


def test_storage_path_aware_fast_path_does_not_hide_wrong_branch():
    checker = RefinementChecker(timeout_ms=1000)
    storage = _storage_array("Storage_path_wrong")
    cond = Bool("storage_wrong_cond")
    written = Store(storage, BitVecVal(0, 256), BitVecVal(1, 256))
    merged = If(cond, written, storage)

    verified, msg = checker._check_storage_equivalence(
        written,
        merged,
        path_condition=Not(cond),
    )

    assert not verified
    assert "storage differs" in msg


def test_calldatasize_partition_shape_is_exhaustive_tail_split():
    checker = RefinementChecker(timeout_ms=1000)

    partitions = list(checker._storage._calldatasize_partitions(ctx=None))

    assert len(partitions) == 69
    assert partitions[0][0] == "size=0"
    assert partitions[67][0] == "size=67"
    assert partitions[68][0] == "size>=68"
