"""存储（Storage）等价检查的专项回归测试。"""

from z3 import And, Array, BitVec, BitVecSort, BitVecVal, Bool, Concat, If, Not, Store, UGE, unknown

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


def test_storage_path_aware_fast_path_proves_store_key_expr_equality():
    checker = RefinementChecker(timeout_ms=1000)
    storage = _storage_array("Storage_path_key_expr")
    calldata_size = BitVec("CallDataSize", 64)
    derived_zero_key = Concat(BitVecVal(0, 192), calldata_size - calldata_size)
    written_with_expr_key = Store(
        storage,
        derived_zero_key,
        BitVecVal(1, 256),
    )
    written_with_concrete_key = Store(
        storage,
        BitVecVal(0, 256),
        BitVecVal(1, 256),
    )

    verified, msg = checker._check_storage_equivalence(
        written_with_expr_key,
        written_with_concrete_key,
        path_condition=UGE(calldata_size, BitVecVal(68, 64)),
    )

    assert verified
    assert msg == "Storage equivalent (path-aware structural)"


def test_storage_calldatasize_partition_proves_noop_store_under_path():
    checker = RefinementChecker(timeout_ms=1000)
    storage = _storage_array("Storage_noop_store")
    calldata_size = BitVec("CallDataSize", 64)
    key = BitVec("storage_noop_key", 256)
    guard = Bool("storage_noop_guard")
    maybe_noop = Store(
        storage,
        key,
        If(guard, storage[key], BitVecVal(1, 256)),
    )

    verified, msg = checker._storage._check_storage_equivalence_by_calldatasize_partition(
        checker._ctx.solver,
        storage,
        maybe_noop,
        deadline=None,
        path_condition=And(guard, calldata_size == BitVecVal(4, 64)),
        context="",
        logs=[],
        ctx=None,
    )

    assert verified
    assert msg == "Storage equivalent (calldatasize partition)"


def test_calldatasize_partition_shape_is_exhaustive_tail_split():
    checker = RefinementChecker(timeout_ms=1000)

    partitions = list(checker._storage._calldatasize_partitions(ctx=None))

    assert len(partitions) == 69
    assert partitions[0][0] == "size=0"
    assert partitions[67][0] == "size=67"
    assert partitions[68][0] == "size>=68"


def test_calldatasize_partition_fast_path_runs_after_exact_substitution(monkeypatch):
    checker = RefinementChecker(timeout_ms=1000)
    storage = _storage_array("Storage_partition_exact_fast")
    calldata_size = BitVec("CallDataSize", 64)
    key_via_size = Concat(BitVecVal(0, 192), calldata_size - calldata_size)
    evm_storage = Store(storage, key_via_size, BitVecVal(1, 256))
    x86_storage = Store(storage, BitVecVal(0, 256), BitVecVal(1, 256))

    def mismatch_query_should_not_run(*_args, **_kwargs):
        raise AssertionError("exact partitions should use the structural fast path")

    monkeypatch.setattr(
        checker._storage,
        "_array_mismatch_query_with_solver",
        mismatch_query_should_not_run,
    )

    verified, msg = checker._storage._check_storage_equivalence_by_calldatasize_partition(
        checker._ctx.solver,
        evm_storage,
        x86_storage,
        deadline=None,
        path_condition=calldata_size == BitVecVal(0, 64),
        context="",
        logs=[],
        ctx=None,
    )

    assert verified
    assert msg == "Storage equivalent (calldatasize partition)"


def test_calldatasize_partition_coalesces_remaining_exact_infeasible_range(monkeypatch):
    checker = RefinementChecker(timeout_ms=1000)
    storage = _storage_array("Storage_partition_range")
    calldata_size = BitVec("CallDataSize", 64)
    evm_storage = If(
        UGE(calldata_size, BitVecVal(37, 64)),
        Store(storage, BitVecVal(1, 256), BitVecVal(2, 256)),
        storage,
    )
    x86_storage = storage
    rescue_labels = []

    def fake_unsat_probe(*_args, log_label: str, **_kwargs):
        rescue_labels.append(log_label)
        return "size=37..67" in log_label or "size>=68" in log_label

    def mismatch_query_should_not_run(*_args, **_kwargs):
        raise AssertionError("coalesced infeasible ranges should skip mismatch queries")

    monkeypatch.setattr(
        checker._storage,
        "_condition_unsat_probe_with_solver",
        fake_unsat_probe,
    )
    monkeypatch.setattr(
        checker._storage,
        "_array_mismatch_query_with_solver",
        mismatch_query_should_not_run,
    )

    verified, msg = checker._storage._check_storage_equivalence_by_calldatasize_partition(
        checker._ctx.solver,
        evm_storage,
        x86_storage,
        deadline=None,
        path_condition=calldata_size == BitVecVal(0, 64),
        context="",
        logs=[],
        ctx=None,
    )

    assert verified
    assert msg == "Storage equivalent (calldatasize partition)"
    assert "Storage calldata-size feasibility split size=37..67" in rescue_labels
    assert "Storage calldata-size feasibility split size>=68" in rescue_labels


def test_storage_quick_unknown_uses_infeasible_path_rescue(monkeypatch):
    checker = RefinementChecker(timeout_ms=5000)
    storage_a = _storage_array("Storage_rescue_a")
    storage_b = _storage_array("Storage_rescue_b")
    guard = Bool("storage_rescue_guard")
    calldata_size = BitVec("CallDataSize", 64)
    path_condition = And(guard, Not(guard), calldata_size == BitVecVal(4, 64))
    query_keys = []

    def quick_unknown(*_args, key_name: str, **_kwargs):
        query_keys.append(key_name)
        return unknown, 0.0

    monkeypatch.setattr(
        checker._storage,
        "_array_mismatch_query_with_solver",
        quick_unknown,
    )

    verified, msg = checker._check_storage_equivalence(
        storage_a,
        storage_b,
        path_condition=path_condition,
    )

    assert verified
    assert msg == "Storage equivalent (infeasible path)"
    assert query_keys == ["storage_check_key_quick"]
