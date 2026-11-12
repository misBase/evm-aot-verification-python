"""Cache scheduling metadata only; seeded answers do not prove SMT facts."""
import pytest

from verification import proof_cache


@pytest.fixture(autouse=True)
def private_cache(tmp_path, monkeypatch):
    monkeypatch.setenv('BLOCK_PROOF_CACHE', str(tmp_path / 'private.sqlite3'))
    monkeypatch.setattr(proof_cache, '_LOCAL_UNKNOWN', {'owner': None, 'budgets': {}})
    monkeypatch.setattr(proof_cache, '_CONNECTIONS', {})
    yield
    for connection in proof_cache._CONNECTIONS.values():
        connection.close()


@pytest.mark.parametrize('seen', [False, True])
@pytest.mark.parametrize('budget', [0, -1])
def test_nonpositive_unknown_is_not_consumed(seen, budget):
    keys = ('seeded-query',)
    if seen:
        proof_cache.record_answer(keys, 'unknown', 5000)
    assert proof_cache.cached_answer(keys, budget) is None


def test_positive_own_budget_still_reused():
    keys = ('seeded-query',)
    proof_cache.record_answer(keys, 'unknown', 5000)
    assert proof_cache.cached_answer(keys, 5000) == 'unknown'
    assert proof_cache.cached_answer(keys, 3000) == 'unknown'
    assert proof_cache.cached_answer(keys, 5001) is None


@pytest.mark.parametrize('answer', ['sat', 'unsat'])
def test_decided_metadata_remains_first(answer):
    keys = ('seeded-decided-query',)
    proof_cache.record_answer(keys, answer, 1)
    for budget in (0, -1, 100):
        assert proof_cache.cached_answer(keys, budget) == answer


@pytest.mark.parametrize('budget', [0, -1, 100])
def test_none_keys_are_not_unknown(budget):
    assert proof_cache.cached_answer(None, budget) is None


def test_foreign_larger_budget_not_adopted():
    keys = ('seeded-query',)
    proof_cache.store(keys, {'unknown': 60000}, replace=True)
    assert proof_cache.cached_answer(keys, 30000) is None
    proof_cache.record_answer(keys, 'unknown', 5000)
    assert proof_cache.cached_answer(keys, 30000) is None
