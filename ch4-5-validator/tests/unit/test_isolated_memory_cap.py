"""The isolated child's memory cap: configurable, never above half of the node's free budget."""
import common.isolated_sat as isolated
import common.node_monitor as monitor


def test_default_cap_is_one_gib(monkeypatch):
    monkeypatch.setattr(monitor, "memory_headroom_mb", lambda: None)
    assert isolated.ISOLATED_MEMORY_MB == 1024 and isolated._child_memory_mb() == 1024


def test_raised_cap_still_bounded_by_node_headroom(monkeypatch):
    monkeypatch.setattr(isolated, "ISOLATED_MEMORY_MB", 4096)
    monkeypatch.setattr(monitor, "memory_headroom_mb", lambda: None)
    assert isolated._child_memory_mb() == 4096
    monkeypatch.setattr(monitor, "memory_headroom_mb", lambda: 3000)
    assert isolated._child_memory_mb() == 1500
    monkeypatch.setattr(monitor, "memory_headroom_mb", lambda: 0)
    assert isolated._child_memory_mb() == 1
