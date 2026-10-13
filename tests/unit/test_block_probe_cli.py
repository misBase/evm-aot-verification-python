"""Directed probe CLI. Local node results only; nothing here claims a program certificate."""
import json
from types import SimpleNamespace

import pytest

from tools.probe_block_obligations import BANNER, main, parse_nodes

STEM = "tests/data/muti_block"


def test_null_memory_and_empty_constants_stay_symbolic():
    spec, = parse_nodes([{"pc": 120, "stack_depth": 0, "memory_size": None,
                          "free_memory_pointer": None}])
    assert spec.memory_size is None and spec.free_memory_pointer is None
    assert spec.stack_constants == ()
    assert parse_nodes([{"pc": 5822, "stack_depth": 6, "memory_size": 96,
                         "free_memory_pointer": 128,
                         "stack_constants": [[2, 2112]]}])[0].stack_constants == ((2, 2112),)


@pytest.mark.parametrize("raw", [
    {"pc": 0, "stack_depth": 0},                                  # not a list
    [],                                                           # empty batch
    [{"pc": 0, "stack_depth": 1, "stack_constants": None}],
    [{"pc": 0, "stack_depth": 1, "stack_constants": ""}],
    [{"pc": 0, "stack_depth": 1, "stack_constants": [[False, 1]]}],
    [{"pc": 0, "stack_depth": 1, "stack_constants": [[0, True]]}],
    [{"pc": 0}],                                                  # missing stack_depth
    [{"pc": 0, "stack_depth": 0, "msize": 96}],                   # unknown key
    [{"pc": "0", "stack_depth": 0}],                              # pc not an int
    [{"pc": 0, "stack_depth": True}],                             # bool is not an int here
    [{"pc": 0, "stack_depth": 0, "memory_size": "96"}],           # not int-or-null
    [{"pc": 0, "stack_depth": 0, "stack_constants": [[1]]}],      # malformed pair
    [{"pc": 0, "stack_depth": 0, "memory_size": 97}],             # unaligned, from the dataclass
    [{"pc": 0, "stack_depth": 0, "stack_constants": [[0, 1]]}],   # index outside the live stack
])
def test_malformed_input_is_rejected(raw):
    with pytest.raises(ValueError):
        parse_nodes(raw)


def test_real_fixture_node_is_proved_locally(tmp_path):
    out = tmp_path / "probe.json"
    nodes = tmp_path / "nodes.json"
    nodes.write_text(json.dumps([{"pc": 120, "stack_depth": 0, "memory_size": 96,
                                  "free_memory_pointer": 128}]))
    code = main([STEM, str(nodes), "--output", str(out), "--no-summaries",
                 "--timeout-ms", "10000", "--formula-dir", str(tmp_path / "formulas")])
    report = json.loads(out.read_text())
    assert code == 0 and report["locally_proved"] == 1
    assert report["scope"] == "block-local" and report["disclaimer"] == BANNER
    node, = report["nodes"]
    assert node["status"] == "proved" and not node["failed_obligations"]
    assert node["evm_paths"] > 0 and node["x86_paths"] > 0 and node["queries"] > 0


def test_null_parameters_reach_the_prover_and_checkpoint(tmp_path, monkeypatch):
    seen = []
    stub = SimpleNamespace(proved=False, obligations=(), reasons=("stub",), elapsed_seconds=0.5,
                           queries=1, evm_paths=1, x86_paths=1, paired_transitions=0,
                           terminals_proved=0, theorem=None)
    monkeypatch.setattr("tools.probe_block_obligations.build_prover",
                        lambda *a, **k: SimpleNamespace(prove=lambda s: (seen.append(s), stub)[1]))
    nodes = tmp_path / "nodes.json"
    out = tmp_path / "probe.json"
    nodes.write_text(json.dumps([{"pc": 779, "stack_depth": 3, "memory_size": None,
                                  "free_memory_pointer": None}]))
    assert main([STEM, str(nodes), "--output", str(out)]) == 1
    assert seen[0].memory_size is None and seen[0].free_memory_pointer is None
    node, = json.loads(out.read_text())["nodes"]
    assert node["spec"]["memory_size"] is None and node["status"] == "inconclusive"
    assert node["reasons"] == ["stub"]


@pytest.mark.parametrize("budget", ["nan", "inf", "-inf"])
def test_nonfinite_budget_is_rejected(tmp_path, budget):
    with pytest.raises(SystemExit):
        main([STEM, "unused.json", "--output", str(tmp_path / "unused.json"),
              "--node-seconds=" + budget])
