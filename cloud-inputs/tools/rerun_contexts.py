"""Re-prove only the unfinished entries of a finished report, at full budget.

Usage (cwd = a frozen snapshot): STEM REPORT.json OUT.jsonl WORKERS [SECONDS]
Discovers the frozen instance set and proof groups as block_parallel does
(constant-insensitive), takes every report entry that is not proved (proved
with an open H2 edge counts as not proved; split groups are covered by their
contexts' own entries) and runs prove_instance on it with its contexts.
Rows are appended to OUT.jsonl as they finish; finished specs are skipped on restart.
"""
import json
import multiprocessing
import os
import sys
import time
from concurrent.futures import FIRST_COMPLETED, ProcessPoolExecutor, wait
from pathlib import Path
from time import monotonic

sys.path.insert(0, ".")
from verification import block_parallel as bp  # noqa: E402
from verification.block_program import BlockProgramResult  # noqa: E402

OPTIONS = dict(gas_check="full", gas_budget=1_000_000_000, num_inputs=0, timeout_ms=30000, node_seconds=3600,
               first_pass_node_seconds=None, max_parameter_values=32, max_depth=400, max_instances=8192,
               wall_seconds=36 * 3600, summaries=True)


def main():
    stem, report, out, workers = sys.argv[1], Path(sys.argv[2]), Path(sys.argv[3]), int(sys.argv[4])
    seconds = float(sys.argv[5]) if len(sys.argv) > 5 else 3600
    only = {int(p) for p in os.environ.get("ONLY_PCS", "").split(",") if p}  # restrict to these blocks
    entries = [i for pc, b in json.loads(report.read_text())["diagnostics"].items() for i in b["instances"]
               if i["status"] != "split" and (i["status"] != "proved" or i["reasons"])
               and (not only or int(pc) in only)]
    grep = os.environ.get("SPEC_GREP")  # keep only entries whose spec text contains this
    if grep:
        entries = [i for i in entries if grep in i["spec"]]
    sample = os.environ.get("SAMPLE_PROVED")  # "N,SEED": regression sample of complete entries instead
    if sample:
        import random
        n, seed = (int(x) for x in sample.split(","))
        proved = [i for b in json.loads(report.read_text())["diagnostics"].values() for i in b["instances"]
                  if i["status"] == "proved" and not i["reasons"] and (i["seconds"] or 0) > 20]
        entries = random.Random(seed).sample(proved, n)
    evm, x86, initial, verifier = bp.build_inputs(stem, OPTIONS)
    setup = verifier._setup(evm, x86, initial, BlockProgramResult(), monotonic(), [])
    ordered, defects = bp.discover(verifier, setup, lambda: None)
    groups = bp.proof_groups(ordered, setup.evm, True)
    by_text = {repr(s): s for s in list(ordered) + list(groups)}
    todo = []
    for entry in entries:
        spec = by_text[entry["spec"]]
        contexts = groups[spec] if spec in groups and len(groups[spec]) == entry["contexts"] else (spec,)
        assert spec in groups or spec in ordered, entry["spec"]
        todo.append((spec, contexts, entry["reasons"][:1]))
    done = set()
    if out.exists():
        done = {json.loads(line)["spec"] for line in out.read_text().splitlines() if line.strip()}
    todo = [t for t in todo if repr(t[0]) not in done]
    per_pc = int(os.environ.get("LIMIT_PER_PC", "0"))  # sample: at most this many entries per block
    if per_pc:
        kept, count = [], {}
        for t in todo:
            count[t[0].pc] = count.get(t[0].pc, 0) + 1
            if count[t[0].pc] <= per_pc:
                kept.append(t)
        todo = kept
    # Worker errors and open H2 edges first: never had their full budget.
    todo.sort(key=lambda t: not any("worker" in r or "H2" in r for r in t[2]))
    print(f"discovery defects={len(defects)} entries={len(entries)} todo={len(todo)}", flush=True)
    deadline = time.time() + OPTIONS["wall_seconds"]
    pool = ProcessPoolExecutor(workers, mp_context=multiprocessing.get_context("spawn"),
                               initializer=bp._init_worker, initargs=(stem, OPTIONS, ordered, os.getpid(), int(os.environ.get("PAIR_WORKERS", "1"))))
    running = {pool.submit(bp.prove_instance, spec, seconds, deadline, contexts): (spec, contexts)
               for spec, contexts, _ in todo}
    with out.open("a") as handle:
        while running:
            finished, _ = wait(running, timeout=60, return_when=FIRST_COMPLETED)
            for future in finished:
                spec, contexts = running.pop(future)
                try:
                    node = future.result()
                    row = dict(spec=repr(spec), contexts=len(contexts), status=bp.final_status(node),
                               seconds=round(node["seconds"], 1), reasons=list(node["reasons"])[:3],
                               failed=node["failed"][:3])
                except Exception as exc:
                    row = dict(spec=repr(spec), contexts=len(contexts), status="error", seconds=0,
                               reasons=[f"worker: {type(exc).__name__}: {exc}"], failed=[])
                handle.write(json.dumps(row) + "\n")
                handle.flush()
                print(row["status"], row["spec"][:80], row["seconds"], flush=True)
    for process in list(getattr(pool, "_processes", {}).values()):
        process.kill()
    pool.shutdown(wait=False, cancel_futures=True)
    print("done", flush=True)


if __name__ == "__main__":
    main()
