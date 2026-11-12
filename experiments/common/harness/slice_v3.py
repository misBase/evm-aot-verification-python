"""V3 (block lockstep) on one B-fn slice: prove every block the slice reaches.

Run from the snapshot directory:
  python slice_v3.py REACH.json STEM WORKDIR WALL_SECONDS
Runs the production subset tool (cloud-inputs/n5/tools/h2_batch.py: whole-contract
discovery, node pool, local theorems and H2 for the selected PCs) on the blocks in
REACH.json, then writes a worker JSON. A completed subset is not a program
certificate (no H0); it is the slice's lockstep proof work.
"""
import json
import os
import subprocess
import sys
from pathlib import Path


def main():
    reach, stem, work, wall = sys.argv[1], sys.argv[2], Path(sys.argv[3]), float(sys.argv[4])
    blocks = json.loads(Path(reach).read_text())["blocks"]
    work.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, PYTHONPATH=os.getcwd(), BLOCK_PROOF_CACHE=str(work / "cache.sqlite3"))
    subprocess.run([sys.executable, "cloud-inputs/n5/tools/h2_batch.py", stem,
                    "--pcs", ",".join(map(str, blocks)), "--output-dir", str(work), "--workers", "4",
                    "--node-seconds", "600", "--first-pass-node-seconds", "300",
                    "--node-memory-mb", "2000", "--max-depth", "400", "--wall-seconds", str(wall)],
                   env=env, check=False)
    report = json.loads((work / "partial.json").read_text())
    instances = [i for b in report["diagnostics"].values() for i in b["instances"]]
    visited = [b for b in report["diagnostics"].values() if b["instances"]]  # discovery may find no instance
    blocks_proved = sum(b["status"] == "proved" for b in visited)
    done = bool(visited) and blocks_proved == len(visited)
    Path(os.environ["PAPER_WORKER_OUT"]).write_text(json.dumps(dict(
        kind="lockstep-slice", target=stem, config="V3", verified=done,
        result="VERIFIED" if done else "UNKNOWN", scope="local theorems + H2 of the slice's blocks; no H0",
        blocks=len(blocks), blocks_with_instances=len(visited), blocks_proved=blocks_proved, instances=len(instances),
        proved_instances=sum(i["status"] == "proved" for i in instances),
        timings=report.get("timings"), message=report.get("status"))))


if __name__ == "__main__":
    main()
