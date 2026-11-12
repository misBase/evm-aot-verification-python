"""Job names to repeat: the repetition rule of the paper (cases whose first wall time exceeds 300 s run only once).

Usage: python repeat_names.py ROUND1_DIR [ROUND1_DIR ...] > names.txt
"""
import json
import sys
from pathlib import Path

THRESHOLD_SECONDS = 300

for directory in sys.argv[1:]:
    for path in sorted(Path(directory).glob("*.json")):
        if path.name.endswith(".worker.json") or path.name == "matrix.process.json":
            continue
        record = json.loads(path.read_text())
        wall = record.get("wall_seconds")
        if isinstance(wall, (int, float)) and wall < THRESHOLD_SECONDS:
            print(path.stem.replace("__", "/"))
