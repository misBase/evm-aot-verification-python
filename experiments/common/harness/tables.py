"""Print the report tables from a results directory (CPU seconds, or status).

  python tables.py RESULTS_DIR
"""
import json
import sys
from collections import defaultdict
from pathlib import Path

out = Path(sys.argv[1])
cells = defaultdict(dict)  # (family, target) -> config -> text
for path in sorted(out.glob("*.json")):
    name = path.name[:-5]
    if name.startswith("superseded__") or name.endswith((".worker", ".reach")) or "__" not in name or name == "matrix.process":
        continue
    family, target, config = name.split("__")
    record = json.loads(path.read_text())
    status = record.get("result")
    cpu = record.get("cpu_seconds")
    text = f"{cpu:.1f}" if status in ("VERIFIED", "BOUNDED", "VERIFIED-RC0") and cpu is not None else status
    if status == "BOUNDED":
        text += "b"
    if record.get("blocks_with_instances") is not None and status != "VERIFIED":
        text += f" ({record.get('blocks_proved')}/{record.get('blocks_with_instances')})"
    cells[(family, target)][config] = text


def table(family, configs, targets=None):
    rows = sorted(t for f, t in cells if f == family and (targets is None or t in targets))
    print(f"\n## {family}")
    print("| target | " + " | ".join(configs) + " |")
    print("|---|" + "---|" * len(configs))
    for target in rows:
        row = cells[(family, target)]
        if not any(c in row for c in configs):
            continue
        print(f"| {target} | " + " | ".join(row.get(c, "-") for c in configs) + " |")


table("prog", ["V0", "V1", "V2", "V2+B5", "V3", "V3-G0"])
table("prog", ["V2", "+B1", "+B2", "+B3", "+B4", "+B5", "-A2", "V2-B1", "V2-B2", "V2-B3", "V2-B4", "V2+B5"])
table("fn", ["V1", "V2", "V2L", "V3", "reach"])
table("fn", ["V2", "V2-B1", "V2-B3", "V2-B4"])
table("whole", ["V2", "V3", "V3-L1", "V3-L2", "V3-L5"])
