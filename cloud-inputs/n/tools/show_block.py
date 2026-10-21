"""Print the EVM IR of the blocks at the given pcs (and the following blocks up to --follow N).

Usage (repo root, PYTHONPATH=.): show_block.py STEM PC [PC ...] [--follow N]
"""
import sys

from evm_ir.json_parser import load_ir_from_json
from evm_ir.program import EVMProgram

argv = sys.argv[1:]
follow = int(argv[argv.index("--follow") + 1]) if "--follow" in argv else 0
argv = [a for n, a in enumerate(argv) if a != "--follow" and (n == 0 or argv[n - 1] != "--follow")]
blocks = sorted(EVMProgram(load_ir_from_json(argv[0] + ".json")).blocks, key=lambda b: b.pc)
pcs = [b.pc for b in blocks]
for pc in map(int, argv[1:]):
    start = pcs.index(pc)
    for block in blocks[start:start + 1 + follow]:
        print(f"== block {block.pc}")
        for ins in block.operations:
            print("  ", ins.pc, ins.kind, "" if ins.immediate is None else hex(ins.immediate), "" if ins.param is None else ins.param, ins.immediate_set or "")
