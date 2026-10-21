"""Static size of an x86 segment: instructions and conditional jumps between a block's entry
address and the next cutpoint address, by mnemonic.

Usage (repo root, PYTHONPATH=.): segment_jcc.py STEM PC [--base-addr ADDR]
"""
import collections
import sys
from pathlib import Path

from evm_ir.json_parser import load_ir_from_json
from evm_ir.program import EVMProgram
from tools.tag_align import build_block_alignment
from x86_64.cfg import identify_basic_blocks
from x86_64.program import X86Program

stem, pc = sys.argv[1], int(sys.argv[2])
base = int(sys.argv[sys.argv.index("--base-addr") + 1], 0) if "--base-addr" in sys.argv else 0x1000
blocks = sorted(EVMProgram(load_ir_from_json(stem + ".json")).blocks, key=lambda b: b.pc)
x86 = X86Program.from_hex(Path(stem + ".hex").read_text().strip(), base_addr=base)
alignment = build_block_alignment(blocks, x86.instructions, identify_basic_blocks(x86.instructions))
start = alignment.pc_to_addr[pc]
after = sorted(a for a in alignment.pc_to_addr.values() if a > start)
end = after[0] if after else None
ins = [i for i in x86.instructions if i.addr >= start and (end is None or i.addr < end)]
counts = collections.Counter(i.mnemonic for i in ins)
jcc = {m: n for m, n in counts.items() if m.startswith("j") and m != "jmp"}
print(f"pc {pc}: x86 {start:#x}..{end:#x}" if end else f"pc {pc}: x86 {start:#x}..end",
      "instructions", len(ins), "jcc", sum(jcc.values()), jcc, "calls", counts.get("call", 0), "ret", counts.get("ret", 0))
