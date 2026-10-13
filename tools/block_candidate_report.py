"""Report candidate depth/memory domains; this tool issues no proof certificate."""
from __future__ import annotations
import argparse
from dataclasses import asdict
from hashlib import sha256
import json
from pathlib import Path
from time import monotonic

from evm_ir.json_parser import load_ir_from_json
from evm_ir.program import EVMProgram
from tools.call_provenance import build_call_provenance
from tools.msize_absint import TOP, analyze_memory_size


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("ir", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    started = monotonic()
    blocks = EVMProgram(load_ir_from_json(str(args.ir))).blocks
    provenance = build_call_provenance(blocks)
    memory = analyze_memory_size(blocks)
    mtop = sorted(pc for pc, value in memory.msize.items() if value is TOP)
    ftop = sorted(pc for pc, value in memory.fmp.items() if value is TOP)
    report = dict(kind="untrusted_candidate_analysis", proof_status="not_checked",
        policy="These candidates establish no reachability, H0/H2 closure, or program equivalence.",
        input=str(args.ir), input_sha256=sha256(args.ir.read_bytes()).hexdigest(),
        analysis_sources_sha256=sha256(b"".join(p.read_bytes() for p in (
            Path("tools/call_provenance.py"), Path("tools/msize_absint.py")))).hexdigest(),
        total_blocks=len(blocks), depth_instances=sum(map(len, provenance.depth_classes.values())),
        msize_top_pcs=mtop, fmp_top_pcs=ftop,
        msize_top_count=len(mtop), fmp_top_count=len(ftop),
        elapsed_seconds=monotonic()-started,
        blocks={b.pc: dict(depth_candidates=sorted(provenance.depth_classes.get(b.pc, ())),
            msize_candidate=("TOP" if memory.msize.get(b.pc) is TOP else
                             sorted(memory.msize[b.pc]) if b.pc in memory.msize else "not_visited_by_analysis"),
            fmp_candidate=("TOP" if memory.fmp.get(b.pc) is TOP else
                           memory.fmp.get(b.pc, "not_visited_by_analysis")),
            top_sources=[asdict(s) for s in memory.top_sources.get(b.pc, ())]) for b in blocks})
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k not in ("blocks", "msize_top_pcs", "fmp_top_pcs")}, ensure_ascii=False))


if __name__ == "__main__":
    main()
