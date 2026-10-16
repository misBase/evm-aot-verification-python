"""Discovery-only instance statistics (no proof, no certificate).

Runs the discover-first discovery phase (verification/block_parallel.discover)
with the same inputs as tools/verify_block_lockstep and reports how the frozen
instance set splits over blocks and dimensions (stack depth, (MSize, fmp)
parameters, return-tag / other stack constants). A failure is reported with its
full traceback together with the partial set discovered so far.

Usage: poetry run python -m tools.discovery_stats <stem> [--max-instances N]
       [--max-parameter-values 32] [--output stats.json] [--specs specs.txt]
       poetry run python -m tools.discovery_stats <stem> --from-specs specs.txt
"""
from __future__ import annotations
import argparse
from collections import Counter
import json
from pathlib import Path
import time
import traceback


def analyze(specs, blocks, return_tags, top=25):
    """Plain-data statistics of `specs` (BlockSpecialization) over `blocks`."""
    from verification.block_parallel import proof_groups
    specs = list(specs)
    per_pc = Counter(s.pc for s in specs)

    def returns(s):
        return tuple(c for c in s.stack_constants if c[1] in return_tags)

    def extras(s):
        return tuple(c for c in s.stack_constants if c[1] not in return_tags)

    # Distinct keys under projections that forget one dimension: a first-order
    # estimate of the instance count a merge of that dimension would leave
    # (the changed proposals downstream of a merged context are not modeled).
    projections = {
        "full": lambda s: s,
        "no_parameters": lambda s: (s.pc, s.stack_depth, s.stack_constants),
        "no_constants": lambda s: (s.pc, s.stack_depth, s.memory_size, s.free_memory_pointer),
        "no_extra_constants": lambda s: (s.pc, s.stack_depth, s.memory_size, s.free_memory_pointer, returns(s)),
        "no_return_tags": lambda s: (s.pc, s.stack_depth, s.memory_size, s.free_memory_pointer, extras(s)),
        "pc_depth_returns": lambda s: (s.pc, s.stack_depth, returns(s)),
        "pc_depth": lambda s: (s.pc, s.stack_depth),
        "pc": lambda s: s.pc,
    }
    distinct = {name: len({f(s) for s in specs}) for name, f in projections.items()}
    by_pc = {b.pc: b for b in blocks}
    groups = proof_groups(specs, [by_pc[pc] for pc in sorted(per_pc)], True) if specs else {}
    distinct["proof_instances_constant_insensitive"] = len(groups)
    # Estimate of --terminal-constant-projection on this set: terminal blocks
    # have no successors, so their projected contexts change no other proposal.
    from verification.block_specialization import project, sensitive_slots, terminal_block
    terminal = {pc: sensitive_slots(by_pc[pc]) for pc in per_pc if terminal_block(by_pc[pc])}
    distinct["terminal_projected"] = len({project(s, terminal[s.pc]) if s.pc in terminal else s for s in specs})
    distinct["instances_at_terminal_blocks"] = sum(s.pc in terminal for s in specs)
    # Estimate of a registration-time projection that keeps every return tag
    # and the constants the block consumes (downstream effects not modeled).
    slots = {pc: sensitive_slots(by_pc[pc]) for pc in per_pc}
    distinct["projected_keep_returns"] = len({project(s, slots[s.pc] | {i for i, _ in returns(s)}) for s in specs})

    def block_row(pc):
        mine = [s for s in specs if s.pc == pc]
        return dict(pc=pc, instances=len(mine),
                    depths=len({s.stack_depth for s in mine}),
                    parameters=len({(s.memory_size, s.free_memory_pointer) for s in mine}),
                    top_parameters=sum(s.memory_size is None and s.free_memory_pointer is None for s in mine),
                    return_contexts=len({(s.stack_depth, returns(s)) for s in mine}),
                    max_return_tags=max((len(returns(s)) for s in mine), default=0),
                    extra_constant_sets=len({extras(s) for s in mine}),
                    proof_instances=sum(1 for k in groups if k.pc == pc))

    rows = [block_row(pc) for pc, _ in per_pc.most_common(top)]
    histogram = lambda values: dict(sorted(Counter(values).items()))
    return dict(
        instances=len(specs), blocks=len(per_pc), distinct=distinct, top_blocks=rows,
        instances_per_block=histogram(per_pc.values()),
        return_tags_per_instance=histogram(len(returns(s)) for s in specs),
        parameter_kinds=dict(Counter(("top" if s.memory_size is None and s.free_memory_pointer is None
                                      else "concrete" if s.memory_size is not None and s.free_memory_pointer is not None
                                      else "mixed") for s in specs)),
        parameters_per_context=histogram(Counter((s.pc, s.stack_depth, returns(s)) for s in specs).values()),
        top_share=dict((f"top{n}", sum(c for _, c in per_pc.most_common(n))) for n in (1, 10, 50, 100)),
    )


def load_specs(path):
    """BlockSpecialization list from a --specs dump (one repr per line)."""
    from verification.block_specialization import BlockSpecialization
    return [eval(line, {"BlockSpecialization": BlockSpecialization})  # our own dump: reprs only
            for line in Path(path).read_text().splitlines() if line.strip()]


def analyze_dump(stem, path):
    """analyze() of a dump against the program's blocks and return tags (no discovery)."""
    from evm_ir.json_parser import load_ir_from_json
    from evm_ir.program import EVMProgram
    blocks = sorted(EVMProgram(load_ir_from_json(str(stem) + ".json")).blocks, key=lambda b: b.pc)
    tags = {t for b in blocks for op in b.operations for t in (op.immediate_set or ())}
    return analyze(load_specs(path), blocks, tags)


def recursive(spec, return_tags):
    """A return tag occurs twice in the context: the call string repeats (recursion)."""
    tags = [v for _, v in spec.stack_constants if v in return_tags]
    return len(tags) != len(set(tags))


def run(stem, options, checkpoint=None, every=500, cut_recursion=False):
    """(specs in discovery order, their sources, defects, error traceback or None,
    seconds, verifier, setup). sources[i] is the (pc, depth) of the instance whose
    EVM exits proposed specs[i] first (None: the raw entry)."""
    import verification.block_parallel as schedule
    from verification.block_program import BlockProgramResult
    from z3 import simplify
    evm, x86, initial, verifier = schedule.build_inputs(stem, options)
    started = time.monotonic()
    setup = verifier._setup(evm, x86, initial, BlockProgramResult(), started, [])
    seen, order, sources, cut = set(), [], [], set()
    original, segment = verifier._discover, schedule.run_evm_segment
    current = [None]

    def tracing(blocks, state, pc, *args, **kwargs):
        current[0] = (pc, simplify(state.evm_stack.SP).as_long())
        return segment(blocks, state, pc, *args, **kwargs)

    def recording(pc, state, joint, budget):
        out = original(pc, state, joint, budget)
        if cut_recursion:
            # Estimation only (never a proof mode): recursive contexts are not
            # registered, so their descendants are not explored either.
            cut.update(s for s in out if recursive(s, verifier._return_tags))
            out = tuple(s for s in out if not recursive(s, verifier._return_tags))
        for spec in out:
            if spec not in seen:
                seen.add(spec)
                order.append(spec)
                sources.append(current[0])
                if checkpoint and len(order) % every == 0:
                    checkpoint(order, sources, time.monotonic() - started)
        return out

    def budget():
        if time.monotonic() - started >= options["wall_seconds"]:
            raise ValueError("program wall budget exhausted")

    # Observation only: proposals and the explored segments are unchanged.
    verifier._discover, schedule.run_evm_segment = recording, tracing
    error, defects = None, ()
    try:
        ordered, defects = schedule.discover(verifier, setup, budget)
        assert set(ordered) == seen
    except Exception:
        error = traceback.format_exc()
    finally:
        schedule.run_evm_segment = segment
    run.cut = len(cut)
    return order, sources, defects, error, time.monotonic() - started, verifier, setup


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("stem", type=Path)
    p.add_argument("--gas-check", choices=("off", "fixed_budget", "full"), default="full")
    p.add_argument("--gas-budget", type=int, default=1_000_000_000)
    p.add_argument("--num-inputs", type=int, default=0)
    p.add_argument("--timeout-ms", type=int, default=30000)
    p.add_argument("--max-depth", type=int, default=400)
    p.add_argument("--max-instances", type=int, default=8192)
    p.add_argument("--max-parameter-values", type=int, default=32)
    p.add_argument("--wall-seconds", type=float, default=21600)
    p.add_argument("--no-summaries", dest="summaries", action="store_false")
    p.add_argument("--pushed-code-return-tags", action="store_true")
    p.add_argument("--terminal-constant-projection", action="store_true")
    p.add_argument("--context-constant-projection", action="store_true")
    p.add_argument("--output", type=Path)
    p.add_argument("--specs", type=Path, help="also dump every discovered spec (repr per line)")
    p.add_argument("--cut-recursion", action="store_true",
                   help="estimate only: do not register contexts whose return tags repeat (recursion)")
    p.add_argument("--from-specs", type=Path, help="analyze a --specs dump offline instead of discovering")
    args = p.parse_args()
    if args.from_specs:
        report = analyze_dump(args.stem, args.from_specs)
        text = json.dumps(report, indent=2, default=repr)
        if args.output:
            args.output.write_text(text + "\n")
        print(text)
        return 0
    options = dict(gas_check=args.gas_check, gas_budget=args.gas_budget, num_inputs=args.num_inputs,
                   timeout_ms=args.timeout_ms, max_depth=args.max_depth, max_instances=args.max_instances,
                   max_parameter_values=args.max_parameter_values, wall_seconds=args.wall_seconds,
                   summaries=args.summaries, node_seconds=1800, first_pass_node_seconds=None,
                   pushed_code_return_tags=args.pushed_code_return_tags,
                   terminal_constant_projection=args.terminal_constant_projection,
                   context_constant_projection=args.context_constant_projection)

    def dump(order, sources, seconds, done=False, error=None, defects=(), verifier=None, setup=None):
        if args.specs:
            args.specs.write_text("".join(repr(s) + "\n" for s in order))
            args.specs.with_suffix(".sources").write_text("".join(f"{p}\n" for p in sources))
        report = dict(stem=str(args.stem), options=options, seconds=seconds, finished=done,
                      error=error, defects=list(defects), discovered=len(order))
        if setup is not None:
            report["cut_recursive_contexts"] = getattr(run, "cut", None) if args.cut_recursion else None
            report["stats"] = analyze(order, setup.evm, verifier._return_tags)
            report["discovery_queries"] = verifier._discovery_queries
        text = json.dumps(report, indent=2, default=repr)
        if args.output:
            args.output.write_text(text + "\n")
        return text

    def checkpoint(order, sources, seconds):
        dump(order, sources, seconds)
        print(f"[{seconds:.0f}s] {len(order)}", flush=True)

    order, sources, defects, error, seconds, verifier, setup = run(args.stem, options, checkpoint,
                                                                   cut_recursion=args.cut_recursion)
    print(dump(order, sources, seconds, True, error, defects, verifier, setup))
    return 0 if error is None else 1


if __name__ == "__main__":
    raise SystemExit(main())
