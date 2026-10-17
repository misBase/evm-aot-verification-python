"""PoolManager SAT triage: concrete differential replay of single blocks (offline evidence only).

A small EVM interpreter over the IR operations runs against the real machine code under
Unicorn. Nothing here feeds the verifier; it only replays the solver's counterexamples
concretely. Needs `pip install unicorn` in the project venv (not a project dependency).

    PYTHONPATH=. .venv/bin/python cloud-inputs/reports/poolmanager-sat/concrete_replay.py
    PYTHONPATH=. .venv/bin/python cloud-inputs/reports/poolmanager-sat/concrete_replay.py --fuzz 300

Runtime layout read off the generated code (x86_64/aot_profile.py offsets): [r13+0x70] gas,
[r13+0x30] stack size in bytes, [r13+0x38] stack base, r14 = base + size (top word at
[r14-0x20], limbs little-endian), [r13+0x10]/[r13+0x18] memory base/size, r15 = memory base,
[r13+0xe0] status. A builtin call (status 5) is served like the Go runtime: memory_grow is a
no-op (memory is pre-sized), div/mod pop a, b at [r14 + sp*8] (sp = [r13+0x28] limbs) and
push a/b, a%b (0 when b == 0); execution resumes at [r13+0xf0].
"""
from __future__ import annotations

import argparse
import json
import random
import re
from pathlib import Path

from unicorn import UC_ARCH_X86, UC_HOOK_CODE, UC_MODE_64, Uc
from unicorn.x86_const import UC_X86_REG_R13, UC_X86_REG_R14, UC_X86_REG_R15, UC_X86_REG_RSP

STEM = "cloud-inputs/poolmanager/PoolManager"
M = (1 << 256) - 1
BASE = 0x1000
ENGINE, STACK, MEMORY, NATIVE = 0x10_0000_0000, 0x20_0000_0000, 0x30_0000_0000, 0x40_0000_0000
RET = NATIVE + 0x1000
SUPPORTED = {"TAG", "BLOCKEND", "PUSH", "POP", "DUP", "SWAP", "JUMP", "JUMPI", "MLOAD", "SIGNEXTEND", "SAR",
             "SUB", "ADD", "AND", "OR", "GT", "LT", "SGT", "SLT", "DIV", "SDIV", "SMOD"}


def signed(x):
    return x - (1 << 256) if x >> 255 else x


def evm_block(ops, stack, memory):
    """(JUMP/JUMPI target or None for fall-through, final stack bottom..top)."""
    st = list(stack)
    for o in ops:
        k, p = o["kind"], o.get("param")
        if k in ("TAG", "BLOCKEND"):
            continue
        if k == "PUSH":
            st.append(int(o.get("immediate") or "0"))
        elif k == "POP":
            st.pop()
        elif k == "DUP":
            st.append(st[-p])
        elif k == "SWAP":
            st[-1], st[-1 - p] = st[-1 - p], st[-1]
        elif k == "JUMP":
            return (int(o["immediate"]) if "immediate" in o else st.pop()), st
        elif k == "JUMPI":
            target = int(o["immediate"]) if "immediate" in o else st.pop()
            return (target if st.pop() else None), st
        elif k == "MLOAD":
            a = st.pop()
            st.append(int.from_bytes(bytes(memory.get(a + i, 0) for i in range(32)), "big"))
        else:
            a, b = st.pop(), st.pop()
            sa, sb = signed(a), signed(b)
            if k == "SIGNEXTEND":
                r = b
                if a < 31:
                    bit = a * 8 + 7
                    r = b & ((1 << (bit + 1)) - 1)
                    if r >> bit:
                        r |= M ^ ((1 << (bit + 1)) - 1)
            elif k == "SAR":
                r = (sb >> min(a, 256)) & M
            elif k == "SUB":
                r = (a - b) & M
            elif k == "ADD":
                r = (a + b) & M
            elif k == "AND":
                r = a & b
            elif k == "OR":
                r = a | b
            elif k == "GT":
                r = int(a > b)
            elif k == "LT":
                r = int(a < b)
            elif k == "SGT":
                r = int(sa > sb)
            elif k == "SLT":
                r = int(sa < sb)
            elif k == "DIV":
                r = 0 if b == 0 else a // b
            elif k == "SDIV":
                q = 0 if b == 0 else abs(sa) // abs(sb)
                r = (q if (sa < 0) == (sb < 0) else -q) & M
            elif k == "SMOD":
                q = 0 if b == 0 else abs(sa) % abs(sb)
                r = (-q if sa < 0 else q) & M
            else:
                raise NotImplementedError(k)
            st.append(r)
    return None, st


def load_program():
    from evm_ir.json_parser import load_ir_from_json
    from evm_ir.program import EVMProgram
    from tools.tag_align import build_block_alignment
    from x86_64.cfg import identify_basic_blocks
    from x86_64.program import X86Program
    blocks = sorted(EVMProgram(load_ir_from_json(STEM + ".json")).blocks, key=lambda b: b.pc)
    code = bytes.fromhex(Path(STEM + ".hex").read_text().strip())
    x86 = X86Program.from_hex(code.hex(), base_addr=BASE)
    alignment = build_block_alignment(blocks, x86.instructions, identify_basic_blocks(x86.instructions))
    frames = {f["operations"][0]["pc"]: f for f in json.loads(Path(STEM + ".json").read_text())["control_frames"]}
    return code, dict(alignment.pc_to_addr), frames


def x86_block(code, pc_to_addr, pc, stack, memory, gas=1 << 40):
    """Run block `pc`'s machine code until it reaches another block's address or returns."""
    addr_to_pc = {}
    for p, a in pc_to_addr.items():
        addr_to_pc.setdefault(a, []).append(p)
    mu = Uc(UC_ARCH_X86, UC_MODE_64)
    mu.mem_map(BASE & ~0xfff, ((len(code) + 0xfff) & ~0xfff) + 0x2000)
    mu.mem_write(BASE, code)
    for region in (ENGINE, STACK, MEMORY, NATIVE):
        mu.mem_map(region, 0x10_0000)
    engine = bytearray(0x200)
    engine[0x10:0x18] = MEMORY.to_bytes(8, "little")
    engine[0x18:0x20] = (0x10000).to_bytes(8, "little")
    engine[0x30:0x38] = (32 * len(stack)).to_bytes(8, "little")
    engine[0x38:0x40] = STACK.to_bytes(8, "little")
    engine[0x70:0x78] = gas.to_bytes(8, "little")
    mu.mem_write(ENGINE, bytes(engine))
    for n, w in enumerate(stack):
        mu.mem_write(STACK + 32 * n, w.to_bytes(32, "little"))
    for offset, byte in memory.items():
        mu.mem_write(MEMORY + offset, bytes([byte]))
    mu.reg_write(UC_X86_REG_R13, ENGINE)
    mu.reg_write(UC_X86_REG_R14, STACK + 32 * len(stack))
    mu.reg_write(UC_X86_REG_R15, MEMORY)
    start, stop = pc_to_addr[pc], {}

    def hook(uc, address, size, _):
        if address == RET or (address != start and address in addr_to_pc):
            stop["at"] = "ret" if address == RET else address
            uc.emu_stop()

    mu.hook_add(UC_HOOK_CODE, hook)
    resume, builtins = start, []
    while True:
        stop.clear()
        mu.mem_write(NATIVE + 0x800, RET.to_bytes(8, "little"))
        mu.reg_write(UC_X86_REG_RSP, NATIVE + 0x800)
        mu.emu_start(resume, BASE + len(code) + 0x10, count=200000)
        engine = mu.mem_read(ENGINE, 0x200)
        index = int.from_bytes(engine[0xe4:0xe8], "little")
        if stop.get("at") != "ret" or engine[0xe0] != 5 or index not in (0, 4, 5):
            break
        if index in (4, 5):
            r14 = int.from_bytes(engine[0x38:0x40], "little") + int.from_bytes(engine[0x30:0x38], "little")
            sp = int.from_bytes(engine[0x28:0x30], "little")
            a = int.from_bytes(mu.mem_read(r14 + (sp - 4) * 8, 32), "little")
            b = int.from_bytes(mu.mem_read(r14 + (sp - 8) * 8, 32), "little")
            r = 0 if b == 0 else (a // b if index == 4 else a % b)
            mu.mem_write(r14 + (sp - 8) * 8, r.to_bytes(32, "little"))
            mu.mem_write(ENGINE + 0x28, (sp - 4).to_bytes(8, "little"))
        builtins.append(index)
        mu.mem_write(ENGINE + 0xe0, bytes([0]))
        mu.reg_write(UC_X86_REG_R13, ENGINE)
        resume = int.from_bytes(engine[0xf0:0xf8], "little")
    engine = mu.mem_read(ENGINE, 0x200)
    depth = int.from_bytes(engine[0x30:0x38], "little") // 32
    return dict(pcs=addr_to_pc.get(stop.get("at")), status=engine[0xe0], builtins=builtins,
                gas_used=gas - int.from_bytes(engine[0x70:0x78], "little"),
                stack=[int.from_bytes(mu.mem_read(STACK + 32 * n, 32), "little") for n in range(depth)])


def compare(program, pc, stack, memory=None, label=""):
    code, p2a, frames = program
    ops = frames[pc]["operations"]
    memory = memory or {}
    target, est = evm_block(ops, stack, memory)
    successor = target if target is not None else ops[-1]["pc"] + 1
    x = x86_block(code, p2a, pc, stack, memory)
    same = x["status"] == 0 and x["pcs"] is not None and successor in x["pcs"] and x["stack"] == est
    print(f"pc={pc} {label:44s} EVM->{successor} x86->{x['pcs']} status={x['status']} "
          f"{'AGREE' if same else 'MISMATCH'}")
    for n, (a, b) in enumerate(zip(est, x["stack"])):
        if a != b:
            print(f"    slot {n}: evm={a:#066x}\n             x86={b:#066x}")
    return same


def limbs(*z):
    return sum(v << (64 * n) for n, v in enumerate(z))


def counterexamples(program):
    # pc=7132 (int128 overflow check of sext(T >>s 128) - sext(A)). Solver model of x86_maps_0_0.
    T = limbs(0x00a6c4642cc00000, 0, 0x2ff1f1196502b000, 0x4000000000000000)  # stack_15 (top)
    A = limbs(0xb7057be9031c7e07, 0xc000000000000000, 0, 0)                    # stack_4 (DUP12)
    for t, a, s13, label in ((T, A, 0, "solver model (T>=0)"),
                             (0, 1, 0, "minimal: T=0, A=1"),
                             (T | 1 << 255, A, 0, "T<0 (spill taken)"),
                             (T | 1 << 255, A, 1 << 255, "T<0, d<0, stale slot-13 limb 3")):
        stack = [0] * 16
        stack[15], stack[4], stack[13] = t, a, s13
        compare(program, 7132, stack, label=label)
    # pc=7329 (tickSpacingToMaxLiquidityPerTick): tickSpacing word at mload(e1+128), liquidity at mload(e8+32).
    for tick_spacing, liquidity, label in ((60, 0, "tickSpacing=60"),
                                           (60, ((1 << 128) - 1) // 29576 + 1, "tickSpacing=60, liquidity=max+1"),
                                           (1, 0, "tickSpacing=1 (MIN_TICK % ts == 0)")):
        stack = [0] * 12
        stack[1], stack[8] = 0x400, 0x800
        memory = {}
        for base, word in ((0x480, tick_spacing), (0x820, liquidity)):
            memory.update((base + i, b) for i, b in enumerate(word.to_bytes(32, "big")))
        compare(program, 7329, stack, memory, label)
    # pc=7024 (POP; DUP14; SIGNEXTEND(15); SWAP1; SAR(128); JUMP 15674): exit stack slot 17.
    for t, a, label in ((0, limbs(0xffffffffffffffff), "H2 model: T>=0, A.z0=2^64-1"),
                        (M ^ 0x1234, limbs(0xffffffffffffffff), "T<0 (spill taken)")):
        stack = [0x1111 * (n + 1) for n in range(19)]
        stack[17], stack[4] = t, a
        compare(program, 7024, stack, label=label)


def fuzz(program, runs):
    """Random differential runs over every interpreter-supported block the survey attempted."""
    code, p2a, frames = program
    survey = json.loads(Path(STEM + "-survey.partial.json").read_text())["diagnostics"]
    rng = random.Random(7)

    def word():
        return rng.choice((lambda: rng.getrandbits(256), lambda: rng.getrandbits(24),
                           lambda: -rng.getrandbits(24) & M, lambda: rng.getrandbits(128),
                           lambda: -rng.getrandbits(127) & M, lambda: rng.randrange(0x80, 0x2000, 32),
                           lambda: rng.getrandbits(64), lambda: rng.choice([0, 1, 2, 60, (1 << 128) - 1, M])))()

    for pc in sorted(frames):
        ops = frames[pc]["operations"]
        if not {o["kind"] for o in ops} <= SUPPORTED or str(pc) not in survey or pc not in p2a:
            continue
        for instance in survey[str(pc)]["instances"]:
            depth = int(re.search(r"stack_depth=(\d+)", instance["spec"]).group(1))
            done = bad = 0
            for _ in range(runs):
                stack = [word() for _ in range(depth)]
                memory = {a: rng.getrandbits(8) for a in range(0x80, 0x2040)}
                try:
                    target, est = evm_block(ops, stack, memory)
                    x = x86_block(code, p2a, pc, stack, memory)
                except Exception:
                    continue  # underflow on the EVM side / wild pointer outside the mapped window
                if x["status"] != 0 or x["pcs"] is None:
                    continue  # error exits are not compared
                done += 1
                successor = target if target is not None else ops[-1]["pc"] + 1
                bad += not (successor in x["pcs"] and x["stack"] == est)
            print(f"pc={pc} depth={depth} survey={instance['status']:12s} runs={done:4d} mismatches={bad}",
                  flush=True)


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--fuzz", type=int, default=0, help="random runs per surveyed instance (0: counterexamples only)")
    args = p.parse_args()
    program = load_program()
    counterexamples(program)
    if args.fuzz:
        fuzz(program, args.fuzz)


if __name__ == "__main__":
    main()
