"""Regression tests from the z8 review (tmp/measurement-work): soundness counterexamples the instruction-chain
producer must reject. B1: a TAG-only block's exit must keep the TAG's static gas. B2: R15's tag at an inner
boundary is checked even before the first literal reload."""
import hashlib
import json
from time import monotonic
from types import SimpleNamespace

import capstone

from evm_ir.models import EVMBlock, EvmOperator
from verification import instruction_chain as ic
from verification.block_equivalence import BlockEquivalenceProver
from verification.block_relation import BlockRelationSchema
from verification.block_specialization import BlockSpecialization
from verification.call_site_mapping import CallSiteMapping
from x86_64.aot_profile import AOT_COMPILER_PROFILE
from x86_64.models import X86Block, X86Instruction


def native(hex_code):
    md = capstone.Cs(capstone.CS_ARCH_X86, capstone.CS_MODE_64)
    md.detail = True
    insns = [X86Instruction(i.address, i.mnemonic, i.op_str, bytes(i.bytes), i.size, i)
             for i in md.disasm(bytes.fromhex(hex_code), 0x1000)]
    return insns, [X86Block(i.addr, i.addr + i.size, [i]) for i in insns]


def test_tag_only_block_exit_keeps_the_static_charge(tmp_path):
    # Block 0 is only a TAG with static gas 1; its x86 code jumps to block 1 without charging gas.
    code_hex = "e90000000090"
    _, blocks = native(code_hex)
    tag = EvmOperator("TAG", 0, param=0)
    b0 = EVMBlock(0, 0, 0, 1024, 1, True, False, False, [tag])
    b1 = EVMBlock(1, 0, 0, 1024, 0, True, True, False, [EvmOperator("TAG", 1, param=1), EvmOperator("STOP", 2)])
    for b in (b0, b1):
        for op in b.operations:
            op.block = b
    p = BlockEquivalenceProver([b0, b1], blocks, {0: 0x1000, 1: 0x1005}, timeout_ms=1000, max_depth=20)
    p.validate()
    code = bytes.fromhex(code_hex)
    (tmp_path / "hint.json").write_text(json.dumps(dict(
        pc=0, code_sha256=hashlib.sha256(code).hexdigest(), code_load_base=4096,
        instructions=[dict(instruction_index=0, opcode="TAG", start=4096, end=4101, before=[], after=[])])))
    p.instruction_hints = ic.load_hints(tmp_path, code)
    p.instruction_hints_digest = ic.hints_digest(p.instruction_hints)
    s, t = BlockSpecialization(0, 0, None, None, ()), BlockSpecialization(1, 0, None, None, ())
    p.deadline = monotonic() + 120
    node = ic.prove_node(p, s, (s,), p.instruction_hints[0], {0: (s,), 1: (t,)}, p.portable_identity, 60)
    # Before the fix: proved, complete theorem, H2 closed although EVM gas 9 != x86 gas 10 at the successor.
    assert node is not None, "the chain producer must take this block (structure and entry tags are fine)"
    assert not node["proved"] and node["theorem"] is None
    assert any("solver=sat" in r for r in node["reasons"]), node["reasons"]


def chain_prover_for(tmp_path, blocks, raw, mapping, rows):
    """A validated prover with a hint for blocks[0] (review's z8c probe harness)."""
    from x86_64.disassembler import disassemble_hex
    for b in blocks:
        for op in b.operations:
            op.block = b
    xs = [X86Block(i.addr, i.addr + i.size, [i]) for i in disassemble_hex(raw, base_addr=0x1000)]
    p = BlockEquivalenceProver(blocks, xs, mapping, timeout_ms=1000, max_depth=30)
    p.validate()
    pc = blocks[0].pc
    (tmp_path / "hint.json").write_text(json.dumps(dict(
        pc=pc, code_sha256=hashlib.sha256(bytes.fromhex(raw)).hexdigest(), code_load_base=4096,
        instructions=[dict(instruction_index=k, opcode=kind, start=a, end=b, before=[], after=[])
                      for k, kind, a, b in rows])))
    p.instruction_hints = ic.load_hints(tmp_path, bytes.fromhex(raw))
    p.instruction_hints_digest = ic.hints_digest(p.instruction_hints)
    p.deadline = monotonic() + 120
    return p, BlockSpecialization(pc, 0, None, None, ()), p.instruction_hints[pc]


def test_self_jump_with_last_pc_equal_to_block_pc_is_not_taken(tmp_path):
    # Review z8c: TAG(0); JUMP(pc=0 -> 0). The exit stand-in at pc 0 would replace the block and lose its
    # jump-target bit (EVM: a valid self jump; x86 stand-in run: INVALID_JUMP). The producer must not take it.
    block = EVMBlock(0, 0, 0, 1024, 0, True, False, False,
                     [EvmOperator("TAG", 0), EvmOperator("JUMP", 0, immediate=0, is_static=True)])
    p, s, h = chain_prover_for(tmp_path, [block], "4d8b753841c685e000000008c3", {0: 0x1000},
                               [(0, "TAG", 0x1000, 0x1004), (1, "JUMP", 0x1004, 0x100d)])
    assert ic.prove_node(p, s, (s,), h, {0: (s,)}, p.portable_identity, 30) is None


def test_last_pc_below_block_pc_is_not_taken(tmp_path):
    # Review z8c: TAG(10); BLOCKEND(5). Sorting the stand-in at pc 5 changes the fallthrough (EVM: to block 20;
    # x86: back to the source). The producer must not take it.
    b0 = EVMBlock(10, 0, 0, 1024, 0, True, False, False, [EvmOperator("TAG", 10), EvmOperator("BLOCKEND", 5)])
    b1 = EVMBlock(20, 0, 0, 1024, 0, True, False, False, [EvmOperator("TAG", 20), EvmOperator("STOP", 21)])
    p, s, h = chain_prover_for(tmp_path, [b0, b1], "4d8b7538e9f7ffffff90", {10: 0x1000, 20: 0x1009},
                               [(0, "TAG", 0x1000, 0x1004), (1, "BLOCKEND", 0x1004, 0x1009)])
    target = BlockSpecialization(20, 0, None, None, ())
    assert ic.prove_node(p, s, (s,), h, {10: (s,), 20: (target,)}, p.portable_identity, 30) is None


def test_height_plan_with_a_terminal_op_falls_back(tmp_path):
    # Review z8e R1: TAG; STOP; BLOCKEND has no continuing height after the STOP: a partial plan must give None
    # (legacy prover), not an IndexError.
    block = EVMBlock(0, 0, 0, 1024, 0, True, False, False,
                     [EvmOperator("TAG", 0), EvmOperator("STOP", 1), EvmOperator("BLOCKEND", 2)])
    target = EVMBlock(3, 0, 0, 1024, 0, True, False, False, [EvmOperator("TAG", 3), EvmOperator("STOP", 4)])
    p, s, h = chain_prover_for(tmp_path, [block, target], "4d8b7538909090", {0: 0x1000, 3: 0x1006},
                               [(0, "TAG", 0x1000, 0x1004), (1, "STOP", 0x1004, 0x1005),
                                (2, "BLOCKEND", 0x1005, 0x1006)])
    assert ic.prove_node(p, s, (s,), h, {}, p.portable_identity, 30) is None


def test_height_plan_below_zero_falls_back_and_legacy_proves(tmp_path):
    # Review z8e R1: entry depth 0, real min_depth 2: TAG's guard stops before the POPs, but the plan (without the
    # guard) would build a negative height. The producer must give None; the legacy prover proves the block.
    block = EVMBlock(0, -2, 2, 1024, 0, True, False, False,
                     [EvmOperator("TAG", 0), EvmOperator("POP", 1), EvmOperator("POP", 2), EvmOperator("BLOCKEND", 3)])
    target = EVMBlock(4, 0, 0, 1024, 0, True, False, False, [EvmOperator("TAG", 4), EvmOperator("STOP", 5)])
    p, s, h = chain_prover_for(tmp_path, [block, target], "41c685e00000000ec390", {0: 0x1000, 4: 0x1009},
                               [(0, "TAG", 0x1000, 0x1009), (1, "POP", 0x1009, 0x1009),
                                (2, "POP", 0x1009, 0x1009), (3, "BLOCKEND", 0x1009, 0x1009)])
    assert ic.prove_node(p, s, (s,), h, {}, p.portable_identity, 30) is None
    p.deadline = None
    assert p.prove(s).proved


def test_r15_reload_through_another_register_is_rejected():
    # A no-op EVM op whose code restores R15's value through rax (mov rax,[r13+0x10]; mov r15,rax): its tag
    # becomes EVM_PTR without the literal reload the predictor looks for, so the next boundary's NONE fails.
    insns, blocks = native("498b45104989c790")
    ops = [EvmOperator("TAG", 100), EvmOperator("BLOCKEND", 101), EvmOperator("JUMP", 102)]
    block = EVMBlock(100, 0, 0, 1024, 0, False, False, False, ops)
    for op in ops:
        op.block = block
    prover = SimpleNamespace(schema=BlockRelationSchema(), host_gas_uf_enabled=True, aot_profile=AOT_COMPILER_PROFILE,
                             deadline=None, pc_to_addr={100: 0x1000}, x86_blocks=blocks)
    hint = ic.BlockHint(100, "test", tuple(ic.OpHint(k, op.kind, 0x1000, insns[-1].addr, (), ())
                                           for k, op in enumerate(ops)), "probe")
    chain = object.__new__(ic.ChainProver)
    chain.prover, chain.block, chain.d0, chain.hint = prover, block, 1, hint
    chain.region = chain.natural = blocks
    chain.starts, chain.macro = {b.start_addr for b in blocks}, set()
    chain.heights = [1, 1, 1]
    chain.call_site_mapping, chain.memo = CallSiteMapping({}), {}
    tags = ic.r15_tags(blocks, hint)
    assert tags[2] == "NONE"
    leaf, reason = chain.prove_op(1, (), (), tags[1], tags[2])
    assert leaf is None and "R15 tag" in reason, reason
