"""Instruction-chain producer: hint loading, chain checks, entry-tag analysis, theorem completeness and the
consumer's producer registry. Mostly negative cases: a wrong hint, chain, dependency or producer must never
yield a complete theorem or an accepted node."""
import json
from dataclasses import replace
from hashlib import sha256
from types import SimpleNamespace

import pytest

from verification.block_equivalence import BlockTheorem, InstructionBlockTheorem, Obligation
from verification.block_parallel import _producer_ok
from verification.block_specialization import BlockSpecialization
from verification.instruction_chain import (PROOF_KIND, BlockHint, OpHint, boolean_refutation,
                                            chain_problems, entry_tags_dead, height, load_hints, locations,
                                            r15_tags)

ENTRY = 0x2000


def op(kind, pc=10, param=None):
    return SimpleNamespace(kind=kind, pc=pc, param=param)


def reg_entry(word, limb, register):
    return (4 * word + limb, word, limb, "register", register, 0)


def hint(ops, pc=10):
    return BlockHint(pc, "c0de", tuple(ops), "digest-" + str(len(ops)))


def good_chain():
    """TAG; PUSH (value kept in rax, limbs 1-3 constant 0); POP."""
    pushed = (reg_entry(0, 0, "AX"),) + tuple((4 * 0 + l, 0, l, "constant", None, 0) for l in (1, 2, 3))
    return hint([OpHint(0, "TAG", ENTRY, ENTRY + 8, (), ()),
                 OpHint(1, "PUSH", ENTRY + 8, ENTRY + 8, (), pushed),
                 OpHint(2, "POP", ENTRY + 8, ENTRY + 12, pushed, ())])


GOOD_HEIGHTS = (3, 3, 4)   # semantic EVM heights before TAG, PUSH, POP at entry depth 3
BLOCK = SimpleNamespace(pc=10, operations=[op("TAG", pc=10), op("PUSH", pc=11), op("POP", pc=13)])


def test_good_chain_has_no_problems():
    assert chain_problems(BLOCK, good_chain(), 3, ENTRY, heights=GOOD_HEIGHTS) == []


@pytest.mark.parametrize("mutate, reason", [
    (lambda ops: ops[:2], "cover"),                                          # missing op
    (lambda ops: [ops[0], ops[1], replace(ops[2], index=1)], "cover"),       # duplicate index
    (lambda ops: [replace(ops[0], start=ENTRY + 4), *ops[1:]], "entry"),     # not at the real entry
    (lambda ops: [ops[0], replace(ops[1], start=ENTRY + 9), ops[2]], "break"),  # gap between intervals
    (lambda ops: [ops[0], ops[1], replace(ops[2], before=())], "differ"),    # location table mismatch
    (lambda ops: [replace(ops[0], opcode="JUMP"), *ops[1:]], "opcode"),      # hint opcode is not the IR's
    (lambda ops: [replace(ops[0], before=(reg_entry(-1, 0, "AX"),)), *ops[1:]], "entry relation"),
])
def test_chain_problems_reject(mutate, reason):
    bad = hint(mutate(list(good_chain().ops)))
    problems = chain_problems(BLOCK, bad, 3, ENTRY, heights=GOOD_HEIGHTS)
    assert problems and any(reason in p for p in problems), problems


def test_locations_and_height():
    # The trace lists every limb of every word in the compiler's window: here one pushed word above d0 = 3.
    entries = (reg_entry(0, 0, "AX"), (1, 0, 1, "stack", None, 0), (2, 0, 2, "constant", None, 7),
               (3, 0, 3, "stack", None, 0))
    h = height(entries, 3)
    assert h == 4
    locs = locations(entries, h, 3)
    assert locs[0][0][0] == "r" and locs[0][2] == ("c", 7) and locs[0][1] == ("s",) and locs[1] == (("s",),) * 4


def write_trace(path, pc, code, rows, base=4096):
    path.write_text(json.dumps(dict(pc=pc, code_sha256=sha256(code).hexdigest(), code_load_base=base,
                                    instructions=rows)))


def row(k, opcode="ADD"):
    return dict(instruction_index=k, opcode=opcode, start=4096 + k, end=4097 + k, before=[], after=[])


def test_load_hints_matches_code_and_rejects_ambiguity(tmp_path):
    code = b"\x90\x90"
    write_trace(tmp_path / "a.json", 7, code, [row(0), row(1)])
    write_trace(tmp_path / "other-code.json", 8, b"\xcc", [row(0)])           # another program: ignored
    write_trace(tmp_path / "other-base.json", 9, code, [row(0)], base=0)       # another load base: ignored
    hints = load_hints(tmp_path, code)
    assert set(hints) == {7} and [o.index for o in hints[7].ops] == [0, 1]
    write_trace(tmp_path / "dup.json", 7, code, [row(0)])
    with pytest.raises(ValueError, match="two hints"):
        load_hints(tmp_path, code)
    (tmp_path / "dup.json").unlink()
    write_trace(tmp_path / "a.json", 7, code, [row(0), row(0)])
    with pytest.raises(ValueError, match="duplicate"):
        load_hints(tmp_path, code)


def tags_dead(hex_code, cuts=()):
    """entry_tags_dead on real decoded blocks, bridges recognised by the executor's own pattern."""
    from verification.block_partition import split_at_cutpoints
    from x86_64.aot_profile import AOT_COMPILER_PROFILE
    from x86_64.cfg import identify_basic_blocks
    from x86_64.cfg_executor import X86SymbolicExecutor
    from x86_64.disassembler import disassemble_hex
    blocks = split_at_cutpoints(identify_basic_blocks(disassemble_hex(hex_code, base_addr=0x1000)), set(cuts))
    bridge = X86SymbolicExecutor(blocks, enable_merge=False, use_reachability_check=False)._is_call_go_function_pattern
    end = 0x1000 + len(bytes.fromhex(hex_code))
    return entry_tags_dead(blocks, 0x1000, end, bridge, AOT_COMPILER_PROFILE.offsets["return_address"])[0]


@pytest.mark.parametrize("hex_code, dead", [
    ("488b18", False),              # mov rbx,[rax]: reads rax's entry tag
    ("498b4500488b18", True),       # mov rax,[r13]; mov rbx,[rax]: rax rewritten first
    ("4889c1488b19", False),        # mov rcx,rax; mov rbx,[rcx]: the origin flows through the move
    ("498b4600", True),             # [r14]: routed by name, no tag read
    ("488d4808488b19", False),      # lea rcx,[rax+8]; mov rbx,[rcx]: lea keeps the origin
    ("c3488b1b", True),             # a ret without the bridge pattern is terminal: nothing after it runs
    ("ffd0", False),                # call rax: unknown
])
def test_entry_tags_dead(hex_code, dead):
    assert tags_dead(hex_code) is dead


# Review z8 B3: mov qword [r13+0xf0], 0x1017; mov byte [r13+0xe0], 5; ret; 0x1014: xor rbx,rbx;
# 0x1017: mov rax,[rbx]; mov byte [r13+0xe0], 2; ret. The executor resumes the bridge at the saved address
# 0x1017, past the instruction that clears rbx, so rbx's entry tag is read.
BRIDGE = "49c785f00000001710000041c685e000000005c34831db488b0341c685e000000002c3"


def test_bridge_resumes_at_the_saved_return_address():
    assert tags_dead(BRIDGE, cuts=(0x1017,)) is False


def test_bridge_return_address_from_rip_relative_lea():
    # 0x1000 lea rax,[rip+0x13] (= 0x101a); 0x1007 mov [r13+0xf0],rax; 0x100e mov byte [r13+0xe0],5; 0x1016 ret;
    # 0x1017 xor rbx,rbx; 0x101a mov rax,[rbx]
    code = "488d0513000000" + "498985f0000000" + "41c685e000000005" + "c3" + "4831db" + "488b03"
    assert tags_dead(code, cuts=(0x101a,)) is False


ALIAS_TAIL = "4831db488b0341c685e000000002c3"   # 0x101c xor rbx,rbx; 0x101f mov rax,[rbx]; ...; ret


def test_bridge_return_address_register_alias():
    # Review z8b #3A: lea rax,[rip+0x15] (= 0x101c); mov eax,0x101f; mov [r13+0xf0],rax: the saved address is
    # 0x101f (eax wrote rax after the lea), past the xor: rbx's entry tag is read. Not dead.
    code = "488d0515000000b81f100000498985f000000041c685e000000005c3" + ALIAS_TAIL
    assert tags_dead(code, cuts=(0x101c, 0x101f)) is False


def test_bridge_return_address_field_rewritten():
    # Review z8b #3B: mov qword [r13+0xf0],0x101c; add qword [r13+0xf0],3: the field ends as 0x101f. Not dead.
    code = "49c785f00000001c100000498385f00000000341c685e000000005c3" + ALIAS_TAIL
    assert tags_dead(code, cuts=(0x101c, 0x101f)) is False


def test_tag_normal_form_and_pc_conflicts():
    # Review z8b #1: the TAG must be unique and op 0 (its lemma alone carries the block's gas and guards)
    for kinds in (["BLOCKEND", "TAG"], ["BLOCKEND", "BLOCKEND"], ["TAG", "TAG"]):
        block = SimpleNamespace(pc=10, operations=[op(k, pc=10 + n) for n, k in enumerate(kinds)])
        chain = hint([OpHint(n, k, ENTRY + n, ENTRY + n + 1, (), ()) for n, k in enumerate(kinds)])
        assert any("TAG normal form" in p for p in chain_problems(block, chain, 3, ENTRY)), kinds
    # Review z8b #2: another block's pc within (block.pc, last op pc] would be replaced by the exit's stand-in
    block = SimpleNamespace(pc=0, operations=[op("TAG", pc=0), op("BLOCKEND", pc=1), op("JUMPI", pc=1)])
    chain = hint([OpHint(n, k, ENTRY + n, ENTRY + n + 1, (), ()) for n, k in enumerate(["TAG", "BLOCKEND", "JUMPI"])])
    assert not any("stand-in" in p for p in chain_problems(block, chain, 1, ENTRY, {0, 2}))
    assert any("stand-in" in p for p in chain_problems(block, chain, 1, ENTRY, {0, 1, 2}))
    # Review z8c: a multi-op block whose last op pc equals the block pc (the stand-in would replace the block
    # itself and drop is_jump_target) or lies below it (sorting would change the fallthrough)
    for last_pc in (5, 3):
        block = SimpleNamespace(pc=5, operations=[op("TAG", pc=5), op("BLOCKEND", pc=5), op("JUMP", pc=last_pc)])
        chain = hint([OpHint(n, k, ENTRY + n, ENTRY + n + 1, (), ()) for n, k in enumerate(["TAG", "BLOCKEND", "JUMP"])])
        assert any("stand-in" in p for p in chain_problems(block, chain, 1, ENTRY, {5, 9})), last_pc
    single = SimpleNamespace(pc=5, operations=[op("TAG", pc=5)])                       # its exit runs the real block
    assert not any("stand-in" in p for p in chain_problems(single, hint([OpHint(0, "TAG", ENTRY, ENTRY + 1, (), ())]),
                                                           1, ENTRY, {5, 9}))


def test_bridge_return_address_not_static_is_unknown():
    # the saved address is rax as it was at entry (no rip-relative lea in the block): unknown, not dead
    assert tags_dead("498985f0000000" + "41c685e000000005" + "c3") is False


def test_r15_tags_switch_on_reload():
    insn = SimpleNamespace(addr=ENTRY + 8, mnemonic="mov", op_str="r15, qword ptr [r13 + 0x10]")
    blocks = [SimpleNamespace(instructions=[insn])]
    tags = r15_tags(blocks, good_chain())
    assert tags == {0: None, 1: "NONE", 2: "NONE", 3: "EVM_PTR"}   # explicit after the entry (review z8 B2)


def test_boolean_refutation_only_unsat():
    from z3 import And, BitVec, Bool, Not, Or
    x = BitVec("x", 8)
    assert boolean_refutation(And(Or(x == 1, Bool("p")), Not(Or(x == 1, Bool("p")))))
    assert not boolean_refutation(And(x == 1, x == 2))   # UNSAT only below the atoms: skeleton is SAT


# ---------------------------------------------------------------- theorem

SPEC = BlockSpecialization(10, 3, None, None, ())


def unsat(name):
    return Obligation(name, "sha256:x", "unsat")


def theorem(**changes):
    leaves = (Obligation("instruction_0", "leaf", "unsat", lemmas=(unsat("q0"),), required_lemmas=("q0",)),)

    def derived(name):
        return Obligation(name, "derived", "unsat", lemmas=leaves, required_lemmas=("instruction_0",))
    records = (Obligation("entry_nonempty", "x", "sat", "sat"), unsat("havoc_relation"),
               Obligation("model_domain_nonempty", "x", "sat", "sat"), unsat("evm_coverage"),
               derived("x86_coverage"), derived("x86_maps_0_0"), derived("pair_0_0"))
    base = InstructionBlockTheorem("id", SPEC, records, tuple(r.name for r in records), "out", 1, 1, True, (), 0,
                                   correspondence=(0,), arity=(1,), cutpoint_manifest=(),
                                   proof_kind=PROOF_KIND, hint_digest="h", chain=((0, ENTRY, ENTRY + 8, 3, 3),),
                                   entry_tags_dead=True)
    return replace(base, **changes)


def test_complete_theorem():
    assert theorem().complete


def with_record(t, name, record):
    records = tuple(record if r.name == name else r for r in t.obligations)
    return replace(t, obligations=records)


@pytest.mark.parametrize("bad", [
    lambda t: replace(t, proof_kind="other"),
    lambda t: replace(t, hint_digest=""),
    lambda t: replace(t, entry_tags_dead=False),
    lambda t: replace(t, chain=()),
    lambda t: replace(t, chain=((1, ENTRY, ENTRY + 8, 3, 3),)),                               # index not from 0
    lambda t: replace(t, chain=((0, ENTRY, ENTRY + 8, 3, 4), (1, ENTRY + 9, ENTRY + 9, 4, 4))),  # gap
    lambda t: replace(t, chain=((0, ENTRY, ENTRY + 8, 3, 4), (1, ENTRY + 8, ENTRY + 9, 5, 5))),  # height break
    # a derived record that does not depend on exactly the leaves
    lambda t: with_record(t, "pair_0_0", Obligation("pair_0_0", "d", "unsat", lemmas=(), required_lemmas=())),
    lambda t: with_record(t, "x86_coverage", unsat("x86_coverage")),
    # a leaf that is not proved (unknown inner query) under a derived record
    lambda t: with_record(t, "x86_maps_0_0", Obligation(
        "x86_maps_0_0", "d", "unsat", lemmas=(Obligation("instruction_0", "leaf", "unsat",
                                                          lemmas=(Obligation("q0", "x", "unknown"),),
                                                          required_lemmas=("q0",)),),
        required_lemmas=("instruction_0",))),
])
def test_incomplete_theorems(bad):
    assert not bad(theorem()).complete


def test_producer_registry():
    t = theorem()
    hints = {10: BlockHint(10, "c0de", (OpHint(0, "TAG", ENTRY, ENTRY + 8, (), ()),), "h")}
    prover = SimpleNamespace(instruction_hints=hints, pc_to_addr={10: ENTRY})
    assert _producer_ok(t, prover, SPEC)
    assert not _producer_ok(replace(t, chain=((0, ENTRY, ENTRY + 4, 3, 3),)), prover, SPEC)          # re-cut chain
    two = {10: BlockHint(10, "c0de", (OpHint(0, "TAG", ENTRY, ENTRY + 8, (), ()),
                                      OpHint(1, "JUMP", ENTRY + 8, ENTRY + 9, (), ())), "h")}
    assert not _producer_ok(t, SimpleNamespace(instruction_hints=two, pc_to_addr={10: ENTRY}), SPEC)  # chain too short
    assert not _producer_ok(t, SimpleNamespace(instruction_hints={}, pc_to_addr={10: ENTRY}), SPEC)  # no hint
    assert not _producer_ok(replace(t, hint_digest="other"), prover, SPEC)                             # other hint
    assert not _producer_ok(t, SimpleNamespace(instruction_hints=hints, pc_to_addr={10: ENTRY + 1}), SPEC)
    assert not _producer_ok(t, prover, replace(SPEC, stack_depth=4))                                   # other depth
    legacy = BlockTheorem(*(getattr(t, f) for f in ("identity", "spec", "obligations", "required", "outcome_digest",
                                                     "evm_count", "x86_count", "finite_execution")))
    assert _producer_ok(legacy, prover, SPEC)

    class Other(BlockTheorem):
        pass
    assert not _producer_ok(Other(*(getattr(legacy, f) for f in ("identity", "spec", "obligations", "required",
                                                                 "outcome_digest", "evm_count", "x86_count",
                                                                 "finite_execution"))), prover, SPEC)


def plan(ops, d0, depth=-2, min_depth=2, facts=()):
    from evm_ir.models import EVMBlock
    from verification.block_relation import BlockRelationSchema
    from verification.instruction_chain import semantic_plan
    block = EVMBlock(0, depth, min_depth, 1024, 0, True, False, False, ops)
    for o in ops:
        o.block = block
    return semantic_plan(SimpleNamespace(schema=BlockRelationSchema(), host_gas_uf_enabled=True), block, d0, facts)


def test_semantic_plan_heights_below_the_entry_depth():
    # Two POPs take the stack below the entry depth: the hint's window is empty there, so only the EVM model can
    # tell the height (1766/5584 failed with a wrong height before).
    from evm_ir.models import EvmOperator
    ops = [EvmOperator("TAG", 0), EvmOperator("POP", 1), EvmOperator("POP", 2), EvmOperator("STOP", 3)]
    heights, facts, problem = plan(ops, 5)
    assert heights == [5, 5, 4, 3] and problem is None and facts == [(), (), (), ()]


def test_semantic_plan_facts_from_push_dup_and_folding():
    # Review z8g: the facts of in-block PUSHes (e.g. a JUMP target, SHA3 offsets) reach later ops; DUP copies them
    # and the entry's constants pass through; ADD of two constants folds to one.
    from evm_ir.models import EvmOperator
    ops = [EvmOperator("TAG", 0), EvmOperator("PUSH", 1, immediate=0x20, param=1),
           EvmOperator("PUSH", 3, immediate=0x40, param=1), EvmOperator("DUP", 5, param=2),
           EvmOperator("ADD", 6), EvmOperator("JUMP", 7)]
    heights, facts, problem = plan(ops, 3, depth=2, min_depth=0, facts=((1, 7),))
    assert problem is None and heights == [3, 3, 4, 5, 6, 5]
    assert facts[2] == ((0, 0x20), (2, 7))                      # after PUSH 0x20; the entry fact moved down
    assert facts[4] == ((0, 0x20), (1, 0x40), (2, 0x20), (4, 7))  # DUP2 copied 0x20
    assert facts[5] == ((0, 0x60), (1, 0x20), (3, 7))           # 0x20 + 0x40 folded
