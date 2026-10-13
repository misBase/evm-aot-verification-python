"""Constant-insensitive proof instances (docs/块级实例常量去敏化方案.md §8 T1/T2)."""
import pytest
from z3 import And, BitVec, BitVecVal, Extract, Implies, Solver, Not, substitute, unsat

from evm_ir.json_parser import load_ir_from_json
from evm_ir.models import EVMBlock, EvmOperator
from evm_ir.program import EVMProgram
from verification.block_parallel import proof_groups
from verification.block_relation import BlockRelationSchema, stack_constant_condition
from verification.block_specialization import BlockSpecialization as S, dropped, project, sensitive_slots, weakens


def block(*ops):
    return EVMBlock(pc=1, stack_depth=0, min_depth=0, max_depth=1024, static_gas=0, is_jump_target=True,
                    is_inner_block=False, is_stop=False,
                    operations=[EvmOperator(kind, i, param=param, is_static=static, immediate=imm)
                                for i, (kind, param, static, imm) in enumerate(ops)])


def op(kind, param=None, static=False, imm=None):
    return (kind, param, static, imm)


# ---------------------------------------------------------------- T1

def test_return_block_keeps_the_return_tag_slot():
    # entry: slot0 = result, slot1 = return tag; SWAP1 JUMP returns to slot1.
    assert sensitive_slots(block(op("SWAP", 1), op("JUMP"))) == {1}


def test_static_jump_target_is_not_a_stack_slot():
    assert sensitive_slots(block(op("JUMP", static=True, imm=9))) == frozenset()
    assert sensitive_slots(block(op("JUMPI", static=True, imm=9))) == {0}  # the condition


def test_dup_and_swap_carry_labels_moves_are_not_uses():
    # DUP3 copies slot2, ADD consumes it with slot0; SWAP2/POP only move/discard.
    assert sensitive_slots(block(op("DUP", 3), op("ADD"), op("SWAP", 2), op("POP"))) == {0, 2}
    assert sensitive_slots(block(op("SWAP", 3), op("POP"), op("POP"))) == frozenset()
    # A computed value is not an entry slot.
    assert sensitive_slots(block(op("PUSH", imm=1), op("PUSH", imm=2), op("ADD"), op("MSTORE"))) == {0}


def test_operations_after_the_control_op_are_dead():
    assert sensitive_slots(block(op("JUMP", static=True, imm=9), op("ADD"))) == frozenset()


@pytest.mark.parametrize("stem", ["three_block", "muti_block", "muti_block_08"])
def test_sensitive_slots_lie_inside_the_go_underflow_window(stem):
    # Every consumed entry slot is below the block's minimum depth (Go's TAG check).
    for b in EVMProgram(load_ir_from_json(f"tests/data/{stem}.json")).blocks:
        assert all(i < b.min_depth for i in sensitive_slots(b)), b.pc


def test_projection_weakens_and_drops_exactly_the_rest():
    c = S(7, 4, 96, 128, ((0, 5), (2, 855), (3, 1 << 200)))
    k = project(c, {0, 1})
    assert k == S(7, 4, 96, 128, ((0, 5),)) and weakens(k, c) and dropped(k, c) == ((2, 855), (3, 1 << 200))
    assert weakens(c, c) and dropped(c, c) == ()
    assert not weakens(c, k)  # k has fewer constants
    assert not weakens(S(7, 4, 96, 128, ((0, 6),)), c)  # same index, other value
    for other in (S(8, 4, 96, 128), S(7, 3, 96, 128), S(7, 4, 64, 128), S(7, 4, 96, None)):
        assert not weakens(other, c)


def test_proof_groups_off_is_identity_and_on_groups_by_projection():
    blocks = [block(op("SWAP", 1), op("JUMP"))]  # pc=1, consumes slot 1 only
    a, b = S(1, 3, 0, 0, ((1, 9), (2, 4))), S(1, 3, 0, 0, ((1, 9), (2, 5)))
    c = S(1, 3, 0, 0, ((1, 8), (2, 4)))
    assert proof_groups((a, b, c), blocks, False) == {a: (a,), b: (b,), c: (c,)}
    assert proof_groups((a, b, c), blocks, True) == {S(1, 3, 0, 0, ((1, 9),)): (a, b),
                                                     S(1, 3, 0, 0, ((1, 8),)): (c,)}


# ---------------------------------------------------------------- T2 (Lemma A)

def _valid(formula):
    s = Solver()
    s.add(Not(formula))
    return s.check() == unsat


@pytest.fixture(scope="module")
def havocs():
    schema = BlockRelationSchema()
    c = S(7, 4, 96, 128, ((0, 5), (2, 855), (3, (1 << 200) + 3)))
    k = project(c, {0})
    kw = dict(prefix="blk7_4_96_128", host_gas_uf_enabled=True, assume_calldata_offset_no_overflow=False,
              abstract_calldataload_words=False)
    return schema, c, k, schema.build_havoc(**kw, **k.as_havoc_kwargs()), schema.build_havoc(**kw, **c.as_havoc_kwargs())


def test_lemma_a_havoc_c_is_havoc_k_under_the_dropped_equalities(havocs):
    schema, c, k, hk, hc = havocs
    sk, sc = hk.state, hc.state
    premise_k, premise_c = And(*sk.assumptions), And(*sc.assumptions)
    e_c = stack_constant_condition(sk, sk, dropped(k, c))
    assert _valid(premise_k == premise_c)  # constants add no assumption
    assert _valid(Implies(And(premise_k, e_c), And(sk.evm_stack.Stack == sc.evm_stack.Stack,
                                                   sk.evm_stack.SP == sc.evm_stack.SP,
                                                   sk.x86_memory.stack_mem == sc.x86_memory.stack_mem)))
    # havoc_relation(c) holds on havoc(k) ∧ E_c (relation decomposition, Lemma B).
    goals = schema.relation_goals(sk, sk, c, memory_snapshot=hk.memory_snapshot)
    assert _valid(Implies(And(premise_k, e_c), And(*(g.condition for g in goals))))
    # Without E_c it does not: the dropped constants are what c adds.
    assert not _valid(Implies(premise_k, And(*(g.condition for g in goals))))


def test_lemma_a_every_c_entry_is_a_k_entry(havocs):
    # Covering direction, by substitution: havoc(k)[s_i := v] is havoc(c).
    schema, c, k, hk, hc = havocs
    sk, sc = hk.state, hc.state
    pairs = []
    for index, value in dropped(k, c):
        for limb in range(4):
            name = f"blk7_4_96_128_stack_{c.stack_depth - 1 - index}_z{limb}"
            pairs.append((BitVec(name, 64), Extract(64 * limb + 63, 64 * limb, BitVecVal(value, 256))))
    for left, right in ((sk.evm_stack.Stack, sc.evm_stack.Stack), (sk.x86_memory.stack_mem, sc.x86_memory.stack_mem)):
        assert _valid(substitute(left, *pairs) == right)
    wrong = [(pairs[0][0], pairs[0][1] + 1)] + pairs[1:]
    assert not _valid(substitute(sk.evm_stack.Stack, *wrong) == sc.evm_stack.Stack)
