"""Candidate discovery is not a reachability or closure proof."""
from z3 import BoolVal, Int, Or

from verification.block_program import BlockProgramVerifier
from verification.block_relation import BlockRelationSchema
from verification.block_specialization import BlockSpecialization


def verifier():
    v = BlockProgramVerifier()
    v._return_tags = {2112}
    v._discovery_cache = {}
    v._parameter_domains = {}
    v._discovery_queries = 0
    return v


def test_literal_depth_candidates_need_no_joint_solver(monkeypatch):
    v = verifier()
    state = BlockRelationSchema().build_havoc(3, memory_size=None,
        free_memory_pointer=None, stack_constants=((2, 2112),)).state
    def forbidden(*args):
        raise AssertionError("literal depth should not solve joint feasibility")
    monkeypatch.setattr("verification.block_program._solver", forbidden)
    assert v._discover(42, state, BoolVal(True), lambda: None) == (
        BlockSpecialization(42, 3, None, None, ((2, 2112),)),)
    assert v._discover(42, state, BoolVal(False), lambda: None) == ()
    assert v._discovery_queries == 0


def test_symbolic_depth_still_enumerates_complete_domain():
    v = verifier()
    state = BlockRelationSchema().build_havoc(0, memory_size=0,
        free_memory_pointer=0).state
    state.evm_stack.SP = Int("candidate_depth")
    values = v._discover(42, state, Or(state.evm_stack.SP == 0,
        state.evm_stack.SP == 1), lambda: None)
    assert {s.stack_depth for s in values} == {0, 1}
    assert v._discovery_queries == 3


def test_literal_buffer_is_retained_and_changing_counter_widens_once():
    v = verifier()
    schema = BlockRelationSchema()
    def discover(value):
        state = schema.build_havoc(3, memory_size=96, free_memory_pointer=128,
            stack_constants=((0, value), (2, 2112))).state
        return v._discover(42, state, BoolVal(True), lambda: None)[0]
    assert discover(128).stack_constants == ((0, 128), (2, 2112))
    assert discover(129).stack_constants == ((2, 2112),)
    assert discover(130).stack_constants == ((2, 2112),)
    assert discover(128).stack_constants == ((2, 2112),)
    assert discover(131).memory_size == 96


def test_memory_parameters_stay_concrete_up_to_the_limit_then_widen():
    v = verifier()
    v.max_parameter_values = 2
    schema = BlockRelationSchema()

    def discover(msize, fmp):
        state = schema.build_havoc(3, memory_size=msize, free_memory_pointer=fmp,
            stack_constants=((2, 2112),)).state
        spec = v._discover(42, state, BoolVal(True), lambda: None)[0]
        return spec.memory_size, spec.free_memory_pointer

    assert discover(96, 128) == (96, 128)
    assert discover(160, 192) == (160, 192)
    assert discover(96, 128) == (96, 128)      # already seen: still concrete
    assert discover(224, 256) == (None, None)  # third distinct value widens
    assert discover(96, 128) == (None, None)   # widened contexts stay TOP (finite)


def _blocks():
    from evm_ir.models import EVMBlock, EvmOperator

    def block(pc, ops, jump_target=True):
        b = EVMBlock(pc, 0, 0, 1024, 0, jump_target, False, False)
        b.operations = [EvmOperator(kind, pc + i, **kw) for i, (kind, kw) in enumerate(ops)]
        return b

    return [
        # caller: PUSH return address 0x20, call 0x40 statically
        block(0x00, [("PUSH", dict(immediate=0x20, param=1)), ("PUSH", dict(immediate=7, param=1)),
                     ("JUMP", dict(immediate=0x40, is_static=True))], jump_target=False),
        block(0x20, [("TAG", {}), ("STOP", {})]),
        block(0x30, [("TAG", {}), ("PUSH", dict(immediate=0x50, param=1)), ("JUMP", dict(immediate_set=[0x60]))]),
        # callee return: dynamic JUMP that Go left unresolved (empty immediate_set)
        block(0x40, [("TAG", {}), ("POP", {}), ("JUMP", {})]),
        block(0x50, [("TAG", {}), ("STOP", {})], jump_target=False),  # 0x50 is no JUMPDEST
        block(0x60, [("TAG", {}), ("STOP", {})]),
    ]


def test_pushed_code_addresses_are_pushed_jumpdests_only():
    from verification.block_program import pushed_code_addresses
    # 0x20: return address pushed for a call; 7: data; 0x50: not a JUMPDEST;
    # 0x40/0x60 are jump targets but only carried by JUMPs, never pushed.
    assert pushed_code_addresses(_blocks()) == {0x20}


def test_pushed_code_return_tag_survives_constant_widening():
    """A return address whose JUMP has no immediate_set widens away by default
    (the return JUMP then forks to the complete jump domain); as a return tag
    it stays, and the changing non-return constant still widens once."""
    schema = BlockRelationSchema()

    def run(tags):
        v = verifier()
        v._return_tags = tags
        out = []
        for counter in (5, 6, 7):
            state = schema.build_havoc(3, memory_size=None, free_memory_pointer=None,
                stack_constants=((0, counter), (1, 0x20))).state
            out.append(v._discover(42, state, BoolVal(True), lambda: None)[0].stack_constants)
        return out

    assert run({2112}) == [((0, 5), (1, 0x20)), (), ()]
    assert run({2112, 0x20}) == [((0, 5), (1, 0x20)), ((1, 0x20),), ((1, 0x20),)]


def test_pushed_code_return_tags_switch_defaults_off_and_unions_in_setup():
    from pathlib import Path
    from time import monotonic
    from verification.block_parallel import build_inputs
    from verification.block_program import BlockProgramResult, pushed_code_addresses
    # muti_block_08 pushes 5 JUMPDESTs that no immediate_set lists
    stem = Path(__file__).resolve().parents[1] / "data" / "muti_block_08"
    options = dict(gas_check="off", gas_budget=10**9, num_inputs=0, timeout_ms=3000, max_depth=400,
                   max_instances=64, wall_seconds=60, summaries=False, node_seconds=60,
                   max_parameter_values=8, first_pass_node_seconds=None)
    tags = {}
    for flag in (None, True):
        if flag is not None:
            options["pushed_code_return_tags"] = flag
        evm, x86, initial, v = build_inputs(stem, options)
        assert v.pushed_code_return_tags is bool(flag)
        setup = v._setup(evm, x86, initial, BlockProgramResult(), monotonic(), [])
        tags[flag] = set(v._return_tags)
    immediate = {t for b in setup.evm for op in b.operations for t in (op.immediate_set or ())}
    assert tags[None] == immediate
    assert pushed_code_addresses(setup.evm) - immediate
    assert tags[True] == immediate | pushed_code_addresses(setup.evm)


def test_terminal_block_detection_follows_the_live_control_op():
    from verification.block_specialization import terminal_block
    blocks = {b.pc: b for b in _blocks()}
    assert terminal_block(blocks[0x20]) and terminal_block(blocks[0x60])
    assert not terminal_block(blocks[0x00]) and not terminal_block(blocks[0x40])
    from evm_ir.models import EVMBlock, EvmOperator
    falls_through = EVMBlock(0x70, 0, 0, 1024, 0, True, False, False)
    falls_through.operations = [EvmOperator("TAG", 0x70), EvmOperator("PUSH", 0x71, immediate=1, param=1)]
    assert not terminal_block(falls_through)


def _projection_verifier(**flags):
    v = BlockProgramVerifier(**flags)
    v._return_tags = {2112}
    v._discovery_cache, v._parameter_domains, v._constant_domains = {}, {}, {}
    v._discovery_queries = 0
    return v


def test_terminal_projection_registers_a_weakening_with_consumed_constants_only():
    from dataclasses import replace
    from verification.block_specialization import weakens
    v = _projection_verifier(terminal_constant_projection=True)
    v._terminal_slots = {42: frozenset({0})}
    state = BlockRelationSchema().build_havoc(3, memory_size=96, free_memory_pointer=128,
        stack_constants=((0, 7), (1, 9), (2, 2112))).state
    spec = v._discover(42, state, BoolVal(True), lambda: None)[0]
    full = BlockSpecialization(42, 3, 96, 128, ((0, 7), (1, 9), (2, 2112)))
    assert spec == BlockSpecialization(42, 3, 96, 128, ((0, 7),))  # even the return tag: no successor
    assert weakens(spec, full)
    assert v._discover(43, state, BoolVal(True), lambda: None)[0] == replace(full, pc=43)  # other blocks unchanged


def test_context_projection_keeps_return_tags_and_consumed_constants():
    import pytest
    from verification.block_specialization import weakens
    with pytest.raises(ValueError, match="requires pushed_code_return_tags"):
        BlockProgramVerifier(context_constant_projection=True)
    v = _projection_verifier(pushed_code_return_tags=True, context_constant_projection=True)
    v._block_slots = {42: frozenset({0})}
    schema = BlockRelationSchema()

    def discover(moved):
        state = schema.build_havoc(3, memory_size=None, free_memory_pointer=None,
            stack_constants=((0, 7), (1, moved), (2, 2112))).state
        return v._discover(42, state, BoolVal(True), lambda: None)[0]

    first = discover(9)
    assert first.stack_constants == ((0, 7), (2, 2112))
    assert weakens(first, BlockSpecialization(42, 3, None, None, ((0, 7), (1, 9), (2, 2112))))
    # a changing constant the block only moves no longer widens the consumed one away
    assert discover(10).stack_constants == ((0, 7), (2, 2112))
