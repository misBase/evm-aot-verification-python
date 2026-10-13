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
