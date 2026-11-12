"""Derived audit metadata survives native evidence transport without granting proofs."""
from dataclasses import replace
import pickle
from types import SimpleNamespace

import z3 as z
import verification.block_equivalence as be
import verification.block_parallel as bp
from verification.cutpoint_relation import RelationGoal


def test_store_view_records_expose_all_source_dependencies():
    mem=z.Array('pr_mem',z.BitVecSort(64),z.BitVecSort(8))
    base,a,r,i=z.BitVecs('pr_base pr_a pr_r pr_i',64);flag=z.Bool('pr_flag')
    logical=z.Store(mem,a,z.If(flag,z.BitVecVal(255,8),z.BitVecVal(0,8)))
    physical=z.Store(z.Lambda(i,z.Select(mem,i-base)),base+a,z.BitVecVal(255,8))
    _,answer,records=be.refute_store_views(z.And(flag,z.Select(logical,r)!=z.Select(physical,base+r)),3000)
    assert answer=='unsat'
    rows=be.obligation_provenance(records)
    reads=[x for x in rows if x['provenance']=='store_view_congruence']
    assert reads and all(x['sources'] and tuple(x['sources'])==x['required_lemmas'] for x in reads)


def test_generalized_schema_and_instantiation_provenance():
    c=z.Bool('pr_c');p,b=z.BitVecs('pr_p pr_b',64)
    old=z.If(c,z.BitVecVal(0,64),p-b);new=z.If(c,b,p)-b
    records=be._schema_identity_proof(old,new)
    assert records and records[0].provenance=='solver_generalized_identity'
    assert all(r.proved for r in records)
    wrapped=be.Obligation('instance',z.Not(old==new).sexpr(),'unsat',lemmas=records,
                          provenance='telescope_identity_instantiation')
    assert {r['provenance'] for r in be.obligation_provenance([wrapped])}=={'telescope_identity_instantiation','solver_generalized_identity'}


def test_shared_edge_provenance_preserves_sources_through_slim_pickle():
    x=z.BitVec('pr_shared_x',8);goal=x==x
    source=be.Obligation('checked_common',z.Not(goal).sexpr(),'unsat')
    shared={'bases':{goal.get_id():z.BoolVal(True)},'done':{goal.get_id():[source]}}
    record=bp.close_edge(be.BlockEquivalenceProver([],[],{},timeout_ms=1000),'H2_pr',z.BoolVal(True),
                         [('target',(RelationGoal('gas',goal),))],shared)
    assert record.proved and record.provenance=='h2_shared_weakening'
    restored=pickle.loads(pickle.dumps(bp.slim(record)))
    assert restored.provenance==record.provenance and restored.lemmas[0].name=='checked_common'
    assert be.obligation_provenance([restored])[0]['sources']==['checked_common']
    assert not replace(record,answer='unknown').proved
    assert not be.Obligation('fake','false','unknown',provenance='prefix_tree_coverage').proved


def test_prefix_tree_coverage_record_has_derivation_metadata(monkeypatch):
    x=z.Bool('pr_tree');prover=be.BlockEquivalenceProver([],[],{},timeout_ms=1000)
    state=SimpleNamespace(assumptions=(),pending_errors=(),pending_constraints=())
    paths=[SimpleNamespace(condition=x,kind='exit',state=state),SimpleNamespace(condition=z.Not(x),kind='exit',state=state)]
    monkeypatch.setattr(be,'solve_query',lambda *a,**k:'unknown')
    records=[]
    prover.check_paths(paths,paths,z.BoolVal(True),state,records)
    roots=[r for r in records if r.name.endswith('_coverage')]
    assert roots and all(r.provenance=='prefix_tree_coverage' and r.proved for r in roots)
