"""Every child result is tied to its actual parsed, typed v3 assertion vector."""
import io
import json
from pathlib import Path
from time import monotonic
from types import SimpleNamespace

import pytest
import z3 as z
import common.isolated_sat as iso
import verification.block_equivalence as be


def envelope(text,payload='unsat',**changes):
    data={'parsed_alpha':be._parse_transport(text)[1],'payload':payload};data.update(changes)
    return json.dumps(data)


@pytest.mark.parametrize('mode',[{}, {'pure_bv':True}, {'refute_probe':True,'rlimit':1000000}])
def test_valid_digest_preserves_answer_protocol(monkeypatch,mode):
    seen=[]
    def run(command,**kw):
        seen.append(command);return SimpleNamespace(returncode=0,stdout=envelope(kw['input']),stderr='')
    monkeypatch.setattr(iso.subprocess,'run',run)
    assert iso.isolated_sat(z.BoolVal(False),1000,**mode)=='unsat'
    assert len(seen)==1


@pytest.mark.parametrize('wire',['mismatch','missing','legacy','malformed'])
def test_unsat_without_correct_parsed_digest_is_unknown(monkeypatch,wire):
    def run(command,**kw):
        text={'mismatch':envelope(kw['input'],parsed_alpha='transport-v3:'+'0'*64),
              'missing':json.dumps({'payload':'unsat'}),'legacy':'unsat','malformed':'{'}[wire]
        return SimpleNamespace(returncode=0,stdout=text,stderr='')
    monkeypatch.setattr(iso.subprocess,'run',run)
    assert iso.isolated_sat(z.BoolVal(False),1000)=='unknown'


def test_scalar_payload_is_unwrapped_only_after_digest_match(monkeypatch):
    def run(command,**kw):return SimpleNamespace(returncode=0,stdout=envelope(kw['input'],{'answer':'unknown'}),stderr='')
    monkeypatch.setattr(iso.subprocess,'run',run)
    result=iso._run_isolated(z.BoolVal(True),monotonic()+1,scalar_model=True)
    assert json.loads(result.stdout)=={'answer':'unknown'}


def test_unsupported_alpha_and_overloads_never_start_child(monkeypatch):
    called=[];monkeypatch.setattr(iso.subprocess,'run',lambda *a,**k:called.append(1))
    sort=z.DeclareSort('digest_unsupported');u=z.Const('digest_u',sort)
    assert iso.isolated_sat(u==u,1000)=='unknown'
    f=z.Function('digest_overload',z.BitVecSort(8),z.BitVecSort(8));g=z.Function('digest_overload',z.BitVecSort(8),z.BitVecSort(16));x=z.BitVec('digest_x',8)
    assert iso.isolated_sat(z.And(f(x)==1,g(x)==2),1000)=='unknown'
    assert not called


def test_parsed_digest_preserves_aliasing_across_contexts():
    outputs=[]
    for ctx in (z.Context(),z.Context()):
        x=z.BitVec('digest_ctx_x',8,ctx=ctx)
        text=be._to_smt2(x==x);outputs.append(be._parse_transport(text,ctx)[1])
    assert outputs[0]==outputs[1]
    text='(declare-fun f ((_ BitVec 8)) (_ BitVec 8)) (declare-fun x () (_ BitVec 8)) (assert (= (f x) x))'
    a=be._parse_transport(text)[1];b=be._parse_transport(text.replace('(f x) x','(f x) (f x)'))[1]
    assert a!=b


def test_actual_worker_reports_digest_before_solver_rewrites(monkeypatch,capsys):
    # Exercise the actual entrypoint on macOS; only Linux OS-limit setup is stubbed.
    import resource
    text='(declare-fun wire_x () (_ BitVec 8)) (assert (not (= wire_x wire_x)))'
    original=Path.read_text
    monkeypatch.setattr(Path,'read_text',lambda self,*a,**k:'1024 0' if str(self)=='/proc/self/statm' else original(self,*a,**k))
    monkeypatch.setattr(resource,'setrlimit',lambda *a:None)
    monkeypatch.setattr(iso.sys,'argv',['isolated_sat.py','1000','1024','0','0','0'])
    monkeypatch.setattr(iso.sys,'stdin',io.StringIO(text))
    iso._worker();data=json.loads(capsys.readouterr().out)
    assert data=={'parsed_alpha':be._parse_transport(text)[1],'payload':'unsat'}


def test_actual_pair_and_alias_worker_report_parsed_digest():
    text='(assert false)';expected=be._parse_transport(text)[1]
    digest,record=be._check_serialized(text,'digest_pair',1000,None,'digest-pair-node')
    assert digest==expected and record.proved
    digest,record=be._alias_case_serialized(text,'digest_alias',1000,1,'digest-alias-node')
    assert digest==expected and record.proved


@pytest.mark.parametrize('wrong',[False,True])
def test_pair_consumer_rejects_changed_child_digest(monkeypatch,wrong):
    class Future:
        def __init__(self,result):self.value=result
        def done(self):return True
        def result(self,timeout=None):return self.value
    class Pool:
        def submit(self,fn,text,name,*args):
            digest,record=be._check_serialized(text,name,*args)
            return Future(('wrong' if wrong else digest,record))
    monkeypatch.setattr(be,'_pair_pool',lambda:Pool())
    prover=be.BlockEquivalenceProver([],[],{},timeout_ms=1000)
    records=[];answer=list(prover._check_all([('one',z.BoolVal(False),''),('two',z.BoolVal(False),'')],records))
    assert answer==[not wrong,not wrong]
    if wrong:assert all(r.answer=='unknown' for r in records)


@pytest.mark.parametrize('mode',['scalar','refute'])
def test_actual_worker_special_modes_return_the_same_parsed_digest(monkeypatch,capsys,mode):
    import resource
    text='(declare-fun wire_m () (_ BitVec 8)) (assert (= (bvmul wire_m wire_m) #x01))'
    original=Path.read_text
    monkeypatch.setattr(Path,'read_text',lambda self,*a,**k:'1024 0' if str(self)=='/proc/self/statm' else original(self,*a,**k))
    monkeypatch.setattr(resource,'setrlimit',lambda *a:None)
    argv=['isolated_sat.py','1000','1024','0','1000000','0']
    argv += ['1'] if mode=='scalar' else ['0','1',str(monotonic()+1)]
    monkeypatch.setattr(iso.sys,'argv',argv);monkeypatch.setattr(iso.sys,'stdin',io.StringIO(text))
    iso._worker();data=json.loads(capsys.readouterr().out)
    assert data['parsed_alpha']==be._parse_transport(text)[1]
    assert isinstance(data['payload'],dict) if mode=='scalar' else data['payload']=='unknown'


@pytest.mark.parametrize('wrong',[False,True])
def test_alias_consumer_checks_parsed_digest(monkeypatch,wrong):
    class Future:
        def __init__(self,result):self.value=result
        def done(self):return True
        def result(self,timeout=None):return self.value
    class Pool:
        def submit(self,fn,text,name,*args):
            return Future(('bad' if wrong else be._parse_transport(text)[1],be.Obligation(name,'false','unsat')))
    monkeypatch.setattr(be,'_pair_pool',lambda:Pool())
    monkeypatch.setattr(be,'solve_query',lambda *a,**kw:'unknown')
    result=be._refute_alias_queries([('a',z.BoolVal(False)),('b',z.BoolVal(False))],1000,monotonic()+2,None,True)
    assert (result is None)==wrong


def test_transport_preparation_exhaustion_never_starts_child(monkeypatch):
    clock=[0.0];original=be._parse_transport
    def digest(*args,**kw):
        result=original(*args,**kw);clock[0]=2.0;return result
    monkeypatch.setattr(be,'_parse_transport',digest)
    monkeypatch.setattr(iso,'monotonic',lambda:clock[0])
    monkeypatch.setattr(iso.subprocess,'run',lambda *a,**k:pytest.fail('child started after preparation budget'))
    assert iso.isolated_sat(z.BoolVal(False),1000)=='unknown'


def test_untransportable_batch_is_proved_in_process(monkeypatch):
    class Pool:
        def submit(self, *args):
            raise AssertionError("an untransportable batch never reaches the pool")
    monkeypatch.setattr(be, "_pair_pool", lambda: Pool())
    def refuse(formula):
        raise ValueError("SMT2 round trip changed the normalized statement")
    monkeypatch.setattr(be, "_to_smt2", refuse)
    prover = be.BlockEquivalenceProver([], [], {}, timeout_ms=1000)
    records = []
    answer = list(prover._check_all([('one', z.BoolVal(False), ''), ('two', z.BoolVal(True), '')], records))
    assert answer == [True, False] and [r.name for r in records] == ["one", "two"]
