"""A warm private equality cache must not bypass foreign-Context rejection."""
import json
import os
from pathlib import Path
import subprocess
import sys
import textwrap

import verification.block_equivalence as be


def test_positive_equality_cache_is_context_scoped():
    # A fresh interpreter avoids dependence on the full suite's hot main-Context IDs.
    code = textwrap.dedent('''
        import gc, json, os
        from pathlib import Path
        from time import monotonic
        import z3 as z
        import verification.block_equivalence as be
        assert Path(be.__file__).resolve() == Path(os.environ['BE_CACHE_EXPECTED_MODULE']).resolve()
        a,b=z.BitVecs('context_cache_a context_cache_b',8)
        premise=a==b
        cache={}
        with be.z3_memory_cap(256):
            seed=be._prove_equal(premise,a,b,1000,monotonic()+3,cache)
            assert seed is not None
            assert be._prove_equal(premise,a,b,1000,monotonic()+3,cache) is seed
            wanted=(tuple(sorted((a.get_id(),b.get_id()))),premise.get_id())
            found=False
            for count in range(65):
                ctx=z.Context()
                padding=[z.BitVec(f'padding_{i}',8,ctx=ctx) for i in range(count)]
                x,y=z.BitVecs('context_cache_x context_cache_y',8,ctx=ctx)
                other=x!=y
                if (tuple(sorted((x.get_id(),y.get_id()))),other.get_id())==wanted:
                    found=True
                    break
                del other,x,y,padding,ctx
                gc.collect()
            assert found, 'No natural ID match in bounded fresh-interpreter control'
            solver=z.Solver(ctx=ctx)
            solver.set(timeout=2000,rlimit=100000,random_seed=0,max_memory=256)
            solver.add(other,x!=y)
            assert solver.check()==z.sat
            try:
                result=be._prove_equal(other,x,y,1000,monotonic()+3,cache)
                returned_none=result is None
                mode='return'
            except (z.Z3Exception,TypeError):
                returned_none=True
                mode='original foreign-Context rejection'
            print(json.dumps(dict(matched_padding=count,xy_ids=list(wanted[0]),premise_id=wanted[1],
                                  raw_other='sat',same_context_cache_kept=True,
                                  foreign_context_failclosed=returned_none,mode=mode)),flush=True)
            assert returned_none, 'Warm cache returned a proof from another Context'
    ''')
    source=Path(be.__file__).resolve().parents[1]
    environment=os.environ.copy()
    environment.pop('BLOCK_PROOF_CACHE',None)
    environment['PYTHONPATH']=str(source)+os.pathsep+environment.get('PYTHONPATH','')
    environment['BE_CACHE_EXPECTED_MODULE']=str(Path(be.__file__).resolve())
    child=subprocess.run([sys.executable,'-c',code],cwd=source,env=environment,text=True,
                         stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=10)
    assert child.returncode==0, child.stdout+'\n'+child.stderr
    receipt=json.loads(child.stdout.strip().splitlines()[-1])
    assert receipt['foreign_context_failclosed'] and receipt['same_context_cache_kept']
