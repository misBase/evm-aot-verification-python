"""An external digest memo must own its native-ID inputs until clear."""
import json
import os
from pathlib import Path
import subprocess
import sys
import textwrap

import pytest
import verification.block_equivalence as be


@pytest.mark.parametrize('legacy', [False, True])
def test_external_term_digest_memo_keeps_identity(legacy):
    code=textwrap.dedent('''
        import gc,json,os,weakref
        from pathlib import Path
        import z3 as z
        def forbidden(*args,**kwargs): raise AssertionError('Solver.check forbidden')
        z.Solver.check=forbidden
        import verification.block_equivalence as be
        assert Path(be.__file__).resolve()==Path(os.environ['DIGEST_EXPECTED_MODULE']).resolve()
        with be.z3_memory_cap(256):
            x=z.BitVec('external_digest_live_x',64)
            old=x+1
            memo={}
            be.term_digest(old,memo)
            legacy=os.environ['DIGEST_LEGACY']=='1'
            if legacy:
                # Exact hashes produced by the actual helper, but an old unanchored table shape.
                copied={k:v for k,v in memo.items() if isinstance(k,tuple)}
                memo.clear()
                memo=copied
            old_ref=weakref.ref(old)
            del old
            gc.collect()
            was_dead=old_ref() is None
            for n in range(2,65):
                term=x+n
                actual=be.term_digest(term,memo)
                expected=be.term_digest(term,{})
                assert actual==expected, f'n={n}: shared memo disagrees with fresh digest'
                del term
                gc.collect()
            if not legacy:
                assert old_ref() is not None, 'Memo did not own the old source wrapper'
            else:
                assert was_dead, 'Legacy table must have no hidden root ownership'
            memo.clear()
            gc.collect()
            assert old_ref() is None
            print(json.dumps(dict(legacy=legacy,checked_new_terms=63,old_wrapper_initially_dead=was_dead,
                                  shared_fresh_equal=True,roots_released_after_clear=True)),flush=True)
    ''')
    source=Path(be.__file__).resolve().parents[1]
    env=os.environ.copy();env.pop('BLOCK_PROOF_CACHE',None)
    env['PYTHONPATH']=str(source)+os.pathsep+env.get('PYTHONPATH','')
    env['DIGEST_EXPECTED_MODULE']=str(Path(be.__file__).resolve());env['DIGEST_LEGACY']=str(int(legacy))
    child=subprocess.run([sys.executable,'-c',code],cwd=source,env=env,text=True,
                         stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=8)
    assert child.returncode==0,child.stdout+'\n'+child.stderr
    receipt=json.loads(child.stdout.strip().splitlines()[-1])
    assert receipt['shared_fresh_equal'] and receipt['roots_released_after_clear']
