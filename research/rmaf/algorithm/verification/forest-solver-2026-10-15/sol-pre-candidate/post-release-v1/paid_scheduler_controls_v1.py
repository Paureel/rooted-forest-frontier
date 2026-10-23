#!/usr/bin/env python3
"""Timed actual paid-scheduler scalar fixture controls; not an ordinary solver."""
import json
import os
from pathlib import Path
import subprocess
import sys
import time
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[6];BUILD=HERE/'isolated-build-v1'
mode=sys.argv[1];spec=json.loads((HERE/'PAID-SCHEDULER-EXPECTATIONS-v1.json').read_text())
out=HERE/('paid-scheduler-'+mode+'-v1.json');receipt=HERE/('paid-scheduler-controls-'+mode+'-v1.json')
cmd=[str(ROOT/'bootloops-lean'),'--run',str(HERE/'PaidSchedulerProbe-v1.lean'),mode,str(out)]
result={'mode':mode,'context':'post-contact fixture realization; no full ordinary solver'}
try:
    start=time.perf_counter();p=subprocess.run(cmd,cwd=BUILD,env={**os.environ,'LEAN_PATH':str(BUILD)},text=True,capture_output=True,timeout=30)
    result['command']={'args':cmd,'seconds':time.perf_counter()-start,'returncode':p.returncode,'stdout':p.stdout,'stderr':p.stderr}
    assert p.returncode==0
    rows=json.loads(out.read_text());expected={r['id']:r for r in spec['cases']}
    assert len(rows)==(1 if mode=='pilot' else 4)
    for r in rows:
        e=expected[r['id']]
        for k in ['calls','answers','recursiveWork']:assert r[k]==e[k],r['id']+' mismatch '+k
        assert [pb[1] for pb in r['queries']]==e['calls']
        assert r['callerWork']>0
    if mode=='full':
        actual=next(r['calls'] for r in rows if r['id']==spec['false_twin']['id'])
        try:assert actual==spec['false_twin']['wrong_own_discount_calls']
        except AssertionError:result['false_own_minimum_discount']={'caught':True,'actual':actual,'false':spec['false_twin']['wrong_own_discount_calls']}
        else:raise AssertionError('own discount false twin survived')
    result['passed']=True
except Exception as exc:
    result['passed']=False;result['failure']=repr(exc);raise
finally:receipt.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'passed':True,'mode':mode,'seconds':result['command']['seconds'],'rows':len(rows)}))
