#!/usr/bin/env python3
"""One-shot exact standard-axiom allowlist positive/false-twin toy."""
import json
import os
from pathlib import Path
import subprocess
import time
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[5]
TOY=HERE/'toy-src'
env={**os.environ,'LEAN_PATH':str(TOY)}
spec=json.loads((HERE/'EXPECTATIONS-v4-supplement.json').read_text())
result={'commands':[]}
try:
    path=HERE/'toy-standard-axioms-origin-v1.json'
    commands=[
      [str(ROOT/'bootloops-lean'),'-o','StandardAxioms.olean','StandardAxioms.lean'],
      [str(ROOT/'bootloops-lean'),'--run',str(HERE/'origin_audit_v2.lean'),
       'StandardAxioms',str(path),'StandardAxioms']]
    for cmd in commands:
        started=time.perf_counter()
        p=subprocess.run(cmd,cwd=TOY,env=env,text=True,capture_output=True,timeout=30)
        result['commands'].append({'command':cmd,'returncode':p.returncode,
          'seconds':time.perf_counter()-started,'stdout':p.stdout,'stderr':p.stderr})
        assert p.returncode==0, 'standard toy compile/audit failure'
    data=json.loads(path.read_text())
    actual=sorted({a for r in data['records'] for a in r['axioms']})
    assert actual==spec['std_axiom_union'], 'exact standard axiom union mismatch'
    result['standard_axiom_union']=actual
    allow=set(spec['std_axiom_union'])
    assert all(not(set(r['axioms'])-allow) for r in data['records']), 'clean axiom twin rejected'
    corrupted=[*data['records'][0]['axioms'],'sorryAx']
    try:
        assert not(set(corrupted)-allow), 'unapproved axiom sorryAx'
    except AssertionError as exc:
        result['false_twin']={'caught':True,'message':str(exc)}
    else:
        raise AssertionError('false axiom twin survived')
    result['passed']=True
except Exception as exc:
    result['passed']=False;result['failure']=repr(exc)
    raise
finally:
    (HERE/'standard-axiom-control-v1.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'passed':True,'standard_axiom_union':actual,'false_twin_caught':True}))
