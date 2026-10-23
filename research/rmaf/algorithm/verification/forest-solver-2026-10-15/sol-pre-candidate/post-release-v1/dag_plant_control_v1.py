#!/usr/bin/env python3
"""Post-contact binder-preserving DAG qualifier, with a caught alpha-collapse."""
from copy import deepcopy
import json
import os
from pathlib import Path
import subprocess
import time
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[6];TOY=HERE/'producer-toys'
env={**os.environ,'LEAN_PATH':str(TOY)}
out=HERE/'dag-plant-occurrences-v1.json'
result={'context':'post-contact representation qualification','commands':[]}


def binder_gate(dag):
    assert dag['encoding']=='exact-Expr-DAG-v1'
    nodes=dag['nodes']
    found={row[1]:i for i,row in enumerate(nodes) if row[0]=='lam'}
    assert '`alpha' in found and '`beta' in found, 'different binder names were collapsed'
    assert found['`alpha']!=found['`beta'], 'alpha-equivalent binders share a node'
    child_positions={'app':[1,2],'lam':[2,3],'forallE':[2,3],'letE':[2,3,4],'mdata':[2],'proj':[3]}
    for i,row in enumerate(nodes):
        for pos in child_positions.get(row[0],[]):assert 0<=row[pos]<i, 'DAG child index not earlier'


try:
    for cmd in [[str(ROOT/'bootloops-lean'),'-o','DAGPlant.olean','DAGPlant.lean'],
                [str(ROOT/'bootloops-lean'),'--run',str(HERE/'producer_audit_v4.lean'),
                 'DAGPlant',str(out),'DAGPlant']]:
        start=time.perf_counter();p=subprocess.run(cmd,cwd=TOY,env=env,text=True,capture_output=True,timeout=30)
        result['commands'].append({'command':cmd,'returncode':p.returncode,'seconds':time.perf_counter()-start,
                                  'stdout':p.stdout,'stderr':p.stderr})
        assert p.returncode==0,'DAG plant compile/audit failed'
    data=json.loads(out.read_text());body=next(r['actual']['body'] for r in data['occurrences'] if r['name']=='DAGPlant.pairFns')
    binder_gate(body)
    bad=deepcopy(body)
    alpha=next(row for row in bad['nodes'] if row[0]=='lam' and row[1]=='`alpha')
    j=next(i for i,row in enumerate(bad['nodes']) if row[0]=='lam' and row[1]=='`beta')
    bad['nodes'][j]=deepcopy(alpha)
    try:binder_gate(bad)
    except AssertionError as exc:result['alpha_collapse_false_twin']={'caught':True,'message':str(exc)}
    else:raise AssertionError('alpha-collapse plant survived')
    result['passed']=True;result['body_nodes']=len(body['nodes'])
except Exception as exc:
    result['passed']=False;result['failure']=repr(exc);raise
finally:(HERE/'dag-plant-control-v1.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'passed':True,'body_nodes':result['body_nodes'],'alpha_collapse_caught':True}))
