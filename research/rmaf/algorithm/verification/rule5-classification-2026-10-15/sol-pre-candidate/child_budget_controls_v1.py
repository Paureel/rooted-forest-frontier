#!/usr/bin/env python3
"""One-shot finite exact-child tables; these fixtures do not implement recursion."""
import importlib.util
import json
from pathlib import Path
import sys
import time
HERE=Path(__file__).resolve().parent
ms=importlib.util.spec_from_file_location('own_BFS_child',HERE/'reused/graph_partition_v2.py')
graph=importlib.util.module_from_spec(ms);ms.loader.exec_module(graph)
spec=json.loads((HERE/'CHILD-BUDGET-SUPPLEMENT-v1.json').read_text())
inputs=json.loads((HERE/'FIXTURE-INPUTS-v1.json').read_text())
mode=sys.argv[1];out={'candidate_contact':False,'context':spec['context'],'mode':mode,'queries':[],'false_twins':[]}
start=time.perf_counter()


def solve(table,budget):
    available=[F for F in table['compatibleAF'] if len(F)-table['sourceCount']<=budget]
    return min(available,key=len) if available else None
def same(a,b):assert a==b
def caught(name,call):
    try:call()
    except AssertionError:out['false_twins'].append({'name':name,'caught':True})
    else:raise AssertionError('surviving child-budget false twin '+name)


try:
    assert mode in ('pilot','full')
    refs={name:json.loads((HERE/('REFERENCE-'+name+'-full-v1.json')).read_text()) for name in spec['literal_child_minima']}
    cases={c['id']:c for c in inputs['cases']}
    selected=spec['queries'][:3] if mode=='pilot' else spec['queries']
    for row in selected:
        table=next(c for c in refs[row['case']]['children'] if c['id']==row['child'])
        answer=solve(table,row['remaining']);assert (answer is not None)==row['success']
        assert table['minimumAdditionalCost']==row['minimumAdditionalCost']
        assert row['rootBudget']-row['paid']==row['remaining']
        if answer is not None:
            state=graph.State(cases[row['case']]['target'],table['sourceForest'])
            assert state.agrees(answer) and len(answer)>=table['sourceCount']
            actual_min=len(answer)-table['sourceCount'];assert actual_min==row['minimumAdditionalCost']<=row['remaining']
            assert row['paid']+actual_min==len(answer)-1<=row['rootBudget']
        else:assert all(len(F)-table['sourceCount']>row['remaining'] for F in table['compatibleAF'])
        out['queries'].append({**row,'answer':answer})
    if mode=='full':
        e=spec['zero_child_plant'];state=graph.State(e['T'],e['ss'])
        assert state.proper and state.agrees(e['F']) and len(e['F'])-len(e['ss'])==0
        calls=[] if e['rootBudget']<e['paid'] else [e['rootBudget']-e['paid']]
        assert len(calls)==e['expectedCalls']==0
        caught('Nat_underflow_unpaid_success',lambda:same(e['paid']+(len(e['F'])-len(e['ss']))<=e['rootBudget'],True))
        caught('own_minimum_discount',lambda:same(6-2-4,4))
        table=refs['outside10']['children'][-1]
        caught('child_minimum_shift',lambda:same(solve(table,3) is not None,True))
        assert len(out['queries'])==33 and {r['name'] for r in out['false_twins']}==set(spec['false_twins'])
    out['passed']=True
except Exception as exc:
    out['passed']=False;out['failure']=repr(exc);raise
finally:
    out['seconds']=time.perf_counter()-start
    (HERE/('child-budget-'+mode+'-v1.json')).write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'passed':True,'mode':mode,'queries':len(out['queries']),'false_twins':len(out['false_twins']),'seconds':out['seconds']}))
