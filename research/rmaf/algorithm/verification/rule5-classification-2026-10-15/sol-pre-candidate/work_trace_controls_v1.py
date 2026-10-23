#!/usr/bin/env python3
"""One-shot public source-semantics counter controls; no candidate work code."""
import json
from pathlib import Path
import sys
import time
HERE=Path(__file__).resolve().parent
SPEC=json.loads((HERE/'WORK-TRACE-EXPECTATIONS-v1.json').read_text())
MODE=sys.argv[1]


def size(t):return 1 if type(t) is int else 1+size(t[0])+size(t[1])
def full(T,S):
    if type(T) is list and type(S) is list:
        return 1+sum(full(t,s) for t in T for s in S)
    return 1
def actual(T,S):
    calls=0
    def compare(t,s):
        nonlocal calls
        calls+=1
        if type(t) is int and type(s) is int:return t==s
        if type(t) is list and type(s) is list:
            return (compare(t[0],s[0]) and compare(t[1],s[1])) or (compare(t[0],s[1]) and compare(t[1],s[0]))
        return False
    return compare(T,S),calls
def restrict(t,X):
    units=0
    def visit(v):
        nonlocal units
        units+=1
        if type(v) is int:
            for x in X:
                units+=1
                if x==v:return v
            return None
        left,right=visit(v[0]),visit(v[1])
        if left is None:return right
        if right is None:return left
        return [left,right]
    return visit(t),units
def same(a,b):assert a==b


result={'context':SPEC['context'],'candidate_contact':False,'mode':MODE,'comparisons':[],'restrictions':[],'false_twins':[]}
start=time.perf_counter()
try:
    assert MODE in ('pilot','full')
    for e in (SPEC['comparison_cases'][:2] if MODE=='pilot' else SPEC['comparison_cases']):
        answer,calls=actual(e['T'],e['S']);trace=full(e['T'],e['S']);product=size(e['T'])*size(e['S'])
        assert answer==e['result'] and calls==e['actual_short_circuit_calls'] and trace==e['four_way_calls'] and product==e['size_product']
        assert calls<=trace<=product
        result['comparisons'].append({'id':e['id'],'actual':calls,'four_way':trace,'size_product':product})
    for e in (SPEC['restriction_cases'][:1] if MODE=='pilot' else SPEC['restriction_cases']):
        answer,units=restrict(e['T'],e['X']);envelope=size(e['T'])*(len(e['X'])+1)
        assert answer==e['result'] and units==e['visits_plus_membership_comparisons'] and envelope==e['envelope']
        assert units<=envelope
        result['restrictions'].append({'id':e['id'],'visits_plus_scans':units,'envelope':envelope})
    mutations=[('four_way_equals_actual',lambda:same(5,3)),('zero_leaf_comparison',lambda:same(actual(0,0)[1],0)),
               ('free_membership_scan',lambda:same(restrict([0,1],[99,0,1])[1],3)),
               ('free_empty_restriction_visit',lambda:same(restrict([0,1],[])[1],0))]
    for name,call in (mutations[:1] if MODE=='pilot' else mutations):
        try:call()
        except AssertionError:result['false_twins'].append({'name':name,'caught':True})
        else:raise AssertionError('surviving cost false twin '+name)
    result['passed']=True
except Exception as exc:
    result['passed']=False;result['failure']=repr(exc);raise
finally:
    result['seconds']=time.perf_counter()-start
    (HERE/('work-trace-'+MODE+'-v1.json')).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'passed':True,'mode':MODE,'seconds':result['seconds'],'comparisons':len(result['comparisons']),'restrictions':len(result['restrictions']),'false_twins':len(result['false_twins'])}))
