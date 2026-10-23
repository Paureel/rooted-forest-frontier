#!/usr/bin/env python3
"""One-shot mock exact-child fixture test; no complete solver is implemented."""
import copy, hashlib, json
from pathlib import Path
import graph_gate_v2 as graph
HERE=Path(__file__).resolve().parent
d=json.loads((HERE/'CHILD-FIXTURE-v1.json').read_text())
c=next(c for c in graph.EXPECT['cases'] if c['id']==d['case'])
T,S=graph.tree(c['T']),graph.tree(c['S'])
AF=graph.all_agreements(T,S)
def exact_fixture_solver(child,r):
    return child['G'] if r>=child['minimum_residual'] else None
def check_solver(child,r,result):
    C=graph.make_child(S,child['P'],child['paid']); graph.validate_child(S,C)
    feasible=[F for F in AF if graph.refines(F,child['P'])]
    minimum=min(map(len,feasible))
    if minimum!=child['minimum_blocks'] or minimum-len(C['P'])!=child['minimum_residual']: raise ValueError('free/wrong minimum')
    affordable=any(len(F)-len(C['P'])<=r for F in feasible)
    if (result is not None)!=affordable: raise ValueError('affordable completeness/refusal')
    if result is not None and (not graph.agreement(T,S,result) or not graph.refines(result,C['P']) or len(result)!=minimum or len(result)-len(C['P'])>r): raise ValueError('attainment/child/budget')
def child_call(child,k):
    r=graph.remaining(k,child['paid'])
    return None if r is None else exact_fixture_solver(child,r)
checks=[]
for child in d['children']:
    for r in range(4):
        F=exact_fixture_solver(child,r); check_solver(child,r,F)
        checks.append({'child':child['id'],'remaining':r,'success':F is not None,'G':F})
parent=[]
for k in range(4):
    out=[G for ch in d['children'] if (G:=child_call(ch,k)) is not None]
    ok=bool(out); best=min(map(len,out)) if out else None
    assert ok==d['parent_success'][k] and best==d['parent_minimum_blocks'][k]
    parent.append({'k':k,'success':ok,'minimum_blocks':best})
a,b,p=d['children']; caught=[]
def catch(name,fn):
    try: fn()
    except (ValueError,AssertionError) as ex: caught.append({'plant':name,'reason':str(ex)})
    else: raise AssertionError('child mutation survived '+name)
free=copy.deepcopy(a); free['minimum_blocks']=1
catch('free-known-minimum',lambda:check_solver(free,1,a['G']))
catch('wrong-child',lambda:check_solver(a,1,b['G']))
catch('wrong-residual-budget',lambda:check_solver(a,0,a['G']))
catch('missing-refusal',lambda:check_solver(b,0,None))
def bad_parent():
    if child_call(p,1) is None: raise ValueError('unaffordable parent rejected before subtraction')
catch('unaffordable-success',bad_parent)
double=copy.deepcopy(a); double['paid']=2
catch('double-proof-split',lambda:check_solver(double,1,a['G']))
assert {x['plant'] for x in caught}==set(d['false_tables'])
out={'scope':'mock exact tables only; finite fixture, no recursive implementation/IH/termination proof','checks':checks,'parent':parent,'mutations':caught,'required_mutations':6,'candidate_contact':False,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'fixture_sha256':hashlib.sha256((HERE/'CHILD-FIXTURE-v1.json').read_bytes()).hexdigest()}
(HERE/'child-fixture-run1.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'child_calls':len(checks),'parent_budgets':len(parent),'caught':len(caught),'required':6}))
