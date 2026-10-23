#!/usr/bin/env python3
"""One-shot prerelease universal finite replacement and cost controls.

Runtime fixture branches are literal frozen data, generated without an optimum
witness. Enumeration here is verification only; it is never a runtime oracle.
Uses only this review's fresh graph instrument.
"""
from copy import deepcopy
from fractions import Fraction
import json
from pathlib import Path
import time
from graph_partition_v2 import State, Graph, equal, expect_caught, mass

HERE=Path(__file__).resolve().parent
spec=json.loads((HERE/'EXPECTATIONS-v1.json').read_text())
extra=json.loads((HERE/'EXPECTATIONS-v4-supplement.json').read_text())
cases={c['id']:c for c in spec['cases']}
result={'utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),
        'candidate_contact':False,'scope':'literal fixtures only; not released raw lists',
        'cases':[],'false_twins':[]}


def child_sources(case,row):
    i=row['parent']
    return (case['ss'][:i] + [Graph(case['ss'][i]).restriction(b) for b in row['Q']]
            + case['ss'][i+1:])


def refines(forest,source_labels):
    return all(any(set(b)<=set(c) for c in source_labels) for b in forest)


def audit_branch(case,branch,row,override=None):
    i=row['parent']
    parent=Graph(case['ss'][i])
    qbs=row['Q']
    d=row['d']
    equal(d,len(qbs)-1,'actual source component delta')
    equal(d>=1,True,'strict forest budget descent')
    equal(State(case['ss'][i],[case['ss'][i]]).agrees(qbs),True,'literal source partition/embeddings')
    rs=[set(r) for r in Graph(case['T']).regions(branch['vertex'],parent.taxa)]
    equal(all(any(set(b)<=r for r in rs) for b in qbs),True,'monochromatic source output')
    expected=child_sources(case,row)
    sources=expected if override is None else override
    equal(sources,expected,'only named parent replaced; all others literal')
    child=State(case['T'],sources)
    equal(child.proper,True,'proper replacement')
    equal(len(child.ss)-len(case['ss']),d,'source component change')
    old=State(case['T'],case['ss'])
    transport=0
    budgets=0
    for forest in old.forests():
        refinement=refines(forest,[s.taxa for s in child.ss])
        equal(child.agrees(forest),refinement,'original-target agreement transport iff refinement')
        if refinement:
            old_cost=len(forest)-len(old.ss)
            residual=len(forest)-len(child.ss)
            equal(old_cost,d+residual,'exact additional cost telescope')
            for q in range(max(0,branch['minimum']-1),branch['minimum']+2):
                if d<=q:
                    equal(old_cost<=q,residual<=q-d,'affordable residual budget equality')
                    budgets+=1
            transport+=1
    return child, {'raw_id':row['id'],'parent':i,'d':d,'sources':sources,
                   'transported_forests':transport,'budget_equalities':budgets}


def audit_cover(case,branch,raw):
    old=State(case['T'],case['ss'])
    v=tuple(branch['vertex'])
    children=[audit_branch(case,branch,row)[0] for row in raw]
    checked=0
    for forest in old.forests():
        covering=[i for i,c in enumerate(children) if c.agrees(forest)]
        equal(bool(covering),True,'all actual agreeing final forests covered')
        owners=[]
        for parent in old.ss:
            local=[b for b in forest if set(b)<=set(parent.taxa)]
            owners.append(any(v in old.T.hull(b) for b in local))
        equal(sum(owners)<=1,True,'target vertex unique parent occupancy')
        for i,row in enumerate(raw):
            if not owners[row['parent']]:
                equal(i in covering,True,'avoiding parent fixture provides refinement')
        checked+=1
    for q in range(branch['minimum']+2):
        outputs=[]
        for row,child in zip(raw,children):
            if row['d']<=q:
                available=[f for f in child.forests() if len(f)-len(child.ss)<=q-row['d']]
                if available:
                    f=min(available,key=len)
                    equal(old.agrees(f),True,'minimum selection original target check')
                    outputs.append(f)
        if outputs:
            chosen=min(outputs,key=len)
            equal(len(chosen)-len(old.ss),branch['minimum'],'minimum over actual returned forests')
        equal(bool(outputs),q>=branch['minimum'],'existence over all checked raw children')
    return checked


try:
    for branch in extra['branches']:
        started=time.perf_counter()
        case=cases[branch['case']]
        children=[]
        for row in branch['raw']:
            _,receipt=audit_branch(case,branch,row)
            children.append(receipt)
        n=audit_cover(case,branch,branch['raw'])
        equal(str(mass(branch['raw'],Fraction(2))),branch['total_mass_c2'],'two-source fixture mass')
        result['cases'].append({'case':branch['case'],'children':children,'coverage_forests':n,
                                'seconds':time.perf_counter()-started})
    branch=extra['branches'][0]
    case=cases[branch['case']]
    raw=branch['raw']
    wrong=deepcopy(raw[0]); wrong['d']=0
    result['false_twins'].append(expect_caught('zero_delta',lambda:audit_branch(case,branch,wrong)))
    result['false_twins'].append(expect_caught('erase_other_source',lambda:audit_branch(case,branch,raw[0],override=[0,1])))
    wrong=deepcopy(raw[0]); wrong['Q']=[[0,1]]
    result['false_twins'].append(expect_caught('free_whole_parent',lambda:audit_branch(case,branch,wrong)))
    result['false_twins'].append(expect_caught('favorable_child_only',lambda:audit_cover(case,branch,raw[:1])))
    result['false_twins'].append(expect_caught('missing_cover_occurrence',lambda:audit_cover(case,branch,raw[1:])))
    original=State(case['T'],case['ss'])
    result['false_twins'].append(expect_caught('forged_child_original_agreement',lambda:equal(
        original.agrees([[0,1],[2,3]]),True,'original agreement output gate')))
    child,_=audit_branch(case,branch,raw[0])
    f=[[0],[1],[2],[3]]; q=1; d=1
    true_affordable=len(f)-len(original.ss)<=q
    false_affordable=len(f)-len(child.ss)<=q-d+1
    equal([true_affordable,false_affordable],[False,True],'budget false plant witness')
    result['false_twins'].append(expect_caught('wrong_residual_budget',lambda:equal(
        false_affordable,true_affordable,'wrong residual q-d+1')))
    equal(sorted(r['plant'] for r in result['false_twins']),
          sorted(extra['replacement_false_twins']),'replacement detector denominator')
    result['passed']=True
except Exception as exc:
    result['passed']=False;result['failure']=repr(exc)
    raise
finally:
    (HERE/'replacement-controls-v1.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'passed':True,'cases':len(result['cases']),
                  'false_twins':len(result['false_twins'])}))
