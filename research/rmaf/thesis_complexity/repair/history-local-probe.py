#!/usr/bin/env python3
"""Coordinator probe, reusing the completed geometry engine; not independent.

This starts from a locally protected state. It does not claim a top-level
unprotected source history. It tests why original eligibility is a premise.
"""
from pathlib import Path
import importlib.util
import sys
import json
import copy

ROOT=Path(__file__).resolve().parents[2]
SRC=Path(__file__).resolve().parent/'geometry/check.py'
spec=importlib.util.spec_from_file_location('geometry_probe_engine',SRC)
g=importlib.util.module_from_spec(spec)
sys.modules[spec.name]=g
spec.loader.exec_module(g)

# Exposed calibration controls execute before the new local history probe.
calibration=g.controls()
f1s='((((a,c),d),((x,y),h)),((W,X),(Y,B)))'
f2s='(((a,((W,(x,X)),(d,(y,Y)))),(c,B)),h)'
a,c,d,x,y=map(g.label,['a','c','d','x','y'])
f1=g.parse(f1s);f2=[g.parse(f2s)]
g.mark([f1],[a]);g.mark(f2,[a])
original_b=g.label('W,x,X,d,y,Y')

before=g.selection(f1,f2)
assert any(set(p)=={a,c} for p in before)
# False eligibility strengthening: deleting the existing protection changes
# eligibility. The intended twin no longer selects the original (a,c) pair.
unprotected=copy.deepcopy(f1)
g.ix([unprotected])[0][a].p=False
without=g.selection(unprotected,f2)
assert not any(set(p)=={a,c} for p in without)

rows=[]
for pair,branch in [((a,c),'C'),((d,a),'A')]:
 f1,f2,info=g.normal(f1,f2,pair)
 rows.append({'f1':f1.text(),'f2':[t.text() for t in f2],
              'protected1':g.protected([f1]),'protected2':g.protected(f2),
              'rule':g.freeze(info),'chosen_branch':branch})
 assert info['case']=='A2BC'
 b=next(b for b in info['branches'] if b['name']==branch)
 f1,f2=g.child(f1,f2,b)

f1,f2,info=g.normal(f1,f2,(x,y))
assert info['case']=='A3BC' and len(info['pendants'])==3
assert all(b['legal'] for b in info['branches'])
ns,pa,_,_=g.ix(f2)
current_b=g.sibling(ns,pa,a)
assert x <= current_b
rows.append({'f1':f1.text(),'f2':[t.text() for t in f2],
             'protected1':g.protected([f1]),'protected2':g.protected(f2),
             'rule':g.freeze(info),'a_sibling':g.freeze(current_b),
             'retained_x_inside_b':True,
             'literal_credit_assignment':{'P':['a'],'Q':[]}})
result={'scope':'local protected entry state, NOT a top-level source-reachable counterexample',
        'engine_lineage':'reuses completed geometry/check.py; coordinator exploration only',
        'input_f1':f1s,'input_f2':f2s,'initial_protected1':['a'],'initial_protected2':['a'],
        'initial_analysis_credits':{'P':[],'Q':[]},
        'initial_selected_pairs':g.freeze(before),
        'protection_removed_twin_selected_pairs':g.freeze(without),
        'calibration_control_groups':len(calibration),
        'original_b':g.freeze(original_b),'rows':rows,
        'conclusion':'original x,y eligibility cannot be inferred from equal F1 depth and this local carried-credit prefix alone',
        'missing_obligation':'reach this protected empty-credit entry state from an unprotected source input, or prove it cannot occur'}
out=ROOT/'results/thesis-runtime-repair-history-local-probe.json'
out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'scope':result['scope'],'control_groups':len(calibration),
                  'rules':[r['rule']['case'] for r in rows],
                  'retained_x_inside_b':True,'path':str(out)}))
