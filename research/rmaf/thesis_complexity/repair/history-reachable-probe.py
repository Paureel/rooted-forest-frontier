#!/usr/bin/env python3
"""Coordinator continuation of the local history probe; engine reuse disclosed."""
from pathlib import Path
import importlib.util,sys,json
ROOT=Path(__file__).resolve().parents[2]
src=Path(__file__).resolve().parent/'geometry/check.py'
spec=importlib.util.spec_from_file_location('history_reachable_geometry',src)
g=importlib.util.module_from_spec(spec);sys.modules[spec.name]=g;spec.loader.exec_module(g)
controls=g.controls()
f1s='((((((a,t),d0),c),d),((x,y),h)),((W,X),(Y,B)))'
f2s='(((a,((W,(x,X)),(d,(y,Y)))),(t,(c,(d0,B)))),h)'
f1=g.parse(f1s);f2=[g.parse(f2s)]
assert not g.protected([f1]) and not g.protected(f2)
rows=[]
steps=[('a','t','C','A2BC',{'P':['a'],'Q':[]},'initial G1 C'),
       ('d0','a','A','A3BC',{'P':[],'Q':[]},'initial G3 sole child resets both credits'),
       ('a','c','C','A2BC',{'P':['a'],'Q':[]},'new empty-credit G1 C'),
       ('d','a','A','A2BC',{'P':['a'],'Q':[]},'new G3 two-child A2 endpoint branch retains a')]
for i,(aa,cc,name,expected,credits,note) in enumerate(steps):
 a,c=map(g.label,[aa,cc]);f1,f2,info=g.normal(f1,f2,(a,c))
 assert info['case']==expected,(i,info['case'],expected)
 selected=next(b for b in info['branches'] if b['name']==name)
 assert selected['legal']
 rows.append({'step':i+1,'budget':20-i,'f1':f1.text(),'f2':[t.text() for t in f2],
              'protected1':g.protected([f1]),'protected2':g.protected(f2),
              'rule':g.freeze(info),'selected_branch':name,
              'output_credits':credits,'credit_rule':note})
 if i==1:assert sum(b['legal'] for b in info['branches'])==1
 if i==2:assert sum(b['legal'] for b in info['branches'])==1
 if i==3:assert sum(b['legal'] for b in info['branches'])==2
 f1,f2=g.child(f1,f2,selected)
x,y,a=map(g.label,['x','y','a'])
f1,f2,info=g.normal(f1,f2,(x,y))
assert info['case']=='A3BC' and len(info['pendants'])==3
assert all(b['legal'] for b in info['branches'])
ns,pa,_,_=g.ix(f2);b=g.sibling(ns,pa,a)
assert x<=b
rows.append({'step':5,'budget':16,'f1':f1.text(),'f2':[t.text() for t in f2],
             'protected1':g.protected([f1]),'protected2':g.protected(f2),
             'rule':g.freeze(info),'input_credits':{'P':['a'],'Q':[]},
             'a_sibling':g.freeze(b),'retained_x_inside_b':True})
out={'scope':'candidate reachable counterexample to unqualified history-to-outside-b application; not a runtime counterexample',
     'validation_status':'coordinator engine replay; independent replay and Lean witness pending',
     'engine_lineage':'completed geometry/check.py reused, no independence claimed',
     'initial_budget':20,'input_f1':f1s,'input_f2':f2s,'root_convention':'labelled unary rho',
     'initial_protected1':[],'initial_protected2':[],'initial_credits':{'P':[],'Q':[]},
     'reachability_convention':'full permitted recursive-call tree; no short-circuit visitation claim',
     'control_groups_passed':len(controls),'rows':rows,
     'contradicted_application':'Every source-reachable three/four-root exceptional G4.1 instance satisfies x outside the inherited protected sibling b and original G1 eligibility of x,y',
     'not_contradicted':'The geometric candidate explicitly assumes original eligibility and x outside b; its conditional local theorem and the joint runtime inequality are not refuted.'}
path=ROOT/'results/thesis-runtime-repair-history-reachable-probe.json'
path.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'rows':len(rows),'rules':[r['rule']['case'] for r in rows],
                  'candidate_retained_x_inside_b':True,'independent_review':'pending','path':str(path)}))
