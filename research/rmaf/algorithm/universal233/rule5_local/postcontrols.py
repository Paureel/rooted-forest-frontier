#!/usr/bin/env python3
"""One-shot bounded post-contact graph controls; oracle is DEVELOPMENT."""
from pathlib import Path
import json,datetime,time,subprocess,os
import local
D=Path(__file__).resolve().parent;R=D.parents[4]
O=R/'results'/('algorithm-universal233-rule5-local-post-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'));O.mkdir()
def mirror(t):return t if local.leaf(t) else (mirror(t[1]),mirror(t[0]))
family=local.fixture_family();rows={}
for name,(t,u,want) in family.items():
 mt,mu=mirror(t),mirror(u);C=local.classify(mt,mu)
 assert C['kind']==want,(name,'MIRROR_CLASS',C)
 rows[name]=dict(guards=local.admitted(mt,mu),classification=C,branches=local.branches(mt,mu,C))
X=('w',('t',('x',('p','q'))))
iT=('t',(('a','b'),('p',('x',('q',('w','c'))))))
iS=((('a',X),'c'),'b')
iiiT=('p',('x',('q',(('a','b'),('w','c')))))
iiiS=((('a',('w',('x',('p','q')))),'c'),'b')
extras={}
for name,t,u,want in [('type3i',iT,iS,[2,1,2,2]),('type3iii',iiiT,iiiS,[2,1,2])]:
 C=local.classify(t,u);assert C['kind']=='322',(name,C)
 B=local.branches(t,u,C);assert [b['paid'] for b in B]==want,(name,B)
 extras[name]=dict(target=t,source=u,classification=C,branches=B)

def census(t,u,B):
 start=time.monotonic();da,db=local.O.TreeData(t),local.O.TreeData(u)
 AF=[];tested=0
 for F in local.O.partitions(da.labels):
  tested+=1
  if da.disjoint(F) and db.disjoint(F) and all(da.restrictions[A]==db.restrictions[A] for A in F):AF.append(F)
 assert AF
 mn=min(map(len,AF));child=[]
 for b in B:
  accepted=[F for F in AF if all(any(set(A)<=set(C) for C in b['partition']) for A in F)]
  assert accepted
  G=min(accepted,key=lambda F:(len(F),F));child.append(dict(name=b['name'],paid=b['paid'],minimum_components=len(G),witness=G))
 assert min(x['minimum_components'] for x in child)==mn,('COVER_FAIL',t,u,child,mn)
 return dict(tested_partitions=tested,actual_AF=len(AF),minimum_components=mn,child_minima=child,seconds=time.monotonic()-start)
checks={};pilot=family['six'];c=local.classify(*pilot[:2]);checks['six']=census(*pilot[:2],local.branches(*pilot[:2],c))
# Faithful rate measurement: same per-partition evaluator, maximum fixture n=8.
projection=(4140+877+4140+877)/checks['six']['tested_partitions']*checks['six']['seconds']
assert projection<60,('RESTRUCTURE_REQUIRED',projection)
for name in ['first','third']:
 t,u,_=family[name];C=local.classify(t,u);checks[name]=census(t,u,local.branches(t,u,C))
for name,r in extras.items():checks[name]=census(r['target'],r['source'],r['branches'])

F321=[['x','c','s'],['a'],['b'],['w'],['p'],['q']]
F323=[['a','c','w'],['b'],['x'],['p'],['q']]
for name,F in [('first',F321),('third',F323)]:
 t,u,_=family[name];assert local.O.validate(t,u,F)['valid'],(name,F)
 X=local.classify(t,u)['P'][local.classify(t,u)['j']]
 def split(F,X):return [C for B in F for C in ([x for x in B if x in X],[x for x in B if x not in X]) if C]
 assert len(split(split(F,set(X)),{'c'}))==len(F)+2,(name,F)

ids=json.loads((D/'LABELS-v1.json').read_text())
def fs(F):return '['+','.join('['+','.join(str(ids[x]) for x in B)+']' for B in F)+']'
txt='import Rule5Case321\nnamespace Universal233.Rule5Local.Post\nopen RMAF Pre\n'
txt+=f'def F321 : List (List Nat) := {fs(F321)}\ndef F323 : List (List Nat) := {fs(F323)}\n'
txt+='theorem valid321 : agreement firstT firstS F321 = true := by decide\n'
txt+='theorem valid323 : agreement thirdT thirdS F323 = true := by decide\n'
txt+='theorem extra321 : (splitTwo F321 firstS [false,false,false,true] [false,false,true]).length = F321.length+2 := by decide\n'
txt+='theorem extra323 : (splitTwo F323 thirdS [false,false,true] [false,true]).length = F323.length+2 := by decide\n'
txt+='end Universal233.Rule5Local.Post\n'
(D/'Rule5GraphControls.lean').write_text(txt)
bad='import Rule5GraphControls\nopen Universal233.Rule5Local Universal233.Rule5Local.Post Universal233.Rule5Local.Pre\n'
bad+='example : (splitTwo F321 firstS [false,false,false,true] [false,false,true]).length ≤ F321.length+1 := by decide\n'
bad+='example : (splitTwo F323 thirdS [false,false,true] [false,true]).length ≤ F323.length+1 := by decide\n'
(D/'Rule5FalseGraphControls.lean').write_text(bad)
record=dict(status='PASS_BOUNDED_DEVELOPMENT',mirrors=rows,additional_paths=extras,finite_checks=checks,
 pilot_projection_seconds=projection,guard_counterexamples=dict(case321=F321,case323=F323),independence='All author/oracle contacts DEVELOPMENT')
(O/'certificate.json').write_text(json.dumps(record,indent=2)+'\n')
(D/'POST-RECEIPT-v1.json').write_text(json.dumps(dict(receipt=str(O.relative_to(R))),indent=2)+'\n')
print('PASS_BOUNDED_DEVELOPMENT', {k:(v['tested_partitions'],v['actual_AF'],round(v['seconds'],4)) for k,v in checks.items()})
print(O)
