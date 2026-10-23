#!/usr/bin/env python3
"""One-shot exact original Rule4 controls; no tree-pair census."""
from pathlib import Path
import datetime, hashlib, importlib.util, json, sys, time
from dataclasses import replace
D=Path(__file__).resolve().parent
ROOT=D.parents[4]
sys.path.insert(0,str(D))
import rule4 as r
p=ROOT/'research/rmaf/oracle/oracle.py'
spec=importlib.util.spec_from_file_location('development_oracle',p)
o=importlib.util.module_from_spec(spec);spec.loader.exec_module(o)
pin=json.loads((D/'CONTROLS-v1.json').read_text())
OUT=ROOT/'results'/('algorithm-universal233-rule4-controls-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'))
OUT.mkdir()
record={'status':'RUNNING','pin_sha256':hashlib.sha256((D/'CONTROLS-v1.json').read_bytes()).hexdigest(),'source_sha256':hashlib.sha256((D/'rule4.py').read_bytes()).hexdigest(),'oracle_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'main_milestones':'ALL THREE OPEN','independent_acceptance':False,'scope':'finite preproof original-graph controls; oracle is development contact','cases':[],'false_plants':[],'corruptions':[]}
start=time.monotonic()
def require(value,reason):
 if not value: raise AssertionError(reason)
def reject(name,fn):
 try: fn()
 except (AssertionError,ValueError) as e:
  record['corruptions'].append({'name':name,'rejected':True,'reason':str(e)})
 else: raise AssertionError('PLANT_SURVIVED: '+name)
def mirror(t): return t if isinstance(t,str) else (mirror(t[1]),mirror(t[0]))
def relabel(t,mp): return mp.get(t,t) if isinstance(t,str) else (relabel(t[0],mp),relabel(t[1],mp))
for key in ['accepted_root','accepted_outside']:
 z=pin[key];T,S=r.tree(z['T']),r.tree(z['S']);ss=r.candidates(T,S)
 for expected in z.get('oriented_candidates',[z['candidate']]):
  require(tuple(expected) in [(s.a,s.b,s.c) for s in ss],'pinned-orientation')
 s=next(s for s in ss if (s.a,s.b,s.c)==tuple(z['candidate']))
 require([b.cost for b in s.branches]==z['branch_costs'],'literal-costs')
 require(all(b.check() for b in s.branches),'literal-states')
 require(r.agreement(T,S,z['F']),'clean-original-F')
 independent=o.validate(*o.pair(T,S),z['F']);require(independent['valid'],'development-oracle-F')
 i,G,mode=r.covering_exchange(s,z['F'])
 require(G==r.forest(z['expected_exchange']),'pinned-exchange')
 require(o.validate(*o.pair(T,S),[list(B) for B in G])['valid'],'development-oracle-G')
 require(not any(r.refines(z['F'],b.partition) for b in s.branches),'strict-refinement-false')
 require(len(r.recover_original_cuts(S,G))==len(G)-1,'whole-source-final-cuts')
 mass,bound=r.paid_mass(s,'233/100');require(mass==bound,'literal-rational-mass')
 ms=r.candidates(mirror(T),mirror(S));require((s.a,s.b,s.c) in [(x.a,x.b,x.c) for x in ms],'sibling-mirror')
 mp={s.a:s.b,s.b:s.a};rs=r.candidates(relabel(T,mp),relabel(S,mp))
 require((s.b,s.a,s.c) in [(x.a,x.b,x.c) for x in rs],'endpoint-orientation')
 branches=[]
 for b in s.branches:
  branches.append({'name':b.name,'cost':b.cost,'swapped':b.swapped,'target':b.target,'source':b.source,'cuts':b.cuts,'partition':b.partition,'source_forest':b.source_forest,'original_regions':r.Graph(b.source).cut_regions(b.cuts)})
 record['cases'].append({'name':key,'candidates':[(x.a,x.b,x.c) for x in ss],'selected':(s.a,s.b,s.c),'branches':branches,'F':z['F'],'F_refines':[r.refines(z['F'],b.partition) for b in s.branches],'G':G,'mode':mode,'mass':str(mass),'bound':str(bound),'final_source_cuts':r.recover_original_cuts(S,G),'oracle_clean':independent['valid'],'mirror_and_endpoint_swap':True})
 for q in range(5):
  # This tiny exact callback is development-only. It never powers selection.
  def exact_child(b,k):
   valid=[F for F in o.partitions(tuple(sorted(r.leaves(T)))) if r.refines(F,b.partition) and r.agreement(b.target,b.source,F) and len(F)-len(b.partition)<=k]
   return min(valid,key=lambda F:(len(F),F)) if valid else None
  ans,calls=r.solve_selected(s,q,exact_child)
  opt=o.optimum(*o.pair(T,S))['k']
  require((ans is None)==(opt-1>q),'conditional-runner-feasibility')
  if ans is not None: require(ans['k']==opt,'conditional-runner-minimum')
  require(all(c['child_budget']<q for c in calls),'strict-decrease')
  record['cases'][-1].setdefault('child_callback_tests',[]).append({'q':q,'calls':calls,'answer':ans})
zt=pin['excluded_t1'];T,S=r.tree(zt['T']),r.tree(zt['S']);a,b,c=zt['candidate']
require(len(r.Graph(S).pendant(a,b))==2,'t1-source-two')
require(len(r.Graph(T).pendant(a,c))==1,'t1-swapped-one')
require(not r.no_common_and_no_t1(T,S) and not r.candidates(T,S),'t1-rejected')
record['excluded_t1']={'source_ab_pendants':r.Graph(S).pendant(a,b),'swapped_ac_pendants':r.Graph(T).pendant(a,c),'admitted':False}
z=pin['accepted_root'];T,S=r.tree(z['T']),r.tree(z['S']);s=r.select(T,S)
false_values=[any(r.refines(z['F'],b.partition) for b in s.branches),s.branches[2].cost==1,s.branches[2].source==S]
zo=pin['accepted_outside'];gs=r.Graph(r.tree(zo['S']));overlap=gs.embedding(('a','d'))&gs.embedding(('c','f'))
false_values += [not bool(overlap),r.no_common_and_no_t1(r.tree(zt['T']),r.tree(zt['S']))]
for name,value in zip(pin['false_plants'],false_values):
 require(value is False,'false-claim-survived');record['false_plants'].append({'claim':name,'value':value,'rejected':True})
record['source_clearance_collision_vertices']=sorted(overlap)
reject('duplicate-label',lambda:r.tree(['a',['b','a']]))
reject('missing-source-label',lambda:require(r.no_common_and_no_t1(T,r.tree(['a','b'])),'label-mismatch'))
reject('root-cut',lambda:r.Graph(S).cut_regions(('',)))
reject('duplicate-cut',lambda:r.Graph(S).cut_regions((s.c_head,s.c_head)))
reject('wrong-role-source',lambda:replace(s.branches[2],source=S).check())
reject('corrupted-pinned-exchange',lambda:require(r.forest(z['F'])==r.forest(z['expected_exchange']),'exchange-drift'))
record.update(status='PASS_PREPROOF_ACTUAL_RULE4_CONTROLS',elapsed_seconds=round(time.monotonic()-start,6),positive_actual_fixtures=2,conditional_callback_budget_tests=10,false_claims_rejected=len(false_values),corruptions_rejected=len(record['corruptions']),warning='No universal theorem or independent certification follows from these finite controls.')
(OUT/'receipt.json').write_text(json.dumps(record,indent=2)+'\n')
if not (D/'RULE4-MANIFEST-v1.json').exists():
 (D/'CONTROLS-RECEIPT.txt').write_text(str(OUT/'receipt.json')+'\n')
print(record['status'],record['elapsed_seconds'],'seconds; 2 fixtures, 10 callback budgets, 5 false claims,',len(record['corruptions']),'corruptions')
print(OUT)
