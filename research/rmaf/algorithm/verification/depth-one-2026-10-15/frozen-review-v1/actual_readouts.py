#!/usr/bin/env python3
"""Actual released edge/pretest definitions against PRECONTACT frozen graph controls.
Postrelease readout instrument; original inputs and witness expectations unchanged.
"""
from pathlib import Path
import json,importlib.util,sys,itertools,hashlib
H=Path(__file__).resolve().parent
s=importlib.util.spec_from_file_location('blind_depth01',H/'frozen-ready-v1/independent_depth_one.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
s=importlib.util.spec_from_file_location('own_std_api',H/'frozen-ready-v1/std_toy_gates.py');a=importlib.util.module_from_spec(s);s.loader.exec_module(a)
a.F=H/'isolated-release-v1';a.OUT=a.ROOT/'research/rmaf/results/algorithm-depth-one-fresh-actual-definitions-v1.json';a.state={'phase':'RELEASED','runs':[],'audits':{},'comparisons':[],'result_witnesses':[],'all_main_milestones':'OPEN'}
pin=json.loads((H/'frozen-ready-v1/CONTROL-PIN-v1.json').read_text());old=json.loads((H/'frozen-ready-v1/results/algorithm-depth-one-fresh-battery-v1.json').read_text());byid={r['id']:r for r in old['fixtures']}
def tree(t):return '(.leaf '+str(t)+')' if isinstance(t,int) else '(.node '+tree(t[0])+' '+tree(t[1])+')'
def nl(xs):return '['+','.join(map(str,xs))+']'
def parts(F):return '['+','.join(nl(x) for x in F)+']'
def vertex(p):return '['+','.join('false' if c=='0' else 'true' for c in p)+']'
def jtree(t):return {'leaf':t} if isinstance(t,int) else {'node':[jtree(t[0]),jtree(t[1])]}
def expr(items):return 'Lean.Json.mkObj ['+','.join('('+json.dumps(k)+',Lean.toJson ('+v+'))' for k,v in items)+']'
lines=['''import Runtime01
import Lean
open RMAF Universal233 Universal233.DepthOne
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
def tj : Tree → Lean.Json
 | .leaf x => Lean.Json.mkObj [("leaf",Lean.toJson x)]
 | .node a b => Lean.Json.mkObj [("node",Lean.toJson [tj a,tj b])]
def otj : Option Tree → Lean.Json
 | none => Lean.Json.null
 | some t => tj t
def rj (T S : Tree) : Lean.Json :=
 match pretest01 T S with
 | .refused => Lean.Json.mkObj [("status",Lean.toJson "REFUSED")]
 | .rejected => Lean.Json.mkObj [("status",Lean.toJson "MINIMUM_AT_LEAST_2")]
 | .found c => Lean.Json.mkObj [("status",Lean.toJson "FOUND"),("cut",Lean.toJson c),
     ("forest",Lean.toJson (forest S c)),("cuts",Lean.toJson (sourceCuts c)),("cost",Lean.toJson (cutCost c))]
def emit (id : String) (j : Lean.Json) : IO Unit := IO.println ("READOUT|" ++ id ++ "|" ++ j.compress)
'''];expected={};resultids={};den={'input_pairs':13,'original_edges':0,'all_partitions':0,'one_two_partitions':0,'restriction_rows':0,'planted_agreement_readouts':0}
def row(id,ex,w):assert id not in expected;expected[id]=w;lines.append('#eval emit '+json.dumps(id)+' ('+ex+')')
for f in pin['cases']:
 S,T=m.g.Original(f['S']),m.g.Original(f['T']);ss,tt=tree(f['S']),tree(f['T']);id=f['id'];b=byid[id]
 row(id+'/guard','Lean.toJson (proper '+tt+' '+ss+')',f['guard'])
 if f['guard']:
  row(id+'/inventory',expr([('edges',f'edges {ss}'),('candidates',f'(candidates {ss}).length'),('size',f'treeSize {ss}')]),{'edges':[[c=='1' for c in p] for p in f['edges']],'candidates':len(f['edges'])+1,'size':len(S.graph)})
  for e in b['edge_checks']:
   p=e['edge'];F=e['partition'];cs=m.components(S,[p]);literal=[[x for v,x in S.leaf_at.items() if v.startswith(p)],[x for v,x in S.leaf_at.items() if not v.startswith(p)]]
   row(id+'/edge/'+p,expr([('forest',f'forest {ss} (some {vertex(p)})'),('cuts',f'sourceCuts (some {vertex(p)})'),('agreement',f'agreement {tt} {ss} (forest {ss} (some {vertex(p)}))'),('parent',f'{vertex(p)}.dropLast')]),{'forest':literal,'cuts':[[c=='1' for c in p]],'agreement':e['agreement'],'parent':[c=='1' for c in p[:-1]]});den['original_edges']+=1
  _,_,ps=m.minimum_forests(S,T)
  for i,F in enumerate(ps):
   fs=parts(F);shape=all(S.clusters(frozenset(B))==T.clusters(frozenset(B)) and S.clusters(frozenset(B)) for B in F)
   row(id+'/partition/'+str(i),expr([('agreement',f'agreement {tt} {ss} {fs}'),('source_embeddings',f'pairwiseEmbeddings {ss} {fs}'),('target_embeddings',f'pairwiseEmbeddings {tt} {fs}'),('shape',f'{fs}.all (restrictionAgrees {tt} {ss})')]),{'agreement':bool(m.g.agrees(S,T,F)),'source_embeddings':S.embedding_disjoint(F),'target_embeddings':T.embedding_disjoint(F),'shape':bool(shape)});den['all_partitions']+=1
   if len(F)<=2:den['one_two_partitions']+=1
 idr=id+'/result';resultids[idr]=f;lines.append('#eval emit '+json.dumps(idr)+' (rj '+tt+' '+ss+')')
for id,f in pin['planted_witnesses'].items():
 S,T=m.g.Original(f['S']),m.g.Original(f['T']);row('plant/'+id,expr([('agreement',f'agreement {tree(f["T"])} {tree(f["S"])} {parts(f["forest"])}')]),{'agreement':bool(m.g.agrees(S,T,f['forest']))});den['planted_agreement_readouts']+=1
r=pin['restriction_controls'];S=m.g.Original(r['tree']);st=tree(r['tree'])
for name in ['empty_selection','absent_selection','repeated_selection','root_selection','below_root_selection','singleton_selection']:
 U=r[name];t=m.g.raw_restrict(S.tree,U);u=nl(U);ex='Lean.Json.mkObj [("restriction",otj (restrict '+u+' '+st+')),("hull",Lean.toJson (minimalVertices '+u+' '+st+'))]'
 row('restriction/'+name,ex,{'restriction':None if t is None else jtree(t),'hull':[[c=='1' for c in p] for p in sorted(S.hull(frozenset(U)))]});den['restriction_rows']+=1
for i,F in enumerate(pin['false_extensions']['malformed_forests']):row('malformed/'+str(i),'Lean.toJson (agreement '+tree([[0,1],2])+' '+tree([[0,1],2])+' '+parts(F)+')',False)

def main():
 (H/'ACTUAL-READOUT-EXPECTED-v1.json').write_text(json.dumps({'phase':'Postrelease instrument; inputs and forest/cut/minimum expectations are frozen-ready-v1','denominators':den,'literal_rows':expected,'result_acceptance':'Any frozen globally minimum forest and matching literal original source cut; no candidate tie order assumption'},indent=2)+'\n')
 name='FreshActualReadouts';(a.F/(name+'.lean')).write_text('\n'.join(lines)+'\n');log=a.compile(name);seen={}
 for line in log.splitlines():
  if line.startswith('READOUT|'):
   _,id,v=line.split('|',2);assert id not in seen;seen[id]=json.loads(v)
 assert set(seen)==set(expected)|set(resultids)
 for id,want in expected.items():
  actual=seen[id]
  if id.startswith('restriction/'):
   actual['hull']=sorted(actual['hull']);want['hull']=sorted(want['hull'])
  ok=actual==want;a.state['comparisons'].append({'id':id,'actual':actual,'expected':want,'passed':ok});a.save();assert ok,(id,actual,want)
 for id,f in resultids.items():
  actual=seen[id];S,T=m.g.Original(f['S']),m.g.Original(f['T'])
  if not f['guard']:assert actual=={'status':'REFUSED'}
  elif f['minimum_cost']>=2:assert actual=={'status':'MINIMUM_AT_LEAST_2'}
  else:
   assert actual['status']=='FOUND' and actual['cost']==f['minimum_cost']
   assert m.canon(actual['forest']) in m.family(f['minimum_forests'])
   cuts=[''.join('1' if c else '0' for c in p) for p in actual['cuts']]
   chosen=None if actual['cut'] is None else ''.join('1' if c else '0' for c in actual['cut'])
   assert cuts==([] if chosen is None else [chosen])
   assert m.realization(S,T,actual['forest'],cuts) and m.witness_minimum(S,T,actual['forest'],cuts)
  a.state['result_witnesses'].append({'id':id,'actual':actual,'frozen_minimum_cost':f.get('minimum_cost'),'guard':f['guard'],'accepted':True});a.save()
 a.state['denominators']=den;a.state['verdict']='PASS-ACTUAL-ORIGINAL-EDGE-SEARCH-GUARDS-CUTS-GLOBAL-MINIMUM-AND-FROZEN-CONTROLS';a.save();print(json.dumps({'verdict':a.state['verdict'],'literal_comparisons':len(expected),'actual_results':len(resultids),'denominators':den}))
if __name__=='__main__':
 try:main()
 except Exception as e:a.state['verdict']='OPEN-ACTUAL-READOUT-FAILURE';a.state['error']=repr(e);a.save();raise
