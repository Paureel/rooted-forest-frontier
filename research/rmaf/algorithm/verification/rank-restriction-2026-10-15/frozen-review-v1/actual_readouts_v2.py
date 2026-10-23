#!/usr/bin/env python3
"""Actual Lean definitions vs own PRECONTACT frozen original-graph/interpreter data.
No author control/checker execution; all finite denominators retained.
"""
import importlib.util,sys,json,itertools,hashlib,re,time
from pathlib import Path
from fractions import Fraction
HERE=Path(__file__).resolve().parent
s=importlib.util.spec_from_file_location('frozen_own',HERE/'frozen-ready-v1/independent_rank_restriction.py');m=importlib.util.module_from_spec(s);sys.modules[s.name]=m;s.loader.exec_module(m)
s=importlib.util.spec_from_file_location('replay_own',HERE/'released_replay.py');a=importlib.util.module_from_spec(s);s.loader.exec_module(a)
a.OUT=a.RMAF/'results/algorithm-rank-restriction-fresh-actual-definitions-v2.json';a.state={'runs':[],'audits':{},'scope':'Finite actual-definition comparisons; not universal proof acceptance','comparisons':[],'denominators':{}}
pin=json.loads((HERE/'frozen-ready-v1/CONTROL-PIN-v1.json').read_text());clear=json.loads((HERE/'frozen-ready-v1/ACTUAL-CLEARING-PIN-v1.json').read_text())
def natlist(xs):return '['+','.join(map(str,xs))+']'
def parts(ps):return '['+','.join(natlist(x) for x in ps)+']'
def tree(t):return '(.leaf '+str(t)+')' if isinstance(t,int) else '(.node '+tree(t[0])+' '+tree(t[1])+')'
def color(cs):return '(fun x : Nat => '+''.join('if x == '+str(x)+' then '+str(c)+' else ' for x,c in cs)+'0)'
def tj(t):return {'leaf':t} if isinstance(t,int) else {'node':[tj(t[0]),tj(t[1])]}
def jsonexpr_pairs(items):return 'Lean.Json.mkObj ['+','.join('('+json.dumps(k)+', Lean.toJson ('+v+'))' for k,v in items)+']'
def outrec(r):
 return {**r,'outputs':[{'partition':o['partition'],'cuts':[[c=='1' for c in p] for p in o['cuts']]} for o in r['outputs']]}
base='''import Lean
open RMAF
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
def tj : Tree → Lean.Json
  | .leaf x => Lean.Json.mkObj [("leaf",Lean.toJson x)]
  | .node l r => Lean.Json.mkObj [("node",Lean.toJson [tj l,tj r])]
def otj : Option Tree → Lean.Json
  | none => Lean.Json.null
  | some t => tj t
def emit (id : String) (j : Lean.Json) : IO Unit :=
  IO.println ("READOUT|" ++ id ++ "|" ++ j.compress)
'''
rankhead='''import ColorClasses
'''+base+'''
open Universal233 Universal233.CoreProgram Universal233.SourceCoverage Universal233.RankDichotomy
def oj (o : Output) : Lean.Json := Lean.Json.mkObj [("partition",Lean.toJson o.partition),("cuts",Lean.toJson o.sourceCuts)]
def rj (r : Receipt) : Lean.Json := Lean.Json.mkObj [("outputs",Lean.toJson (r.outputs.map oj)),("refusals",Lean.toJson r.refusals),("visited",Lean.toJson r.visited),("attempts",Lean.toJson r.childAttempts),("pruned",Lean.toJson r.pruned)]
def qj (q : Rat) : Lean.Json := Lean.Json.mkObj [("num",Lean.toJson q.num),("den",Lean.toJson q.den)]
'''
expected={};ranklines=[rankhead];counts={'rank_original_partitions':0,'rank_budget_receipts':0,'clearing_actual_receipts':0,'mass_terms':0,'restriction_fixtures':0,'restriction_path_rows':0,'embedding_pair_transport':0,'negative_local_families':0}
def row(lines,id,expr,want):
 assert id not in expected;expected[id]=want;lines.append('#eval emit '+json.dumps(id)+' ('+expr+')')
for f in pin['rank_cases']:
 t=tree(f['tree']);c=color(f['colors']);model=m.g.Original(f['tree']);cols=dict(f['colors']);n=len(model.labels)
 row(ranklines,f['id']+'/rank','Lean.toJson (inputRank '+t+' '+c+')',len(set(cols[x] for x in model.labels)))
 budgets=range(n+3) if model.proper else [n-1]
 for q in budgets:
  r=m.generate(f['tree'],cols,q);row(ranklines,f['id']+'/q'+str(q),'rj (generate '+t+' '+c+' '+str(q)+')',outrec(r));counts['rank_budget_receipts']+=1
  if model.proper:
   rnk=len(set(cols[x] for x in model.labels));costs=[len(o['cuts']) for o in r['outputs']]
   for L in range(rnk-1,n+2):
    if not all(d>=L for d in costs):continue
    for b in map(Fraction,pin['rational_bases']):
     v=m.mass(costs,b);expr=f'qj (rawQMass ({b.numerator}/{b.denominator} : Rat) (generate {t} {c} {q}).outputs)'
     row(ranklines,f['id']+'/mass/'+str(q)+'/'+str(L)+'/'+str(b),expr,{'num':v.numerator,'den':v.denominator});counts['mass_terms']+=1
 if not model.proper:continue
 for i,p in enumerate(m.g.partitions(sorted(model.labels))):
  want={'partition':m.g.partition_check(model.labels,p),'embedding':model.embedding_disjoint(p),'mono':all(len({cols[x] for x in b})==1 for b in p),'size':len(p)}
  ps=parts(p);expr=jsonexpr_pairs([('partition',f'partitionCheck (leaves {t}) {ps}'),('embedding',f'pairwiseEmbeddings {t} {ps}'),('mono',f'{ps}.all (fun b => b.all (fun x => b.all (fun y => {c} x == {c} y)))'),('size',f'{ps}.length')])
  row(ranklines,f['id']+'/partition/'+str(i),expr,want);counts['rank_original_partitions']+=1
 classes=[[x for x in model.labels if cols[x]==v] for v in sorted(set(cols.values()))];ps=parts(classes)
 row(ranklines,f['id']+'/canonical',jsonexpr_pairs([('partition',f'partitionCheck (leaves {t}) {ps}'),('embedding',f'pairwiseEmbeddings {t} {ps}'),('full_classes',f'{ps}.all (fun b => (leaves {t}).all (fun x => b.contains x == ({c} x == {c} (b.headD 0))))')]),{'partition':True,'embedding':f['feasible'],'full_classes':True})
for f in clear['cases']:
 r=m.generate(f['S'],dict(f['colors']),f['budget']);row(ranklines,f['id']+'/receipt','rj (generate '+tree(f['S'])+' '+color(f['colors'])+' '+str(f['budget'])+')',outrec(r));counts['clearing_actual_receipts']+=1
 for i,o in enumerate(r['outputs']):
  ps=parts(o['partition']);T=tree(f['T']);S=tree(f['S']);tm=m.g.Original(f['T']);sm=m.g.Original(f['S']);vs='['+','.join('['+','.join('false' if b=='0' else 'true' for b in v)+']' for v in f['requested_vertices'])+']'
  row(ranklines,f['id']+'/output/'+str(i),jsonexpr_pairs([('source',f'pairwiseEmbeddings {S} {ps}'),('target',f'pairwiseEmbeddings {T} {ps}'),('clear',f'{ps}.all (fun b => {vs}.all (fun v => !(minimalVertices b {T}).contains v))'),('agreement',f'agreement {T} {S} {ps}')]),{'source':True,'target':tm.embedding_disjoint(o['partition']),'clear':True,'agreement':bool(m.g.agrees(tm,sm,o['partition']))})
restlines=['import Consumers\n'+base+'\nopen RestrictionBridge\n']
for f in pin['restriction_cases']:
 S,T=m.g.Original(f['S']),m.g.Original(f['T']);ss,tt=tree(f['S']),tree(f['T']);Q,F=f['Q'],f['F'];qs,fs=parts(Q),parts(F);fams=[[B for B in F if set(B)<=set(U)] for U in Q]
 expr=jsonexpr_pairs([('original_agreement',f'agreement {ss} {tt} {fs}'),('refines',f'{fs}.all (fun B => {qs}.any (fun U => contained B U))'),('source_Q_disjoint',f'pairwiseEmbeddings {ss} {qs}'),('target_Q_disjoint',f'pairwiseEmbeddings {tt} {qs}'),('families',f'{qs}.map (fun U => family U {fs})'),('sumcost',f'({qs}.map (fun U => (family U {fs}).length - 1)).sum')])
 row(restlines,f['id']+'/family',expr,{'original_agreement':bool(m.g.agrees(S,T,F)),'refines':m.g.refines(F,Q),'source_Q_disjoint':S.embedding_disjoint(Q),'target_Q_disjoint':T.embedding_disjoint(Q),'families':fams,'sumcost':sum(len(x)-1 for x in fams)});counts['restriction_fixtures']+=1
 for U,fa in zip(Q,fams):
  us=natlist(U);u=m.g.raw_restrict(S.tree,U);v=m.g.raw_restrict(T.tree,U)
  expr='Lean.Json.mkObj [("source",otj (restrict '+us+' '+ss+')),("target",otj (restrict '+us+' '+tt+')),("local_agreement",Lean.toJson (agreement '+tree(u)+' '+tree(v)+' '+parts(fa)+'))]'
  row(restlines,f['id']+'/local/'+str(U),expr,{'source':tj(u),'target':tj(v),'local_agreement':bool(m.g.agrees(m.g.Original(u),m.g.Original(v),fa))})
 for side,model,tr in [('S',S,ss),('T',T,tt)]:
  for U in Q:
   sub=[list(x) for k in range(len(U)+1) for x in itertools.combinations(U,k)];local=m.g.Original(m.g.raw_restrict(model.tree,U));lt=tree(local.tree);us=natlist(U)
   for B in sub:
    bs=natlist(B);want=m.transport(model,U,B)
    # Raw original and local occupied vertex lists each compared as sets to BFS hull.
    row(restlines,f['id']+'/path/'+side+'/'+str(U)+'/'+str(B),jsonexpr_pairs([('original',f'minimalVertices {bs} {tr}'),('local',f'minimalVertices {bs} {lt}'),('nested_equal',f'decide (restrict {bs} {lt} = restrict {bs} {tr})')]),{'original':[[c=='1' for c in p] for p in sorted(model.hull(frozenset(B)))],'local':[[c=='1' for c in p] for p in sorted(local.hull(frozenset(B)))],'nested_equal':True});counts['restriction_path_rows']+=1
   for i,B in enumerate(sub):
    for j,C in enumerate(sub):
     bs,cs=natlist(B),natlist(C);orig=not bool(model.hull(frozenset(B))&model.hull(frozenset(C)));loc=not bool(local.hull(frozenset(B))&local.hull(frozenset(C)));assert orig==loc
     row(restlines,f['id']+'/transport/'+side+'/'+str(U)+'/'+str(i)+'/'+str(j),jsonexpr_pairs([('original',f'disjointVertices (minimalVertices {bs} {tr}) (minimalVertices {cs} {tr})'),('local',f'disjointVertices (minimalVertices {bs} {lt}) (minimalVertices {cs} {lt})')]),{'original':orig,'local':loc});counts['embedding_pair_transport']+=1
# Malformed Q/F, empty/duplicate/missing local families and rooted topology guard readouts.
S=m.g.Original([[0,1],[2,3]]);T=m.g.Original([[0,2],[1,3]]);st=tree(S.tree)
for tag,ps in [('Q'+str(i),x) for i,x in enumerate(pin['false_controls']['invalid_Qs'])]+[('F'+str(i),x) for i,x in enumerate(pin['false_controls']['invalid_Fs'])]:
 row(restlines,'malformed/'+tag,'Lean.toJson (partitionCheck (leaves '+st+') '+parts(ps)+')',False)
for name in ['empty_local_family','duplicate_local_block','missing_local_family']:
 fam=pin['false_controls'][name]['families'];Q=[[0,1],[2,3]];pred=[]
 for U,famU in zip(Q,fam):
  lt=tree(m.g.raw_restrict(S.tree,U));pred.append(f'agreement {lt} {lt} {parts(famU)}')
 if len(fam)!=len(Q):pred.append('false')
 row(restlines,'badlocal/'+name,'Lean.toJson ('+' && '.join(pred)+')',False);counts['negative_local_families']+=1
w=pin['false_controls']['wrong_rooted_topology'];row(restlines,'wrongroot','Lean.toJson (agreement '+tree(w['S'])+' '+tree(w['T'])+' '+parts(w['families'][0])+')',False)
for f in clear['cases']:
 ps=parts(f['expected_bad_Q']);S,T=m.g.Original(f['S']),m.g.Original(f['T']);locals_=[]
 for U in f['expected_bad_Q']:locals_.append(f'agreement {tree(m.g.raw_restrict(S.tree,U))} {tree(m.g.raw_restrict(T.tree,U))} {parts([U])}')
 row(restlines,f['id']+'/reverseguard',jsonexpr_pairs([('source',f'pairwiseEmbeddings {tree(S.tree)} {ps}'),('target',f'pairwiseEmbeddings {tree(T.tree)} {ps}'),('local', ' && '.join(locals_)),('global',f'agreement {tree(S.tree)} {tree(T.tree)} {ps}')]),{'source':True,'target':False,'local':True,'global':False})
def run():
 (HERE/'ACTUAL-READOUT-EXPECTATIONS-v2.json').write_text(json.dumps({'counts':counts,'rows':expected},indent=2)+'\n')
 for kind,lines,name in [('rank',ranklines,'FreshRankReadoutV2'),('restriction',restlines,'FreshRestrictionReadoutV2')]:
  folder=a.BUILD/kind;(folder/(name+'.lean')).write_text('\n'.join(lines)+'\n');log=a.compile_one(folder,name);seen={}
  for line in log.splitlines():
   if line.startswith('READOUT|'):
    _,id,val=line.split('|',2);assert id not in seen;seen[id]=json.loads(val)
  ids=[id for id in expected if ('#eval emit '+json.dumps(id)+' (') in '\n'.join(lines)]
  assert set(ids)==set(seen),(kind,len(ids),len(seen))
  for id,actual in seen.items():
   want=expected[id]
   # Lists of occupied vertices are mathematical sets; no order asserted by pin.
   if '/path/' in id:
    for k in ['original','local']:actual[k]=sorted(actual[k]);want[k]=sorted(want[k])
   ok=actual==want;a.state['comparisons'].append({'id':id,'actual':actual,'expected':want,'passed':ok});a.save();assert ok,(id,actual,want)
 a.state['denominators']=counts;a.state['verdict']='PASS-ACTUAL-DEFINITION-READOUTS-AGAINST-PRECONTACT-ORIGINAL-INSTRUMENTS';a.save();print(json.dumps({'status':a.state['verdict'],'comparisons':len(expected),'counts':counts}))
if __name__=='__main__':
 try:run()
 except Exception as e:a.state['verdict']='OPEN-ACTUAL-READOUT-FAILURE';a.state['error']=repr(e);a.save();raise
