#!/usr/bin/env python3
"""Postcontact exact fixed24 original-graph readout checks; no new census."""
import collections,json,pathlib,time
P=pathlib.Path(__file__).resolve().parent
def normal(f):return tuple(sorted(tuple(sorted(b)) for b in f))
def graph(t):
 adj=collections.defaultdict(set);ls={}
 def visit(t,p):
  adj[p]
  if isinstance(t,int):ls[t]=p;return
  for b,c in enumerate(t):
   q=p+str(b);adj[p].add(q);adj[q].add(p);visit(c,q)
 visit(t,'');return adj,ls
def path(adj,a,b):
 q=collections.deque([a]);parent={a:None}
 while q:
  x=q.popleft()
  if x==b:break
  for y in adj[x]:
   if y not in parent:parent[y]=x;q.append(y)
 out=set();x=b
 while x is not None:out.add(x);x=parent[x]
 return out
def hull(adj,ls,B):
 first=ls[B[0]];return sorted(set.union(*(path(adj,first,ls[x]) for x in B)))
def components(adj,ls,cut):
 removed=set() if cut is None else {frozenset([cut[:-1],cut])}
 seen=set();out=[]
 for v in adj:
  if v in seen:continue
  q=[v];seen.add(v);vs=set()
  while q:
   x=q.pop();vs.add(x)
   for y in adj[x]:
    if y not in seen and frozenset([x,y]) not in removed:seen.add(y);q.append(y)
  labels=sorted(x for x,p in ls.items() if p in vs)
  if labels:out.append(labels)
 return normal(out)
start=time.perf_counter();registry=json.loads((P/'ACTUAL-CONTROL-REGISTRY-v1.json').read_text());results=[]
for r in registry:
 m=r['module'];files=list((P/'control-results').glob('*/'+m+'.stdout'));assert len(files)==1
 a=json.loads(files[0].read_text());e=r['expected'];checks={};hull_count=0
 gs=[graph(e['T']),graph(e['S'])]
 for i,f in enumerate(e['minima'][0]):
  for j,B in enumerate(f):
   for k,(adj,ls) in enumerate(gs):
    actual=sorted(''.join('1' if b else '0' for b in v) for v in a['hulls'][i][j][k])
    checks[f'hull-{i}-{j}-{k}']=actual==hull(adj,ls,B);hull_count+=1
 cut_count=0
 for i,pair in enumerate(a['pairs']):
  q=pair['pretest'];c=q['cut'];cut=None if c is None else ''.join('1' if b else '0' for b in c)
  adj,ls=graph(pair['S']);checks[f'cut-{i}-is-actual-edge']=cut is None or bool(cut) and cut in adj and cut[:-1] in adj[cut]
  checks[f'cut-{i}-components']=components(adj,ls,cut)==normal(q['forest'])
  checks[f'cut-{i}-is-frozen-minimum']=normal(q['forest']) in [normal(f) for f in e['minima'][i]]
  checks[f'cut-{i}-cost']=int(cut is not None)==q['cost']==e['costs'][i];cut_count+=1
 result={'case_id':r['case_id'],'checks':checks,'hull_readouts':hull_count,'actual_cut_readouts':cut_count,'status':'PASS' if all(checks.values()) else 'MISMATCH'};results.append(result)
out={'status':'PASS_POSTCONTACT_FIXED_BANK_GRAPH_READOUTS' if all(r['status']=='PASS' for r in results) else 'MISMATCH','cases':len(results),'hull_readouts':sum(x['hull_readouts'] for x in results),'actual_cut_readouts':sum(x['actual_cut_readouts'] for x in results),'results':results,'seconds':time.perf_counter()-start,'additional_replication_credit':0,'limits':['same old24 only','host BFS and old X0 share original-graph lineage','postcontact interface validation, not new blind truth','only exposed0/1 pretest cuts, not a general graph witness extractor']}
(P/'ACTUAL-CUT-HULL-RESULT-v1.json').write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps({k:out[k] for k in ['status','cases','hull_readouts','actual_cut_readouts','seconds']}))
if out['status']=='MISMATCH':raise RuntimeError('preserve actual mismatch')
