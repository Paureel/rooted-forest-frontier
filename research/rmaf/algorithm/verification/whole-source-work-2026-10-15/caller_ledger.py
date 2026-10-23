#!/usr/bin/env python3
"""Preregistered original-graph/callback/outer-list demands; no candidate imports.
The byte-identical prior independent core ledger is same-lineage reuse.
"""
import argparse,copy,json,time,hashlib
from pathlib import Path
from collections import Counter,deque
import core_ledger as core
HERE=Path(__file__).resolve().parent

def width(x):return max(1,int(x).bit_length())
def leaf_values(t):return [t] if isinstance(t,int) else leaf_values(t[0])+leaf_values(t[1])
def field(obj,path):
 if path=='$':return obj
 for k in path.split('.'):obj=obj[int(k)] if isinstance(obj,list) else obj[k]
 return obj

class Caller:
 def __init__(self,d):
  self.d=d;self.events=[];self.nodes=[];self.labels=[];self.adj={};self.core_runs=[];self.identifiers=[]
  if 'target' in d:self.build(d['target'])
 def emit(self,k,n=1,sizes=None):self.events.append({'id':len(self.events),'kind':k,'amount':n,'argument_sizes':sizes or []})
 def build(self,t,p=''):
  self.emit('target.build_nodes');self.nodes.append(p);self.adj.setdefault(p,[])
  if p:self.adj[p].append(p[:-1]);self.adj[p[:-1]].append(p);self.emit('target.edge_cells',2)
  if isinstance(t,int):self.labels.append((t,p));return
  self.build(t[0],p+'0');self.build(t[1],p+'1')
 def member(self,x,xs):
  self.emit('membership.calls')
  for y in xs:
   self.emit('membership.label_comparisons',sizes=[width(x),width(y)])
   if x==y:return True
  return False
 def lookup(self,x):
  self.emit('leaf.lookup_calls')
  byaddr={p:y for y,p in self.labels}
  for p in self.nodes:
   self.emit('leaf.lookup_nodes')
   if p in byaddr:
    y=byaddr[p];self.emit('leaf.lookup_label_comparisons',sizes=[width(x),width(y)])
    if x==y:return p
  return None
 def component(self,start,removed):
  if start in removed:return set()
  seen={start};q=deque([start])
  while q:
   p=q.popleft();self.emit('graph.component_nodes')
   for a in self.adj[p]:
    self.emit('graph.adjacency_cells')
    if a not in removed and a not in seen:seen.add(a);q.append(a)
  return seen
 def region(self,v,a):
  self.emit('region.calls');self.emit('region.address_capacity',len(v)+len(a)+1,[len(v),len(a)])
  if v not in self.adj:return None
  if a==v:return 3
  c=self.component(a,{v})
  if v+'0' in c:return 0
  if v+'1' in c:return 1
  if v and v[:-1] in c:return 2
  raise AssertionError(('region',v,a,c))
 def path(self,a,b):
  todo=deque([a]);prev={a:None}
  while todo:
   x=todo.popleft();self.emit('graph.path_nodes')
   if x==b:break
   for y in self.adj[x]:
    self.emit('graph.path_edges')
    if y not in prev:prev[y]=x;todo.append(y)
  assert b in prev
  out=[];x=b
  while x is not None:out.append(x);x=prev[x]
  return out
 def selected(self,D):
  return [p for x,p in self.labels if self.member(x,D)]
 def hull(self,D):
  leaves=self.selected(D);out=set()
  for i,a in enumerate(leaves):
   for b in leaves[i:]:out.update(self.path(a,b))
  return sorted(out)
 def callback(self,x):
  self.emit('callback.invocations',sizes=[width(x)])
  ps=self.d['parents'];owners=[i for i,D in enumerate(ps) if self.member(x,D)]
  if len(owners)!=1:return {'invalid':'overlap' if owners else 'missing-parent'},None
  j=owners[0];active=self.d.get('active',0)
  if j!=active:
   code=(16 if self.d.get('mode')=='joint' else 4)+j
   self.emit('callback.encoding_ops',2);self.identifiers.append(code);return ['residue',j],code
  a=self.lookup(x)
  if a is None:return {'invalid':'missing-target-label'},None
  v=self.d.get('v','');r=self.region(v,a)
  if r is None:return {'invalid':'missing-target-vertex'},None
  if self.d.get('mode')=='joint':
   w=self.d['w'];s=self.region(w,a)
   if s is None:return {'invalid':'missing-target-vertex'},None
   self.emit('callback.encoding_ops',2);code=4*r+s;tag=['joint',r,s]
  else:self.emit('callback.encoding_ops');code=r;tag=['local',r]
  self.identifiers.append(code);return tag,code
 def append(self,domain,left,right):
  self.emit('outer.'+domain+'.append_calls');self.emit('outer.'+domain+'.left_cells',len(left),[len(left),len(right)])
  self.emit('outer.'+domain+'.cell_upper_ops',8*len(left));return left+right
 def materialize(self,lists,domain):
  if self.d.get('association','left')=='left':
   out=[]
   for xs in lists:out=self.append(domain,out,xs)
   return out
  out=[]
  for xs in reversed(lists):out=self.append(domain,xs,out)
  return out
 def dedup(self,xs):
  out=[]
  for x in xs:
   self.emit('dedup.input_cells');found=False
   for y in out:
    self.emit('dedup.record_comparisons',sizes=[len(json.dumps(x)),len(json.dumps(y))])
    if x==y:found=True;break
   if not found:out.append(x);self.emit('dedup.kept_cells')
  return out
 def alternatives(self,family):
  if family=='clique':return [[['local',1,'v'],['local',2,'v']],[['local',0,'v'],['local',2,'v']],[['local',0,'v'],['local',1,'v']]]
  if family=='chain':return [[['local',1,'v'],['local',2,'w']],[['joint',1,'v','w']],[['local',0,'v'],['local',2,'w']],[['local',0,'v'],['local',1,'w']]]
  return [[['joint',1,'v','w']],[['local',0,'v'],['local',2,'w']]]
 def generate(self):
  results=[];trace=[]
  for i,alternative in enumerate(self.alternatives(self.d['family'])):
   self.emit('caller.generate_invocations');e=core.Ledger({})
   def actual(x):
    tag,code=self.callback(x)
    if code is None:raise ValueError(('invalid callback',tag))
    return code
   e.raw_color=actual;r=e.generate(self.d['source'],self.d['budget']);v=core.rec_view(r)
   self.core_runs.append({'id':i,'events':e.events,'receipt':v})
   results.append(v);trace.append({'id':i,'alternative':alternative,'budget':self.d['budget'],'source':self.d['source'],'callbacks':sum(z['amount'] for z in e.events if z['kind']=='oracle.color_calls')})
  outputs=self.materialize([r['outputs'] for r in results],'outputs');refusals=self.materialize([r['refusals'] for r in results],'refusals')
  unique=self.dedup(outputs)
  return {'trace':trace,'raw_outputs':outputs,'raw_refusals':refusals,'dedup_outputs':unique,'raw_count':len(outputs),'refusal_count':len(refusals),'dedup_count':len(unique),'pruned':sum(r['pruned'] for r in results),'attempts':sum(r['childAttempts'] for r in results)}

def evaluate(c):
 d=c['input'];e=Caller(d);op=c['op']
 if op=='callbacks':
  tags=[];codes=[]
  for x in d['queries']:
   tag,code=e.callback(x);tags.append(tag);codes.append(code)
  val={'tags':tags,'codes':codes}
 elif op=='lookup':val={'addresses':[e.lookup(x) for x in d['queries']]}
 elif op=='hull':val={'hull':e.hull(d['selected'])}
 elif op=='regions':
  addrs=e.selected(d['selected']);pairs=[[e.region(d['v'],a),e.region(d['w'],a)] for a in addrs];unique=e.dedup(pairs)
  val={'leaf_addresses':addrs,'joint':pairs,'joint_codes':[4*r+s for r,s in pairs],'distinct_joint':unique,'joint_count':len(unique)}
 elif op=='selector':
  spans=[e.hull(D) for D in d['parents']];sets=list(map(set,spans));val={'spans':spans,'pair_overlap':[sorted(sets[0]&sets[1]),sorted(sets[0]&sets[2]),sorted(sets[1]&sets[2])],'triple_overlap':sorted(sets[0]&sets[1]&sets[2])}
 elif op=='schedule':val={'alternatives':e.alternatives(d['family']),'calls':len(e.alternatives(d['family']))}
 elif op=='outer':
  raw=e.materialize(d['outputs'],'outputs');ref=e.materialize(d.get('refusals',[[] for _ in d['outputs']]),'refusals');val={'raw':raw,'refusals':ref,'dedup':e.dedup(raw),'raw_count':len(raw)}
 elif op=='generate':val=e.generate()
 else:raise ValueError(op)
 counts=dict(Counter())
 for x in e.events:counts[x['kind']]=counts.get(x['kind'],0)+x['amount']
 labels=leaf_values(d['source']) if 'source' in d else []
 targetlabels=leaf_values(d['target']) if 'target' in d else []
 meta={'source_label_bits':max([width(x) for x in labels] or [1]),'target_label_bits':max([width(x) for x in targetlabels] or [1]),'budget_bits':width(d.get('budget',0)),'identifier_max_value':max(e.identifiers or [0]),'identifier_max_bits':max([width(x) for x in e.identifiers] or [1]),'cell_multiplier':8,'reference_encoding':'local0..3/residue4+j;joint4*r+s/residue16+j','no_machine_time_claim':True}
 return {'id':c['id'],'value':val,'counts':counts,'metadata':meta,'events':e.events,'core_runs':e.core_runs}

def validate(r,c):
 ids=[x['id'] for x in r['events']]
 if ids!=list(range(len(ids))):return False
 totals={}
 for x in r['events']:
  if x['amount']<0:return False
  totals[x['kind']]=totals.get(x['kind'],0)+x['amount']
 if totals!=r['counts']:return False
 for run in r['core_runs']:
  if [x['id'] for x in run['events']]!=list(range(len(run['events']))):return False
 for p,want in c.get('value_fields',{}).items():
  if field(r['value'],p)!=want:return False
 for k,want in c.get('counts',{}).items():
  if r['counts'].get(k,0)!=want:return False
 for k in c.get('positive_counts',[]):
  if r['counts'].get(k,0)<=0:return False
 for k,want in c.get('metadata',{}).items():
  if r['metadata'].get(k)!=want:return False
 return True

def corrupt(r,p):
 r=copy.deepcopy(r);kind=p['kind']
 if kind in ['zero','omit']:
  k=p['target']
  if kind=='zero':
   for x in r['events']:
    if x['kind']==k:x['amount']=0
  else:r['events']=[x for x in r['events'] if x['kind']!=k]
  for i,x in enumerate(r['events']):x['id']=i
  r['counts']={}
  for x in r['events']:r['counts'][x['kind']]=r['counts'].get(x['kind'],0)+x['amount']
 elif kind=='duplicate_record':r['events'].append(copy.deepcopy(r['events'][0]))
 elif kind=='missing_record':r['events'].pop()
 elif kind=='value':
  keys=p['target'].split('.');obj=r['value']
  for k in keys[:-1]:obj=obj[int(k)] if isinstance(obj,list) else obj[k]
  k=keys[-1]
  if isinstance(obj,list):obj[int(k)]=p['replacement']
  else:obj[k]=p['replacement']
 elif kind=='metadata':r['metadata'][p['target']]=p['replacement']
 else:raise ValueError(kind)
 return r

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--ids',nargs='*');ap.add_argument('--output',required=True);args=ap.parse_args()
 pin=json.loads((HERE/'CONTROL-PIN.json').read_text());selected=[c for c in pin['controls'] if not args.ids or c['id'] in args.ids]
 t=time.perf_counter();rows=[]
 for c in selected:
  start=time.perf_counter();r=evaluate(c);assert validate(r,c),c['id'];plants=[]
  for p in c['plants']:
   bad=corrupt(r,p);caught=not validate(bad,c);assert caught,(c['id'],p);plants.append({'plant':p,'caught':caught,'value_preserved':bad['value']==r['value']})
  rows.append({'id':c['id'],'seconds':time.perf_counter()-start,'report':r,'plants':plants})
 receipt={'status':'PASS-FIXED-PRE-CANDIDATE-CONTROLS','cases':len(rows),'plants_caught':sum(len(r['plants']) for r in rows),'seconds':time.perf_counter()-t,'rows':rows,'scope':'Readiness of independent same-lineage source-envelope controls only; no candidate acceptance,cycle bound or extra replication.'}
 Path(args.output).write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({k:v for k,v in receipt.items() if k!='rows'}))
if __name__=='__main__':main()
