"""One-shot independent recovery-control instrument; not candidate recovery.
Reuses own frozen Graph and Ledger lineage, with zero extra replications.
No candidate/prover/author audit imports. No universal theorem follows here.
"""
from pathlib import Path
import importlib.util,sys,json,copy,argparse,time,hashlib
from collections import Counter
from fractions import Fraction
b=Path(__file__).resolve().parent
def module(name):
 spec=importlib.util.spec_from_file_location('final_cuts_'+name,b/'frozen-inputs'/(name+'.py'));m=importlib.util.module_from_spec(spec);sys.modules[spec.name]=m;spec.loader.exec_module(m);return m
old=module('original_graph');core=module('core_ledger')
def canon(bs):return sorted([sorted(x) for x in bs])
def equiv(a,c):return canon(a)==canon(c)
class Events:
 def __init__(self):self.rows=[]
 def emit(self,k,n=1):self.rows.append({'id':len(self.rows),'kind':k,'amount':n})
def certificate(tree,blocks,cuts):
 g=old.Graph(tree);actual=all(x and x in g.at for x in cuts);removed=set();orient=[]
 for x in cuts:
  if x and x in g.at:
   u,v=g.at[x[:-1]],g.at[x];removed.add(frozenset([u,v]));orient.extend([[x[:-1],x],[x,x[:-1]]])
 unseen=set(g.address);components=[]
 while unseen:
  start=min(unseen,key=lambda x:(len(g.address[x]),g.address[x]));todo=[start];seen=set()
  while todo:
   v=todo.pop()
   if v not in unseen:continue
   unseen.remove(v);seen.add(v);todo.extend(w for w in g.adj[v] if frozenset([v,w]) not in removed)
  vertices=sorted(g.address[v] for v in seen);labels=sorted(g.label[v] for v in seen if v in g.label)
  components.append({'root':min(vertices,key=lambda x:(len(x),x)),'vertices':vertices,'labels':labels})
 components.sort(key=lambda x:x['root']);leafless=sum(not x['labels'] for x in components)
 exact=bool(actual and len(set(cuts))==len(cuts) and not leafless and equiv([x['labels'] for x in components],blocks) and len(components)==len(cuts)+1==len(blocks))
 return {'actual_edges':bool(actual),'distinct_cuts':len(set(cuts))==len(cuts),'cut_count':len(cuts),'component_count':len(components),'leafless_count':leafless,'exact':exact,'components':components,'removed_orientations':orient,'vertices':sorted(g.at),'all_original_vertices':len(g.at),'cuts':cuts[:]}
def target_agrees(s,t,p):return old.evaluate('agreement',{'left':s,'right':t,'blocks':p})['agreement']
def evaluate(c):
 d=c['input'];op=c['op'];e=Events()
 if op=='recover':
  g=old.Graph(d['tree']);p=d['partition'];labels=g.labels;e.emit('guard.nodup_calls');seen=[];distinct=True
  for x in labels:
   for y in seen:
    e.emit('guard.nodup_comparisons')
    if x==y:distinct=False;break
   if not distinct:break
   seen.append(x)
  e.emit('guard.partition_calls');pc=bool(old.partition(labels,p));e.emit('guard.embedding_calls');emb=g.embeddings(p)
  v={'guards':{'distinct':distinct,'partition':pc,'embeddings':emb},'success':False,'budget':None,'raw_count':0,'outputs':[],'output_costs':[],'colors':{},'color_count':0,'first_head_accesses':0,'source_vertex_count':len(g.at),'target_agreement':target_agrees(d['tree'],d['target'],p) if 'target' in d else None,'target_transport_licensed':False,'output_equivalent':False,'realized':False,'label_bits':max(max(1,x.bit_length()) for x in labels),'color_bits':1,'mass':{x:'0' for x in ['2','233/100','3']}}
  if distinct and pc and emb:
   colors={}
   def color(x):
    e.emit('color.calls')
    for block in p:
     e.emit('color.block_inspections');hit=False
     for y in block:
      e.emit('color.label_comparisons')
      if x==y:hit=True;break
     if hit:
      assert block;e.emit('color.first_head');colors[str(x)]=block[0];return block[0]
    raise AssertionError('admitted label lacks a containing block')
   k=max(0,len(p)-1);e.emit('recovery.generate_calls');ledger=core.Ledger({});ledger.raw_color=color;r=ledger.generate(d['tree'],k)
   for row in ledger.events:e.emit('core.'+row['kind'],row['amount'])
   e.emit('recovery.head_selection');out=r.outputs[0] if r.outputs else None
   v.update({'budget':k,'raw_count':len(r.outputs),'outputs':r.outputs,'output_costs':[len(x['cuts']) for x in r.outputs],'success':out is not None,'colors':colors,'color_count':len(set(colors.values())),'first_head_accesses':sum(x['amount'] for x in e.rows if x['kind']=='color.first_head'),'color_bits':max(max(1,x.bit_length()) for x in colors.values()),'output_equivalent':out is not None and equiv(out['partition'],p)})
   if out:
    cert=certificate(d['tree'],p,out['cuts']);v['certificate']=cert;v['realized']=cert['exact'];v['target_transport_licensed']=bool(v['realized'] and v['target_agreement'] is True)
   v['mass']={base:str(sum((Fraction(base)**(-len(x['cuts'])) for x in r.outputs),Fraction())) for base in ['2','233/100','3']}
 elif op=='certificate':v=certificate(d['tree'],d['partition'],d['cuts'])
 elif op=='permutation':v={'equivalent':equiv(d['left'],d['right'])}
 elif op=='edges':
  g=old.Graph(d['tree']);prototype=old.Graph([0,2]);assert g.signature([0,2])==prototype.signature([0,2]);v={'actual':[g.actual_edge(a,z) for a,z in d['pairs']],'local_zero_original_leafset':sorted(x for i,x in g.label.items() if g.address[i].startswith('0')),'selected_zero_leafset':sorted(x for i,x in prototype.label.items() if prototype.address[i].startswith('0'))}
 elif op=='absorption':
  e.emit('recovery.materialized_calls',d['calls']);factor=2**d['k'];charge=d['calls']*factor;v={'premises':d['k']<=d['q'] and Fraction(d['c'])>=2,'single_recovery':d['calls']==1,'factor':factor,'charged':charge,'absorbed':charge<=Fraction(d['c'])**d['q']}
 else:raise ValueError(op)
 counts={}
 for x in e.rows:counts[x['kind']]=counts.get(x['kind'],0)+x['amount']
 return {'id':c['id'],'value':v,'events':e.rows,'counts':counts,'metadata':{'candidate_contact':False,'scientific_candidate_builds':0,'fine_instruction_identity':False,'replications_added':0}}
def at(obj,path):
 for k in path.split('.'):obj=obj[int(k)] if isinstance(obj,list) else obj[k]
 return obj
def validate(r,c):
 if r['metadata']!={'candidate_contact':False,'scientific_candidate_builds':0,'fine_instruction_identity':False,'replications_added':0}:return False
 if [x['id'] for x in r['events']]!=list(range(len(r['events']))):return False
 counts={}
 for x in r['events']:
  if x['amount']<0:return False
  counts[x['kind']]=counts.get(x['kind'],0)+x['amount']
 if counts!=r['counts']:return False
 for path,x in c['expected'].items():
  if at(r['value'],path)!=x:return False
 for k,x in c['counts'].items():
  if counts.get(k,0)!=x:return False
 if any(counts.get(k,0)<=0 for k in c['positive_counts']):return False
 cert=(r['value'].get('certificate') if c['op']=='recover' else r['value'] if c['op']=='certificate' else None)
 if cert:
  g=old.Graph(c['input']['tree']);vertices=[x for z in cert['components'] for x in z['vertices']]
  if Counter(vertices)!=Counter(g.at.keys()) or cert['vertices']!=sorted(g.at):return False
  if cert['all_original_vertices']!=len(g.at) or cert['component_count']!=len(cert['components']):return False
  for cut in cert['cuts']:
   if cut and cut in g.at:
    if [cut[:-1],cut] not in cert['removed_orientations'] or [cut,cut[:-1]] not in cert['removed_orientations']:return False
 if c['op']=='recover' and r['value']['success']:
  v=r['value'];p=c['input']['partition']
  if len(v['outputs'])!=1 or len(set(v['colors'].values()))!=len(p):return False
  for x,y in v['colors'].items():
   if not any(int(x) in z and z and z[0]==y for z in p):return False
  if v['mass']!=json.loads((b/'CONTROL-PIN.json').read_text())['mass_expectations'][str(len(p)-1)]:return False
 return True
def corrupt(r,p):
 r=copy.deepcopy(r);v=r['value'];kind=p['kind']
 if kind=='value':
  keys=p['path'].split('.');o=v
  for k in keys[:-1]:o=o[int(k)] if isinstance(o,list) else o[k]
  k=keys[-1]
  if isinstance(o,list):o[int(k)]=p['replacement']
  else:o[k]=p['replacement']
 elif kind=='metadata_fine':r['metadata']['fine_instruction_identity']=True
 elif kind=='color_collision':v['colors'][p['from']]=p['to']
 elif kind=='zero_event':
  for x in r['events']:
   if x['kind']==p['path']:x['amount']=0
  r['counts']={}
  for x in r['events']:r['counts'][x['kind']]=r['counts'].get(x['kind'],0)+x['amount']
 else:
  cert=v.get('certificate',v)
  if kind=='drop_original_vertex':
   vertex='01' if '01' in cert['vertices'] else ''
   for z in cert['components']:
    if vertex in z['vertices']:z['vertices'].remove(vertex)
  elif kind=='drop_leafless':
   cert['components']=[x for x in cert['components'] if x['labels']];cert['component_count']=len(cert['components']);cert['leafless_count']=0
  elif kind=='omit_reverse_edge':cert['removed_orientations'].pop()
  else:raise ValueError(kind)
 return r
def main():
 a=argparse.ArgumentParser();a.add_argument('--phase',choices=['pilot','size-pilot','full'],required=True);a.add_argument('--out',required=True);args=a.parse_args();pin=json.loads((b/'CONTROL-PIN.json').read_text());cs=pin['controls']
 if args.phase!='full':cs=[c for c in cs if c['id'] in pin['pilot_ids' if args.phase=='pilot' else 'size_pilot_ids']]
 assert len(cs)>0;rows=[];start=time.perf_counter()
 for c in cs:
  t=time.perf_counter();r=evaluate(c);ok=validate(r,c)
  if not ok:print(json.dumps({'FAILED_CLEAN':c['id'],'actual':r,'control':c}));raise AssertionError(c['id'])
  plants=[]
  for p in c['plants']:
   bad=corrupt(r,p);caught=not validate(bad,c)
   if not caught:print(json.dumps({'FAILED_PLANT':c['id'],'plant':p}));raise AssertionError((c['id'],p))
   plants.append({'plant':p,'caught':True,'value_preserved':bad['value']==r['value']})
  rows.append({'id':c['id'],'seconds':time.perf_counter()-t,'report':r,'plants':plants})
 result={'status':'PASS-PRE-CANDIDATE-INSTRUMENT-ONLY','phase':args.phase,'clean':len(rows),'plants_caught':sum(len(x['plants']) for x in rows),'elapsed_seconds':time.perf_counter()-start,'rows':rows,'candidate_content_contact':False,'scientific_candidate_builds':0,'additional_replications':0};Path(args.out).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='rows'}))
if __name__=='__main__':main()
