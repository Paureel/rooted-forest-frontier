#!/usr/bin/env python3
import argparse,copy,json,time
from pathlib import Path
from collections import Counter
from fractions import Fraction
import core_ledger as core
HERE=Path(__file__).resolve().parent

def at(x,p):
 if p=='$':return x
 for k in p.split('.'):x=x[int(k)] if isinstance(x,list) else x[k]
 return x
class Events:
 def __init__(self):self.events=[]
 def emit(self,k,n=1,sizes=None):self.events.append({'id':len(self.events),'kind':k,'amount':n,'argument_sizes':sizes or []})

def schedule(q,resolved,slots,solve,e):
 e.emit('query.pretest');known=0
 for r in resolved:e.emit('query.resolved_cells');e.emit('query.cost_additions');known+=r['cost']
 e.emit('query.slot_length_cells',len(slots));p=len(slots)
 e.emit('query.guard_arithmetic',3)
 if known+2*p>q:return {'accepted':False,'reason':'early','known':known,'p':p,'budget':None,'cost':known,'trace':[]}
 budget=q-known-2*max(0,p-1);e.emit('query.budget_arithmetic',4)
 trace=[];cost=known
 for i,s in enumerate(slots):
  e.emit('query.actual_calls');r=solve(i,s,budget);trace.append(copy.deepcopy(r));e.emit('query.trace_cells')
  if not r['success']:return {'accepted':False,'reason':'failure','known':known,'p':p,'budget':budget,'cost':cost,'trace':trace}
  e.emit('query.returned_sum_cells');e.emit('query.cost_additions');cost+=r['cost']
 e.emit('query.final_sum_check')
 return {'accepted':cost<=q,'reason':'accept' if cost<=q else 'sum','known':known,'p':p,'budget':budget,'cost':cost,'trace':trace}

class Mock:
 def __init__(self,minima):self._minima=minima;self.spy=[]
 def invoke(self,i,s,budget):
  m=self._minima[i];success=m<=budget
  r={'index':i,'slot':s,'budget':budget,'success':success,'cost':m if success else None,'witness':['slot',i,s,'minimum',m] if success else None}
  self.spy.append(copy.deepcopy(r));return r

def classifier(d,e):
 q=d['q'];trace=[];tariff=d.get('tariff',1)
 def generate(budget,phase):
  e.emit('probe.generate_calls');engine=core.Ledger({'oracle_tariff':tariff})
  def color(x):e.emit('probe.color_calls');e.emit('probe.oracle_tariff',tariff);return x//2
  engine.raw_color=color;r=engine.generate(d['source'],budget)
  call={'phase':phase,'budget':budget,'callbacks':sum(z['amount'] for z in engine.events if z['kind']=='oracle.color_calls'),'outputs':r.outputs,'costs':[len(o['cuts']) for o in r.outputs],'pruned':r.pruned}
  trace.append(call);return r.outputs
 e.emit('probe.q_guard')
 if q<3:return {'outputs':[],'costs':[],'trace':[],'path':'below-three','rank_calls':0}
 probe=generate(3,'probe');e.emit('probe.nonempty_check')
 if probe:return {'outputs':probe,'costs':[len(o['cuts']) for o in probe],'trace':trace,'path':'reuse','rank_calls':0}
 out=generate(q,'full');return {'outputs':out,'costs':[len(o['cuts']) for o in out],'trace':trace,'path':'full','rank_calls':0}

def evaluate(c):
 d=c['input'];e=Events();spy=[];op=c['op']
 if op=='query':
  m=Mock(d['minima']);v=schedule(d['q'],d.get('resolved',[]),d['slots'],m.invoke,e);spy=m.spy
  bad=len(d['slots'])+sum(r['cost']>0 for r in d.get('resolved',[]));mass={}
  for s in ['2','233/100','3']:
   base=Fraction(s);a=sum((base**(r['budget']-d['q']) for r in spy),Fraction(0));mass[s]={'exact':str(a),'discount_holds':a<=1/base}
  v.update({'bad':bad,'discount_eligible':bad>=2,'mass':mass})
 elif op=='classify':v=classifier(d,e)
 elif op=='rank':
  vals=[];seen=[]
  for x in core.raw_labels(d['source']):
   e.emit('rank.color_calls');e.emit('rank.oracle_tariff',d.get('tariff',1));y=x//2;vals.append(y)
   duplicate=False
   for z in seen:
    e.emit('rank.equality_calls')
    if y==z:duplicate=True;break
   if not duplicate:seen.append(y);e.emit('rank.kept_cells')
  v={'rank':len(seen),'values':vals,'colors':seen}
 elif op=='trace_builder':
  out=[]
  for i in range(d['calls']):
   e.emit('trace_builder.append_calls');e.emit('trace_builder.left_cells',len(out));e.emit('trace_builder.cell_upper_ops',8*len(out));out=out+[i]
  v={'trace':out,'calls':len(out),'linear_cons_reverse_cells':2*len(out)}
 else:raise ValueError(op)
 counts={}
 for x in e.events:counts[x['kind']]=counts.get(x['kind'],0)+x['amount']
 labels=core.raw_labels(d['source']) if 'source' in d else []
 metadata={'q_bits':max(1,d.get('q',0).bit_length()),'label_bits':max([max(1,x.bit_length()) for x in labels] or [1]),'tariff':d.get('tariff',1),'symbolic_floor_color_bits':max([max(1,(x//2).bit_length()) for x in labels] or [1]),'no_machine_time_claim':True,'minima_access_in_caller':False,'core_lineage':'byte-identical prior independent ledger;zero new replications'}
 return {'id':c['id'],'value':v,'counts':counts,'events':e.events,'spy':spy,'metadata':metadata}

def validate(r,c):
 if r['metadata'].get('minima_access_in_caller') is not False:return False
 if [x['id'] for x in r['events']]!=list(range(len(r['events']))):return False
 totals={}
 for x in r['events']:
  if x['amount']<0:return False
  totals[x['kind']]=totals.get(x['kind'],0)+x['amount']
 if totals!=r['counts']:return False
 if c['op']=='query':
  if r['value']['trace']!=r['spy']:return False
  if r['counts'].get('query.actual_calls',0)!=len(r['spy']):return False
  for z in r['spy']:
   i=z['index'];m=c['input']['minima'][i]
   if z['slot']!=c['input']['slots'][i] or z['success']!=(m<=z['budget']):return False
   if z['success'] and (z['cost']!=m or z['witness']!=['slot',i,z['slot'],'minimum',m]):return False
 for p,x in c.get('value_fields',{}).items():
  if at(r['value'],p)!=x:return False
 for k,x in c.get('counts',{}).items():
  if r['counts'].get(k,0)!=x:return False
 for k in c.get('positive_counts',[]):
  if r['counts'].get(k,0)<=0:return False
 for k,x in c.get('metadata',{}).items():
  if r['metadata'].get(k)!=x:return False
 return True

def corrupt(r,p):
 r=copy.deepcopy(r);kind=p['kind']
 if kind in ['zero','omit']:
  if kind=='zero':
   for x in r['events']:
    if x['kind']==p['target']:x['amount']=0
  else:r['events']=[x for x in r['events'] if x['kind']!=p['target']]
  r['counts']={}
  for i,x in enumerate(r['events']):x['id']=i;r['counts'][x['kind']]=r['counts'].get(x['kind'],0)+x['amount']
 elif kind in ['value','metadata']:
  obj=r['value'] if kind=='value' else r['metadata'];keys=p['target'].split('.')
  for k in keys[:-1]:obj=obj[int(k)] if isinstance(obj,list) else obj[k]
  k=keys[-1]
  if isinstance(obj,list):obj[int(k)]=p['replacement']
  else:obj[k]=p['replacement']
 elif kind=='omit_trace':r['value']['trace'].pop()
 elif kind=='duplicate_trace':r['value']['trace'].append(copy.deepcopy(r['value']['trace'][0]))
 elif kind=='wrong_IH':
  for xs in [r['spy'],r['value']['trace']]:
   xs[0]['cost']+=1;xs[0]['witness']=['wrong slot witness']
 elif kind=='duplicate_record':r['events'].append(copy.deepcopy(r['events'][0]))
 elif kind=='missing_record':r['events'].pop()
 else:raise ValueError(kind)
 return r

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--ids',nargs='*');ap.add_argument('--output',required=True);a=ap.parse_args();pin=json.loads((HERE/'CONTROL-PIN.json').read_text());cs=[c for c in pin['controls'] if not a.ids or c['id'] in a.ids];rows=[];t=time.perf_counter()
 for c in cs:
  t0=time.perf_counter();r=evaluate(c);assert validate(r,c),c['id'];ps=[]
  for p in c['plants']:
   bad=corrupt(r,p);caught=not validate(bad,c);assert caught,(c['id'],p);ps.append({'plant':p,'caught':True,'value_preserved':bad['value']==r['value']})
  rows.append({'id':c['id'],'seconds':time.perf_counter()-t0,'report':r,'plants':ps})
 out={'status':'PASS-PRE-CANDIDATE-FIXED-CONTROLS','cases':len(rows),'plants_caught':sum(len(x['plants']) for x in rows),'seconds':time.perf_counter()-t,'rows':rows,'scope':'same-lineage readiness only;no actual MAF solver/global recurrence/candidate acceptance'};Path(a.output).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='rows'}))
if __name__=='__main__':main()
