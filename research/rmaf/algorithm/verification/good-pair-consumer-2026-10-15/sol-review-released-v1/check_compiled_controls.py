#!/usr/bin/env python3
"""Independent comparison against immutable prepared fixtures and raw receipts."""
import copy,hashlib,importlib.util,json
from fractions import Fraction as F
from pathlib import Path
P=Path(__file__).resolve().parent;PREP=P.parent/'sol-preparation-READY-v1/preparation'
sp=importlib.util.spec_from_file_location('prep',PREP/'instrument/prepare_graph_controls.py');m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m)
data=json.loads((PREP/'fixtures-v1.json').read_text());plan=json.loads((P/'CONTROL-ADAPTER-PLAN-v1.json').read_text());rows=[json.loads(z)for z in(P/'compiled-controls-v1.jsonl').read_text().splitlines()];checks=[];maps=[];coverage=0;call_den=0;output_den=0
lookup={f['id']:f for f in data['fixtures']};negative={f['id']:f for f in data['premise_corruptions']}
def add(name,got,want=True):checks.append({'name':name,'got':got,'expected':want,'pass':got==want})
add('complete declared row denominator',len(rows),30)
for row in rows:
 if row.get('boundary_only'):
  add('duplicate source labels refused',row['duplicate_core_refusals'],['duplicate original label']);add('compiled sibling swap',row['sibling_order_same']);continue
 name=row['id'];q=row['q']
 if name in lookup:
  f=lookup[name];s,t=m.x.Graph(f['S']),m.x.Graph(f['T']);expected=m.calls_for(f,q);actual=row['calls'];call_den+=len(actual);output_den+=len(row['outputs'])
  expectedchoice=plan['expected_selectors'][name]
  add(name+' selector q'+str(q),{k:row['choice'][k]for k in expectedchoice},expectedchoice)
  add(name+' all compiled premises q'+str(q),all(row['guards'].values()))
  add(name+' retained call identities q'+str(q),[z['identity']for z in actual],[z['identity']for z in expected])
  for j,(a,e)in enumerate(zip(actual,expected)):
   add(name+' full raw receipt q'+str(q)+' call'+str(j),a['receipt'],e['receipt'])
   ac=dict(a['colors']);ec=e['colors'];same=set(ac)==set(ec) and all((ac[u]==ac[v])==(ec[u]==ec[v])for u in ac for v in ac)
   add(name+' equality-class color adapter q'+str(q)+' call'+str(j),same)
   if q==f['q']:maps.append({'fixture':name,'call':a['identity'],'literal_lean_colors':a['colors'],'prepared_python_colors':ec,'equality_classes_identical':same})
  expectedos=m.raw_outputs(expected);add(name+' actual total list q'+str(q),row['outputs'],expectedos)
  add(name+' compiled Q agreement matches graph q'+str(q),row['Q_agreement'],[m.x.agreement(s,t,s.labels,o['partition'])for o in row['outputs']])
  for o in row['outputs']:add(name+' original literal cuts q'+str(q),m.source_valid(f,o))
  for cc in data['rational_c']:
   c=F(*cc);mass=sum((c**-len(o['sourceCuts'])for o in row['outputs']),F());bound=c**-3 if row['choice']['kind']=='edge'else c**-3+c**-4
   add(name+' literal mass bound '+str(c)+' q'+str(q),mass<=bound)
  for fc in row['known_F_controls']:
   orig,fp=fc['F'],fc['Fprime'];eligible=len(orig)-1<=q
   add(name+' known F valid q'+str(q),fc['F_agreement'] and m.x.agreement(s,t,s.labels,orig))
   add(name+' compiled replacement valid q'+str(q),fc['Fprime_agreement'] and m.x.agreement(s,t,s.labels,fp) and fc['no_larger'] and len(fp)<=len(orig) and fc['Fprime_refines_P'] and m.refines(fp,f['P']))
   orig_ref=any(m.refines(orig,o['partition'])for o in row['outputs']);fp_ref=any(m.refines(fp,o['partition'])for o in row['outputs'])
   add(name+' original refinement crosscheck q'+str(q),fc['original_F_refines_some_Q'],orig_ref);add(name+' replacement refinement crosscheck q'+str(q),fc['Fprime_refines_some_Q'],fp_ref)
   if eligible:coverage+=1;add(name+' eligible F replacement covered q'+str(q),fp_ref)
  if row['choice']['kind']=='edge':
   D=set(row['choice']['descendants']);add('edge descendants actual subtree q'+str(q),row['choice']['descendants'],row['choice']['subtreeLeaves'])
   for o in row['outputs']:
    add('edge actual kept whole A q'+str(q),sum(set(b)==set(f['P'][0])for b in o['partition'])==1)
    add('edge actual B clear q'+str(q),all(not(t.hull(b)&t.hull(f['P'][0]))and(set(b)<=D or set(b).isdisjoint(D))for b in o['partition']if set(b)<=set(f['P'][1])))
   if q==f['q']:
    given=next(z for z in row['known_F_controls']if m.x.canon(z['F'])==m.x.canon(f['F']))
    add('original F stronger assertion rejected',given['original_F_refines_some_Q'],False)
    add('actual compiled exchange matches frozen Fprime',m.x.canon(given['Fprime']),m.x.canon(f['Fprime']))
  if 'vertex'in f:
   add('root has no upward A region q'+str(q),len(row['root_A_regions']),1);add('root has no upward B region q'+str(q),len(row['root_B_regions']),1)
   if q==f['q']and name=='vertex-good-A-bad-C-not-all-Q-agreement':add('actual bad-C outputs reject target agreement',any(row['Q_agreement']),False)
 elif name in negative:
  f=negative[name];g=m.premises(f);expected={k:g[k]for k in row['guards']};add(name+' precise compiled guard failure',row['guards'],expected)
  add(name+' only frozen guard removed',[k for k,v in row['guards'].items()if not v],[f['expected_false_guard']])
 else:
  add(name+' proper selector boundary',row['choice']['kind'],'none');add(name+' no boundary outputs',row['outputs'],[])
# Mutants of ACTUAL compiled data demonstrate the comparison can fail.
v=next(r for r in rows if r.get('id')=='root-supplied-six-leaf-vertex'and r['q']==5)
bad=copy.deepcopy(v['calls']);bad.pop(0);add('omitted actual call detected',[z['identity']for z in bad]!=[z['identity']for z in v['calls']])
bad=copy.deepcopy(v['outputs'][0]);bad['sourceCuts'].pop();add('wrong actual literal cost detected',m.source_valid(lookup[v['id']],bad),False)
actualdup=v['outputs']+[copy.deepcopy(v['outputs'][1])];dedup=list({json.dumps(z,sort_keys=True):z for z in actualdup}.values())
add('actual raw duplicate preserved',len(actualdup)!=len(dedup));add('actual duplicated mass',str(sum((F(2)**-len(o['sourceCuts'])for o in actualdup),F())),'5/16')
add('actual forged original refinement rejected',any(m.refines(lookup['public-good-A-edge-reused']['F'],o['partition'])for o in next(r for r in rows if r.get('id')=='public-good-A-edge-reused'and r['q']==6)['outputs']),False)
out={'checks':checks,'check_denominator':len(checks),'passed':sum(z['pass']for z in checks),'actual_call_receipts':call_den,'actual_raw_occurrences_across_budgets':output_den,'eligible_F_budget_pairs':coverage,'color_adapters':maps,'all_pass':all(z['pass']for z in checks),'source_runtime_cost_claim':False,'replication_increment':0}
(P/'compiled-control-comparison-v1.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k not in['checks','color_adapters']},indent=2));raise SystemExit(0 if out['all_pass']else 1)
