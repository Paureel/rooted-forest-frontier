"""One-shot comparison to immutable46/221 expectations; source events stay
the independent ledger,never reclassified as extracted candidate instructions.
"""
from pathlib import Path
from collections import Counter
import json,copy
import control_engine as eng
b=Path(__file__).resolve().parent;pin=json.loads((b/'CONTROL-PIN.json').read_text());values={};spies={}
for line in (b/'ACTUAL.stdout.log').read_text().splitlines():
 if line.startswith('ACTUAL_VALUE '):r=json.loads(line.split(' ',1)[1]);assert r['id'] not in values;values[r['id']]=r
for line in (b/'ACTUAL.stderr.log').read_text().splitlines():
 if line.startswith('COLOR_DIAGNOSTIC '):r=json.loads(line.split(' ',1)[1]);tag=r.pop('tag');spies.setdefault(tag,[]).append(r)
assert len(values)==44,len(values);rows=[];plants=[]
for c in pin['controls']:
 ident=c['id'];d=c['input'];expected=eng.evaluate(c);r=copy.deepcopy(expected);v=r['value'];a=values.get(ident);op=c['op'];measured={}
 if op=='recover':
  guards={'distinct':a['distinct'],'partition':a['partitionCheck'],'embeddings':a['embeddings']};assert guards==v['guards'] and a['inputCheck']==all(guards.values()),ident
  assert a['recover']==a['meterRecover'],ident
  g=eng.old.Graph(d['tree']);assert a['nodes']==len(g.at)==v['source_vertex_count']
  for block,addresses in zip(d['partition'],a['minimalVertices']):assert Counter(addresses)==Counter(g.address[i] for i in g.hull(block)),(ident,block,addresses)
  assert len(a['minimalVertices'])==len(d['partition'])
  assert (a['recover'] is not None)==v['success'],ident
  assert a['rawOutputs']==a['tracedDiagnosticOutputs']==v['outputs'],ident
  assert a['recover']==(a['rawOutputs'][0] if a['rawOutputs'] else None),ident
  if v['success']:
   assert a['rankDiagnostic']==len(d['partition'])
   colors={str(x['label']):x['color'] for x in a['colors']};assert colors==v['colors']
   assert all(x['color']==x['meterColor'] for x in a['colors'])
   assert spies[ident]==[{'label':x,'color':colors[str(x)]} for x in g.labels]
   assert len(a['colors'])==a['coreColorCalls']==len(spies[ident])==len(g.labels)
   assert sum(x['meterWork'] for x in a['colors'])<=a['colorCharge']
   p=d['partition'];assert a['guardCharge']==4096*(len(g.at)+sum(map(len,p))+len(p)+2)**8
   assert a['colorCharge']==32*len(g.labels)*(sum(map(len,p))+len(p)+1)
   assert a['meterWork']<=a['finalPolynomial']*2**(len(p)-1)
   cert=eng.certificate(d['tree'],p,a['recover']['cuts']);assert cert['exact']
   assert cert==v['certificate'];assert len(a['recover']['cuts'])==len(p)-1
   # RealizedOutput's literal component-order requirement, in addition to P permutations.
   byroot={z['root']:z['labels'] for z in cert['components']};roots=a['recover']['cuts']+['']
   assert len(roots)==len(set(roots))==len(cert['components'])
   assert [byroot[x] for x in roots]==[sorted(x) for x in a['recover']['partition']],ident
   assert a['visited']==r['counts']['core.step.calls'] and a['attempts']==r['counts'].get('core.attempt.calls',0)
   assert a['pruned']==r['counts'].get('core.prune.callback',0) and a['refusals']==[]
   assert a['returnedTargetAgreement']==a['targetAgreement'],ident
   v['outputs']=copy.deepcopy(a['rawOutputs']);v['certificate']=copy.deepcopy(cert);v['colors']=colors;v['color_count']=len(set(colors.values()))
  else:
   assert a['colors']==[] and a['rankDiagnostic'] is None and ident not in spies
   assert a['meterWork']==a['guardCharge']>0
  v['guards']=guards;v['success']=a['recover'] is not None;v['raw_count']=len(a['rawOutputs']);v['output_costs']=[len(x['cuts']) for x in a['rawOutputs']]
  if 'target' in d:
   assert a['targetAgreement']==v['target_agreement']==False
   v['target_agreement']=a['targetAgreement'];v['target_transport_licensed']=bool(v['success'] and a['targetAgreement'])
  measured={'actual_recover':a['recover'],'actual_guards':guards,'derived_rank_diagnostic':a['rankDiagnostic'],'separate_traced_generate_colors':len(spies.get(ident,[])),'formal_meter_work':a['meterWork'],'all_original_graph_checked':v['success'],'output_components_order_checked':v['success']}
 elif op=='certificate':
  g=eng.old.Graph(d['tree']);assert a['nodes']==len(g.at) and len(a['validOriginalVertices'])==len(g.at) and all(a['validOriginalVertices'])
  edge=[bool(x and x in g.at) for x in d['cuts']];assert a['cutEdges']==a['reverseEdges']==edge
  measured={'compiled_original_addresses':len(g.at),'both_orientations':a['cutEdges'],'exact_certificate':v['exact'],'leafless_components':v['leafless_count']}
 elif op=='edges':assert a['actual']==v['actual'];v['actual']=a['actual'];measured={'compiled_original_edge_checks':a['actual']}
 elif op=='absorption':
  for k in ['factor','charged','absorbed']:assert a[k]==v[k];v[k]=a[k]
  measured={'compiled_Rat_power_comparison':a,'scope':'fixed arithmetic toy; no claim of repeated actual recovery execution'}
 elif op=='permutation':measured={'actual_candidate_execution':False,'scope':'exact graph/list relation; candidate only proves BlockPermutation,does not execute a comparison scan'}
 assert eng.validate(r,c),ident
 for p in c['plants']:
  bad=eng.corrupt(r,p);assert not eng.validate(bad,c),(ident,p)
  plants.append({'case':ident,'plant':p,'caught':True,'value_preserved':bad['value']==r['value']})
 rows.append({'id':ident,'status':'CONFIRMED-SCOPED','observed':measured})
assert len(rows)==46 and len(plants)==221
out={'status':'PASS-SCOPED-ACTUAL-RECOVERY-READOUTS','actual_recovery_cases':22,'valid_recovery_cases':12,'refused_cases':10,'original_address_cases':16,'edge_trap_cases':1,'literal_absorption_cases':5,'reference_permutation_cases':2,'clean_controls':46,'corrupt_twins_caught':221,'rows':rows,'plants':plants,'scope':'Actual recover/meter/guards/blockColor/rank/generate/head/counters/list readouts replace matching reference fields. Reference work events remain source-contract instrumentation. Traced colors are a separately evaluated core generate diagnostic,not an effect trace of hardcoded recover. Full original graphs are independent reviewer computations from actual cuts. No runtime BlockPermutation checker or component graph object is added to recover.','all_three_main_milestones':'OPEN','extra_replications':0}
(b/'ACTUAL-COMPARISON.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k not in ['rows','plants']}))
