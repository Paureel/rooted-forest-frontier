"""One-shot retained-evidence certificate assembly; no candidate code execution.
Reuses own calibrated actual graph reader/comparator and semantic checker.
All comparisons concern old executed evidence and grant no fresh replication.
"""
import collections,copy,hashlib,json,pathlib,sys
HERE=pathlib.Path(__file__).resolve().parent;OLD=HERE.parent/'postrelease-v1'
sys.path.insert(0,str(OLD))
from check_closure import controls,graph
from check_semantics import receipt,one

def pin(p):
 p=pathlib.Path(p);return {'path':str(p),'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
def write(name,data):
 with (HERE/name).open('x') as f:json.dump(data,f,indent=2,sort_keys=True);f.write('\n')
def runtime_pin_matches(r):
 p=pin(r["path"])
 assert set(r)=={"path","bytes","sha256","module"}
 assert p=={k:r[k] for k in p}
def main():
 # A clean extra-module metadata row passes; corrupted pins must refuse.
 p=pin(__file__);r={**p,"module":"Synthetic"};runtime_pin_matches(r)
 for field,bad in [("sha256","0"*64),("bytes",p["bytes"]+1)]:
  b={**r,field:bad}
  try:runtime_pin_matches(b)
  except AssertionError:pass
  else:raise AssertionError("pin corruption escaped")
 # Executed own truth/corruption controls before any candidate evidence below.
 controls()
 a=receipt('closure-full-cold');b=receipt('closure-full-released')
 da,ra=graph(a);db,rb=graph(b);assert da==db and a[0]==b[0] and a[-1]==b[-1]
 roots={}
 for n in a[0]['roots']:
  reached=ra(n);roots[n]={'declarations':len(reached),'axioms':sorted(x for x in reached if da[x]['kind']=='axiom'),'partial':sorted(x for x in reached if da[x]['partial']),'unsafe':sorted(x for x in reached if da[x]['unsafe'])}
 assert len(da)==9998 and len(roots)==7
 assert {n for n,d in da.items() if d['kind']=='axiom'}=={'Classical.choice','Quot.sound','propext'}
 assert not any(d['partial'] or d['unsafe'] for d in da.values())
 assert 'sorryAx' not in da
 runtime=[]
 ready=json.loads((HERE.parent/'READY-v1.json').read_text())
 for r in ready['owned_files']+ready['installed_runtime_trust_pins']:
  p=pathlib.Path(r['path']);pinned=pin(p);assert pinned['sha256']==r['sha256'] and pinned['bytes']==r['bytes']
 for name in ['closure-full-cold-CHECKED-v1.json','closure-full-released-CHECKED-v1.json']:
  ck=json.loads((OLD/name).read_text())
  for r in ck['trusted_runtime_pins']:
   runtime_pin_matches(r)
  runtime.append({'certificate':name,'trusted_modules_checked':len(ck['trusted_runtime_pins'])})
 write('AXIOM-CLOSURE-REVALIDATED-v1.json',{'status':'RETAINED-ACTUAL-CLOSURE-ROWS-MATCH','declarations':len(da),'roots':roots,'actual_stored_values_walked_in_prior_runs':True,'cached_axiom_extension_used':False,'custom_axioms':[],'sorryAx':False,'partial':[],'unsafe':[],'trusted_runtime_checks':runtime,'ready_owned_pins':len(ready['owned_files']),'ready_runtime_pins':len(ready['installed_runtime_trust_pins']),'new_replication_credit':False})
 manifest=json.loads((OLD/'SEMANTIC-CASE-MANIFEST-v1.json').read_text());expected=json.loads((OLD/'SEMANTIC-EXPECTATIONS-v1.json').read_text());counts={}
 for phase in ['cold','released']:
  n=0;hist=collections.Counter()
  for batch in manifest['batches']:
   p=pathlib.Path(batch['path']);assert pin(p)['sha256']==batch['sha256'] and p.stat().st_size==batch['bytes']
   inputs=[json.loads(line) for line in p.read_text().splitlines()];out=receipt('eval-'+phase+'-'+batch['batch']);assert len(inputs)==batch['rows']
   ids=[x['id'] for x in out];assert len(ids)==len(set(ids)) and set(ids)=={x['id'] for x in inputs}
   table={x['id']:x for x in out}
   for inp in inputs:hist[one(inp,expected[inp['id']],table[inp['id']])]+=1;n+=1
  assert n==4873;counts[phase]={'rows':n,'histogram':dict(hist)}
 receipts=[json.loads(p.read_text()) for p in (OLD/'evidence').glob('*.json')]
 plan=json.loads((OLD/'COLD-SOURCE-PLAN-v1.json').read_text());build=[]
 for module in plan['order']:
  rr=[r for r in receipts if r['label']=='cold-'+module];assert len(rr)==1
  r=rr[0];assert r['returncode']==0 and r['stop_reason'] is None
  build.append({'module':module,'seconds':r['seconds'],'command':r['command']})
 write('RETAINED-SOURCE-SEMANTIC-EVIDENCE-v1.json',{'status':'RETAINED-EVIDENCE-RECHECKED','cold_build_receipts':len(build),'semantic':counts,'semantic_total_unique_rows':4873,'cold_source_binaries_copied_from_author':False,'old_forest_cases_per_phase':15,'new_evaluator_runs':0,'new_source_rebuilds':0,'new_replication_credit':False})
 print(json.dumps({'status':'RETAINED-EVIDENCE-RECHECKED','closure_declarations':len(da),'closure_roots':len(roots),'actual_closure_equal':True,'cold_builds':len(build),'finite_rows_per_phase':counts,'runtime_checks':runtime},sort_keys=True))
if __name__=='__main__':main()
