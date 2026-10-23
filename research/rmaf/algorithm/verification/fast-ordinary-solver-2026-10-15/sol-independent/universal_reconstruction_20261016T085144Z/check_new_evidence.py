"""One-phase proof evidence consumer. The calibrated actual walker and expression
parser are reused. Only this new module's body rows are inspected; no old raw
source audit, cold build or finite solver census is repeated.
"""
import copy,gzip,hashlib,json,pathlib,sys
HERE=pathlib.Path(__file__).resolve().parent;OLD=HERE.parent/'postrelease-v1'
sys.path.insert(0,str(OLD))
import check_closure,check_semantics
from row_audit_metadata import expression,source_gate
from scan_rows import read_label
RUNTIME=HERE.parents[6]/'.runtime/elan/toolchains/leanprover--lean4---v4.35.0'
def pin(p):
 p=pathlib.Path(p);return {'path':str(p.resolve()),'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
def write(n,v):
 with (HERE/n).open('x') as f:json.dump(v,f,indent=2,sort_keys=True);f.write('\n')
def own_rows(rr,allowed):
 h=rr[0];ds={};external={};nodes=0
 assert h['record']=='header' and h['import_level']=='private'
 for r in rr[1:]:
  if 'record' in r:
   assert r['record']=='external-trust-boundary' and r['name'] not in external
   external[r['name']]=r
  else:
   assert r['name'] not in ds and r['module'] in h['modules'];ds[r['name']]=r
 assert len(ds)==h['count'] and len(ds)>0
 source_gate(ds)
 refs=set()
 for n,r in ds.items():
  a,k=expression(r['type']);nodes+=k;assert a==set(r['type_refs'])
  assert r['kind'] in ('definition','theorem')
  if r['kind']=='theorem':
   assert r['body'] is None and r['proof_body_omitted_after_actual_walk'] and r['body_nodes']>0
   assert set(r['data_payload'])=={'all'}
  else:
   assert r['body'] is not None and not r['proof_body_omitted_after_actual_walk']
   a,k=expression(r['body']);nodes+=k;assert a==set(r['body_refs']) and k==r['body_nodes']
   assert set(r['data_payload'])=={'safety','hints','all'}
  assert r['extra_refs']==[]
  refs.update(r['type_refs']+r['body_refs'])
 assert refs-set(ds)==set(external)
 for n,r in external.items():
  m=r['module']
  if m in allowed:continue
  p=RUNTIME/'lib/lean'/pathlib.Path(*m.split('.')).with_suffix('.olean')
  assert p.is_file() and p.resolve().is_relative_to(RUNTIME.resolve())
 return ds,{'rows':len(ds),'full_type_nonproof_expression_nodes':nodes,'actual_proofs':sum(r['kind']=='theorem' for r in ds.values()),'complete_nonproof_bodies':sum(r['kind']=='definition' for r in ds.values())}
def main():
 # Full-path old truth/forged-closure controls execute before new module evidence.
 check_closure.controls()
 clean=read_label('fixed-clean');own_rows(clean,{'PClean'})
 catches=[]
 for mutation in ['missing-row','duplicate-row','missing-nonproof-body','forged-reference','partial']:
  bad=copy.deepcopy(clean);i=next(i for i,r in enumerate(bad) if r.get('kind')=='definition')
  if mutation=='missing-row':bad.pop(i)
  elif mutation=='duplicate-row':bad.append(copy.deepcopy(bad[i]))
  elif mutation=='missing-nonproof-body':bad[i]['body']=None
  elif mutation=='forged-reference':bad[i]['body_refs'].append('Forged.missing')
  else:bad[i]['partial']=True
  try:own_rows(bad,{'PClean'})
  except (AssertionError,ValueError,TypeError):catches.append(mutation)
  else:raise AssertionError('new module reader accepted corruption '+mutation)
 # Switch only the in-memory evidence location; original code/files remain frozen.
 check_semantics.HERE=HERE
 rr=check_semantics.receipt('own-proof-body-v1')
 plan=json.loads((OLD/'COLD-SOURCE-PLAN-v1.json').read_text());allowed=set(plan['order'])|{'ReconstructionV2'}
 ds,bodyinfo=own_rows(rr,allowed)
 cr=check_semantics.receipt('own-proof-closure-v1');deps,reach=check_closure.graph(cr)
 forbidden={'OrdinaryDispatch.FastOrdinary.solve_exact','OrdinaryDispatch.FastOrdinary.external_exact','OrdinaryDispatch.FastOrdinary.actual_ordinary_IH','OrdinaryDispatch.FastOrdinary.actual_local_ordinary_IH','Universal233.DepthOne.found_globally_minimum','OrdinaryDispatch.FastOrdinary.found_query_exact','OrdinaryDispatch.FastOrdinary.query_of_checked_complete'}
 assert not (forbidden&set(deps))
 assert 'sorryAx' not in deps and not any(r['partial'] or r['unsafe'] for r in deps.values())
 roots={}
 for root in cr[0]['roots']:
  names=reach(root)
  auth=[n for n in sorted(names) if deps[n]['kind']=='theorem' and deps[n]['module'] in plan['order']]
  roots[root]={'declarations':len(names),'axioms':sorted(n for n in names if deps[n]['kind']=='axiom'),'author_theorem_dependencies':auth,'author_global_targets':sorted(names&forbidden)}
 runtime=[]
 for m in sorted({r['module'] for r in deps.values()}-allowed):
  p=RUNTIME/'lib/lean'/pathlib.Path(*m.split('.')).with_suffix('.olean');assert p.is_file()
  runtime.append({'module':m,**pin(p)})
 compiler=pin(RUNTIME/'bin/lean')
 previous=json.loads((HERE.parent/'resume_20261016T083330Z/FINAL-MANIFEST-v1.json').read_text())
 previouspins={r['path']:r for r in previous['files']}
 tools=[]
 for name in ['instrument-v5/Producer.lean','instrument-v5/Producer.olean','instrument-v5/AxiomClosure.lean','instrument-v6/Producer.lean','instrument-v6/Producer.olean','instrument-v6/StoredInvoke.lean']:
  p=OLD/name;cur=pin(p);assert cur==previouspins[str(p.resolve())];tools.append(cur)
 result={'status':'NEW-QUANTIFIED-PROOF-BODY-AND-ACTUAL-CLOSURE-CHECKED','body':bodyinfo,'roots':roots,'closure_declarations':len(deps),'axioms':cr[-1]['axioms'],'forbidden_targets_checked':sorted(forbidden),'forbidden_reached':[],'custom_axioms':sorted(n for n,r in deps.items() if r['kind']=='axiom' and r['module'] in allowed),'sorryAx':False,'partial':[],'unsafe':[],'controls_caught':catches,'cached_axiom_extension_used':False,'new_source':pin(HERE/'ReconstructionV2.lean'),'new_olean':pin(HERE/'ReconstructionV2.olean'),'compiler':compiler,'trusted_runtime_pins':runtime,'unchanged_calibrated_producer_pins':tools,'independent_full_solver_exactness':False,'rejected_arm_open':True,'new_blind_credit':False}
 write('PROOF-DEPENDENCY-CERTIFICATE-v1.json',result)
 print(json.dumps({'status':result['status'],'body':bodyinfo,'closure_declarations':len(deps),'axioms':result['axioms'],'forbidden_reached':[],'per_root_author_theorem_counts':{n:len(r['author_theorem_dependencies']) for n,r in roots.items()},'first_root_author_theorems':roots[cr[0]['roots'][0]]['author_theorem_dependencies'],'runtime_modules':len(runtime)},sort_keys=True))
if __name__=='__main__':main()
