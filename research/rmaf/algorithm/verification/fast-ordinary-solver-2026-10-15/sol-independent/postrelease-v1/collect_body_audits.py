"""Full released/cold scientific declaration audit, no suffix exclusions.

Proof text is already omitted only by the calibrated actual-value walker.
Every retained scientific nonproof/opaque body, type and recursor RHS is parsed.
"""
import hashlib,json,pathlib,sys,time
from scan_rows import read_label
from row_audit_metadata import rows,source_gate
HERE=pathlib.Path(__file__).resolve().parent
def canonical(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def load_phase(phase):
 plan=json.loads((HERE/'COLD-SOURCE-PLAN-v1.json').read_text());order=plan['order']
 groups=[order[:10],order[10:20]]+[order[i:i+20] for i in range(20,len(order),20)]
 decls={};external={};module_seen=[];permodule={}
 for i,group in enumerate(groups):
  label=f'{phase}-v5-b{i:03d}';data=read_label(label);assert data[0]['modules']==group
  module_seen.extend(group)
  for r in data[1:]:
   if r.get('record')=='external-trust-boundary':
    if r['name'] in external:assert external[r['name']]==r,('external ambiguity',r['name'])
    external[r['name']]=r
   elif 'record' not in r:
    assert r['name'] not in decls,('duplicate nonproof/declaration name',r['name'])
    assert r['module'] in group;decls[r['name']]=r;permodule.setdefault(r['module'],[]).append(r)
   else:raise ValueError('unknown producer row')
 assert module_seen==order and set(permodule)==set(order),('module denominator',set(order)-set(permodule))
 allrefs=set()
 for r in decls.values():allrefs.update(r['type_refs']+r['body_refs']+r['extra_refs'])
 for n in set(external)&set(decls):
  assert external[n]['module']==decls[n]['module'] and external[n]['kind']==decls[n]['kind'],('custom boundary ambiguity',n)
 outside=[r for n,r in external.items() if n not in decls and n in allrefs]
 merged=[{'record':'header','modules':order,'count':len(decls),'import_level':'private'}]+list(decls.values())+outside
 return merged,permodule
def main():
 phase=sys.argv[1];start=time.perf_counter();merged,permodule=load_phase(phase)
 try:
  decls,info=rows(merged)
 except Exception as e:
  failure={'phase':phase,'status':'STRUCTURAL-REFUSAL','reason':str(e),'no_waiver':True}
  (HERE/f'BODY-AUDIT-{phase}-REFUSAL-v1.json').write_text(json.dumps(failure,indent=2)+'\n');raise
 flags={key:sorted(n for n,r in decls.items() if (r['kind']=='axiom' if key=='axiom' else r[key]))
        for key in ('axiom','unsafe','partial')}
 sorry=sorted(n for n,r in decls.items() if any(x=='sorryAx' or x.endswith('.sorryAx') for x in r['type_refs']+r['body_refs']+r['extra_refs']))
 gate='admitted';gate_reason=None
 try:source_gate(decls)
 except ValueError as e:gate='REFUSED';gate_reason=str(e)[:1500]
 fps={m:{'declarations':len(rs),'sha256':hashlib.sha256(canonical(sorted(rs,key=lambda r:r['name']))).hexdigest()}
      for m,rs in permodule.items()}
 result={'phase':phase,'status':'FULL-SCIENTIFIC-BODY-STRUCTURE-AUDITED','modules':len(permodule),
  'declarations':len(decls),'structural':info,'raw_flags':flags,'sorry_referrers':sorry,
  'full_raw_source_gate':gate,'gate_reason_excerpt':gate_reason,'all_flagged_rows_retained':True,
  'module_fingerprints':fps,'seconds':time.perf_counter()-start,
  'proof_text_equality_claimed':False,'proof_text_policy':'Actual complete stored proof traversed; refs and expanded counts retained.',
  'no_suffix_exclusions':True,'universal_solver_correctness_from_this_audit_alone':False}
 (HERE/f'BODY-AUDIT-{phase}-v1.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
 print(json.dumps({k:v for k,v in result.items() if k not in ('raw_flags','module_fingerprints','gate_reason_excerpt')},sort_keys=True))
 print(json.dumps({'raw_flag_counts':{k:len(v) for k,v in flags.items()},'first_partial':flags['partial'][:4]},sort_keys=True))
if __name__=='__main__':main()
