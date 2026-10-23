#!/usr/bin/env python3
"""Retain each postcontact actual-input corruption and its specific catch."""
import copy,importlib.util,json,pathlib,shutil,time
P=pathlib.Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('own_index',P/'index_receipt.py');I=importlib.util.module_from_spec(spec);spec.loader.exec_module(I)
DEST=P/'actual-attribution-controls';DEST.mkdir(exist_ok=True)
REG=json.loads((P/'ACTUAL-AUDIT-REGISTRY-pilot-v2.json').read_text());SOURCE=P/'producer-rows/RMAF.jsonl'
CASES=['source_byte_alteration','olean_byte_alteration','wrong_scientific_olean_path','changed_import_flag','missing_occurrence','duplicate_occurrence','wrong_origin','custom_axiom_raw','changed_type','changed_body']
def one(case):
 reg=copy.deepcopy(REG);out=DEST/(case+'.jsonl');target=None
 if case in ['source_byte_alteration','olean_byte_alteration','wrong_scientific_olean_path']:
  field='source' if case=='source_byte_alteration' else 'olean';q=DEST/(case+('.lean' if field=='source' else '.olean'))
  shutil.copyfile(reg['scientific_modules']['RMAF'][field],q)
  if case!='wrong_scientific_olean_path':
   with q.open('ab') as f:f.write(b'\nCORRUPT\n')
  reg['scientific_modules']['RMAF'][field]=str(q)
 with SOURCE.open('rb') as f,out.open('wb') as g:
  changed=False
  for line in f:
   r=json.loads(line)
   if not changed and r['record']=='producer_part' and case=='changed_import_flag':
    r['import_records'][0]['is_meta']=not r['import_records'][0]['is_meta'];changed=True
   elif not changed and r['record']=='occurrence':
    if case in ['missing_occurrence','duplicate_occurrence','wrong_origin']:
     target=[r['producer'],r['part'],r['index']];changed=True
     if case=='missing_occurrence':continue
     if case=='duplicate_occurrence':g.write(line)
     if case=='wrong_origin':r['resolved_origin']='UNREGISTERED_FABRICATED_ORIGIN'
    elif case in ['custom_axiom_raw','changed_type','changed_body'] and r['stored']['kind']=='theorem':
     target=[r['producer'],r['part'],r['index']];s=r['stored'];changed=True
     if case=='custom_axiom_raw':s['kind']='axiom'
     if case=='changed_type':s['type_root']=s['body_root']
     if case=='changed_body':s['body_root']=s['type_root']
   g.write((json.dumps(r,separators=(',',':'),ensure_ascii=False)+'\n').encode())
 regpath=DEST/(case+'-registry.json');regpath.write_text(json.dumps(reg,sort_keys=True)+'\n')
 start=time.perf_counter();error=None;res=None
 try:res=I.index(out,regpath,DEST/(case+'.sqlite'))
 except Exception as e:error=type(e).__name__+': '+str(e)
 messages=[] if res is None else [v[3] for v in res['issues']]
 want={'source_byte_alteration':'source bytes differ','olean_byte_alteration':'olean bytes differ','wrong_scientific_olean_path':'logical module/olean mapping mismatch','changed_import_flag':'exact import flags/order differ','missing_occurrence':'missing/duplicate occurrence denominator','duplicate_occurrence':'UNIQUE constraint','wrong_origin':'resolved_origin_missing','custom_axiom_raw':'direct_custom_axiom','changed_type':'stored_resolved_body_kind_type_mismatch','changed_body':'stored_resolved_body_kind_type_mismatch'}[case]
 caught=want in (error or '') or any(want in m for m in messages)
 result={'case':case,'expected_specific_catch':want,'caught':caught,'target':target,'error':error,'gate_result':res,'seconds':time.perf_counter()-start}
 (DEST/(case+'-result.json')).write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
 if not caught:raise RuntimeError('missed corruption '+case)
 return result
start=time.perf_counter();results=[one(c) for c in CASES]
(P/'ACTUAL-ATTRIBUTION-CONTROL-RESULT-v1.json').write_text(json.dumps({'status':'ALL10_SPECIFIC_CORRUPTIONS_CAUGHT','results':results,'seconds':time.perf_counter()-start,'raw_baseline_partial_rejections_preserved':True},indent=2)+'\n')
print('all10 specific corruption catches passed')
