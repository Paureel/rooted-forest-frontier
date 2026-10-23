"""One-shot immutable scoped review seal; preserve all prior freezes."""
from pathlib import Path
import json,hashlib,datetime
b=Path(__file__).resolve().parent;root=b.parents[4];h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
ready=b/'READY-ARTIFACTS.json';assert h(ready)=='b5ddb36b1b49641d9780c97442c8d1669f8aad2500ae961e6a182b1ef6ba47fe';rd=json.loads(ready.read_text());assert len(rd['file_hashes'])==55
for path,sha in rd['file_hashes'].items():assert h(root/path)==sha,path
manifest=b/'AUTHOR-MANIFEST.json';assert h(manifest)=='95569c46912bff25f74cd01174bc51a934e7395524922271e6de4538fbdc4fb3';a=json.loads(manifest.read_text());assert len(a['immutable_files'])==618
for x in a['immutable_files']:assert h(root/x['path'])==x['sha256'],x
assert len(a['exact_source_import_pins'])==62
for path,sha in a['exact_source_import_pins'].items():assert h(root/path)==sha,path
pin=json.loads((b/'CANDIDATE-PIN.json').read_text())
for x in pin['copied_sources']:assert h(b/'isolated'/(x['module']+'.lean'))==x['sha256'],x
priorpins={
 'actual-query-classifier-2026-10-15':'b7c7fa96d1ea95f91d41218e537b098ce15d5a9cee87375ec212a7f54837cdd8',
 'whole-source-work-2026-10-15':'2526f8cb77fad799770557765a9d862d54e84fd31a0c1d49e20afd4254741580',
 'core-work-2026-10-15':'61e9aaa274f9ac625939efc3315bf9aa93638435daa90ae039d41a5ebbc67455',
 'integration-2026-10-15':'4cbbba186a546ac48e5f27736b7a537a5d83d3b0bec40a2156b15d80040b1c65',
 'geometry-2026-10-15':'b18691927138dc6142fb4306aab87e096a8c3c5a5b9d305905f993cd65d075b6',
 'continuation-2026-10-15':'9e6ab630ae7332dd0d572e775f8ee75537c05d013476cc64add4cd9f6111c2b7'}
old=[]
for name,sha in priorpins.items():
 p=b.parent/name/'ARTIFACTS.json';assert h(p)==sha,(name,h(p));d=json.loads(p.read_text());fs=d.get('file_hashes',d.get('files',{}))
 if isinstance(fs,list):fs={x['path']:x['sha256'] for x in fs}
 for path,value in fs.items():assert h(root/path)==(value['sha256'] if isinstance(value,dict) else value),path
 old.append({'review':name,'entries_rechecked':len(fs),'manifest_sha256':sha})
previousready=b.parent/'actual-query-classifier-2026-10-15/READY-ARTIFACTS.json';assert h(previousready)=='655f32eef6ee281e4d820e49e26d2b20bbf694f11e27cb0605ca4c5d2ac5f535';assert len(json.loads(previousready.read_text())['file_hashes'])==60
r=json.loads((b/'REPLAY.json').read_text());actual=json.loads((b/'ACTUAL-COMPARISON.json').read_text());sc=json.loads((b/'POST-CANDIDATE-SCOPE-RECEIPT.json').read_text());imports=json.loads((b/'IMPORT-CLOSURE-RECEIPT.json').read_text());prov=json.loads((b/'PROVENANCE-MAP.json').read_text())
assert (r['positive_modules'],r['declaration_count'],r['private_count'])==(62,2719,249)
assert r['axiom_union']==['Classical.choice','Quot.sound','propext'] and all(x['kind']!='axiom' for x in r['all_origin_records'])
assert sum(x['explicit_false_diagnostics'] for x in r['false_propositions'])==4
assert actual['clean_controls']==46 and actual['corrupt_twins_caught']==221 and actual['actual_recovery_cases']==22
assert sc['mass_clean']==sc['wrong_cost_claims_rejected']==sc['duplicate_mass_claims_rejected']==12 and sc['separate_postcandidate_explicit_false_controls']==2
assert imports['external_imports']==['Std'] and len(prov['modules'])==62 and len(prov['all_declarations'])==2719
cert={'status':'CONFIRMED-SCOPED exact final original-cut recovery','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'author_manifest_sha256':h(manifest),'author_immutable_entries_rechecked':618,'author_exact_primary_source_pins_rechecked':62,'readiness_entries_rechecked':55,'prior275_ready_entries_rechecked':60,'prior_reviews_rechecked':old,'isolated_scientific_source_builds':62,'copied_scientific_oleans':0,'origin_declarations':2719,'private_origin_names':249,'originating_custom_axioms':0,'axiom_union':r['axiom_union'],'full_import_body_private_generated_adoption_map':'PROVENANCE-MAP.json','direct_external_scientific_imports':['Std'],'actual_recovery_cases':22,'valid_recovery_cases':12,'refused_cases':10,'original_address_certificate_cases':16,'edge_trap_cases':1,'literal_Rat_absorption_cases':5,'reference_list_permutation_cases':2,'frozen_clean_controls':46,'frozen_corrupt_twins_caught':221,'actual_raw_mass_cases':12,'wrong_cost_mass_claims_caught':12,'duplicate_mass_claims_caught':12,'author_explicit_false_diagnostics':4,'separate_postcandidate_false_scope_diagnostics':2,'source_cost_grade':'Kernel value/color/size/envelope algebra PLUS separate conservative source inspection under corrected8/cell,list/scalar/bit contracts. No fine-operation identity,machine/compiler/GC proof or search/runtime closure.','invocation_scope':'One recovery after selected final original AF,with rational c>=2 and k<=q; actual main caller still OPEN. Repeated-call toy checks sum of charges,not tight runtime lower bound.','retained_history':'INSTRUMENT-HISTORY.md','main_open_obligations':['MINIMUM-SELECTION','MAIN-CALL-ONCE','GLOBAL-RECURRENCE'],'fresh_context_prose_referee_review':'PENDING separate root assignment; no self-credit','all_three_main_milestones':'OPEN','full_algorithm_proved':False,'additional_independent_replications':0,'author_child_contact':False,'novelty_claim':False}
(b/'CERTIFICATE.json').write_text(json.dumps(cert,indent=2)+'\n')
files={}
for p in sorted(b.rglob('*')):
 if p.is_file() and p.name!='ARTIFACTS.json' and '__pycache__' not in p.parts and p.suffix not in ['.olean','.ilean','.o','.c'] and '.olean' not in p.name:files[str(p.relative_to(root))]=h(p)
for p in sorted((root/'research/rmaf/results').glob('algorithm-final-cuts-fresh-review-*')):
 if p.is_file():files[str(p.relative_to(root))]=h(p)
out={'status':'FROZEN-SCOPED-FINAL-CUT-RECOVERY-REVIEW','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'file_count':len(files),'file_hashes':files,'author_manifest_sha256':h(manifest),'ready_manifest_sha256':h(ready),'readiness_entries_rechecked':55,'prior_reviews_rechecked':old,'all_three_main_milestones':'OPEN','additional_independent_replications':0,'fresh_context_prose_referee':'PENDING separate root assignment;write new files only','excludes':['derived scientific and Std olean/ilean/object caches','Python caches','this manifest self-hash']}
p=b/'ARTIFACTS.json';p.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'frozen_files':len(files),'manifest_sha256':h(p),'source_modules':62,'origin_declarations':2719,'main_milestones':'OPEN','fresh_context_review':'pending separate root assignment'}))
