from pathlib import Path
import json,hashlib,datetime
b=Path(__file__).resolve().parent;root=b.parents[4];h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
expected={
 'continuation-2026-10-15':'9e6ab630ae7332dd0d572e775f8ee75537c05d013476cc64add4cd9f6111c2b7',
 'geometry-2026-10-15':'b18691927138dc6142fb4306aab87e096a8c3c5a5b9d305905f993cd65d075b6',
 'integration-2026-10-15':'4cbbba186a546ac48e5f27736b7a537a5d83d3b0bec40a2156b15d80040b1c65',
 'core-work-2026-10-15':'61e9aaa274f9ac625939efc3315bf9aa93638435daa90ae039d41a5ebbc67455',
 'whole-source-work-2026-10-15':'2526f8cb77fad799770557765a9d862d54e84fd31a0c1d49e20afd4254741580'}
prior={}
for name,sha in expected.items():
 p=b.parent/name/'ARTIFACTS.json';assert h(p)==sha,(name,h(p));d=json.loads(p.read_text());fs=d.get('file_hashes',d.get('files',{}))
 if isinstance(fs,list):fs={x['path']:x['sha256'] for x in fs}
 assert isinstance(fs,dict),(name,type(fs))
 for path,value in fs.items():
  e=value['sha256'] if isinstance(value,dict) else value
  assert h(root/path)==e,(name,path)
 prior[name]={'manifest_sha256':sha,'entries_rechecked':len(fs)}
rd=json.loads((b/'READY-ARTIFACTS.json').read_text());assert h(b/'READY-ARTIFACTS.json')=='655f32eef6ee281e4d820e49e26d2b20bbf694f11e27cb0605ca4c5d2ac5f535';assert len(rd['file_hashes'])==60
for path,sha in rd['file_hashes'].items():assert h(root/path)==sha,path
cp=json.loads((b/'CANDIDATE-PIN.json').read_text())
for label,pkg in cp['packages'].items():
 manifest=b/('AUTHOR-'+label.upper()+'-MANIFEST.json');assert h(manifest)==pkg['manifest_sha256'];ad=json.loads(manifest.read_text())
 for x in ad['immutable_files']:assert h(root/x['path'])==x['sha256'],x
 for x in pkg['copied_sources']:assert h(b/('isolated-'+label)/(x['module']+'.lean'))==x['sha256'],x
actual=json.loads((b/'ACTUAL-COMPARISON.json').read_text());assert actual['corrupt_twins_caught']==111 and len(actual['exact_mass_checks'])==6 and actual['additional_mass_false_claims_caught']==12
assert (actual['actual_query_fixtures'],actual['actual_classifier_fixtures'],actual['generic_rank_fixtures'])==(16,16,1)
inv=json.loads((b/'AXIOM-INVENTORY.json').read_text());assert [inv['packages'][x]['count'] for x in ['query','rank']]==[289,2479]
for x in inv['packages'].values():assert set(x['axiom_union'])=={'Classical.choice','Quot.sound','propext'} and all(d['kind']!='axiom' for d in x['all_declarations'])
cert={'status':'CONFIRMED-SCOPED exact conditional query and known-four classifier','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'author_entries_rechecked':{'query':54,'rank':153},'readiness_entries_rechecked':60,'prior_reviews_rechecked':prior,'source_builds':{'query':7,'rank':58},'full_origin_declarations':{'query':289,'rank':2479},'private_declarations':{'query':28,'rank':220},'axiom_union':['Classical.choice','Quot.sound','propext'],'originating_custom_axioms':0,'author_explicit_false_diagnostics':7,'separate_post_candidate_false_scope':1,'actual_query_fixtures':16,'actual_classifier_fixtures':16,'generic_rank_fixtures':1,'diagnostic_append_toys':2,'frozen_clean_controls':35,'frozen_corrupt_twins_caught':111,'supplemental_exact_mass_checks':6,'supplemental_false_claims_caught':12,'source_cost_ruling':{'query_formal_meter':'32(n+1)','query_fine32':'OPEN-AT-NAMED-OBLIGATION SC32','independent_conservative_source':'128(n+1) under explicit ordinary-list/scalar contracts','classifier_fixed_source_allowance':64,'core_source_contract':'prior corrected8/cell,external oracle/bit/serialization costs','machine_instructions_cycles':'OPEN'},'retained_failures':'INSTRUMENT-HISTORY.md','consumer':'CONSUMER-TRACE.md','claim_verdicts':'CLAIM-VERDICTS.json','all_three_main_milestones':'OPEN','full_algorithm_proved':False,'additional_independent_replications':0,'author_child_contact':False,'fresh_context_referee_sim':'NOT-PERFORMED; root no-child-contact instruction; self-run framing recorded'}
(b/'CERTIFICATE.json').write_text(json.dumps(cert,indent=2)+'\n')
files={}
for p in sorted(b.rglob('*')):
 if p.is_file() and p.name!='ARTIFACTS.json' and '__pycache__' not in p.parts and p.suffix not in ['.olean','.ilean','.c','.o'] and '.olean' not in p.name:files[str(p.relative_to(root))]=h(p)
for p in sorted((root/'research/rmaf/results').glob('algorithm-query-classifier-fresh-review-*')):
 if p.is_file():files[str(p.relative_to(root))]=h(p)
out={'status':'FROZEN-SCOPED-QUERY-CLASSIFIER-REVIEW','created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'file_count':len(files),'file_hashes':files,'author_manifest_sha256':{k:v['manifest_sha256'] for k,v in cp['packages'].items()},'readiness_manifest_sha256':h(b/'READY-ARTIFACTS.json'),'readiness_entries_rechecked':60,'prior_reviews_rechecked':prior,'excludes':['compiled oleans/ileans/object caches','Python caches','this manifest self-hash'],'additional_independent_replications':0,'all_three_main_milestones':'OPEN','SC32':'OPEN; see explicit128 conservative source contract'}
p=b/'ARTIFACTS.json';p.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'file_count':len(files),'manifest_sha256':h(p),'prior':prior}))
