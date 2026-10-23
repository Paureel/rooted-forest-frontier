"""Seal the exact scoped nonauthor review, with all failed attempts retained."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,sys
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[6];HERE=Path(__file__).resolve().parent
AUTHOR=ROOT/'research/rmaf/algorithm/universal233/kept_parent/HANDOFF-MANIFEST-v1.json'
AUTHOR_PIN='a2506163a4e1231b02eb785b5a4275167ef657ccd1becb35e956550c19982d70'
READY=HERE.parent/'READY-MANIFEST-v1.json';READY_PIN='3d3eac6f2608c2f0b2b41d969a4d2c0adb316a9b2d3fbced2b0fb7dc0014504b'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def main():
 assert sha(AUTHOR)==AUTHOR_PIN;author=read(AUTHOR);assert len(author['entries'])==228
 for r in author['entries']:assert sha(ROOT/r['path'])==r['sha256'],r['path']
 assert sha(READY)==READY_PIN;ready=read(READY);assert len(ready['files'])==57
 prior=[{'manifest':str(READY.relative_to(ROOT)),'sha256':READY_PIN,'files':57,'all_match':True}]
 for r in ready['files']:assert sha(ROOT/r['path'])==r['sha256'],r['path']
 for p in ready['prior_preservation']:
  m=ROOT/p['manifest'];assert sha(m)==p['sha256'];v=read(m);assert len(v['files'])==p['files']
  for r in v['files']:assert sha(ROOT/r['path'])==r['sha256'],r['path']
  prior.append({**p,'all_match':True})
 base=ROOT/'research/rmaf/results'
 required=['rebuild-v2','readout-v1','frozen-replay-v1','false-controls-v1','audit-v2','toy-gates-v1','replay-full-v1','replay-pilot-v1']
 values={}
 for key in required:
  p=base/f'algorithm-kept-parent-fresh-review-{key}.json';m=read(p);assert m['status'].startswith('PASS'),(key,m['status']);values[key]=m
 audit=values['audit-v2'];assert audit['positive_module_count']==46 and audit['audit']['total']==2071 and audit['literal_theorems_printed']==1217
 assert values['readout-v1']['comparisons']==173 and values['frozen-replay-v1']['actual_generate_calls']==29
 assert values['replay-full-v1']['positive_checks']==203 and values['replay-full-v1']['negative_catches']==30
 assert values['false-controls-v1']['false_propositions']==15
 assert values['toy-gates-v1']['negative_custom_axiom_catches']==3 and values['toy-gates-v1']['explicit_false_prop_catches']==1
 for row in values['rebuild-v2']['sources']:
  assert sha(ROOT/row['original'])==row['sha256'] and sha(ROOT/row['copy'])==row['sha256'],row
 for row in audit['source_scans']:assert sha(HERE/'isolated'/(row['module']+'.lean'))==row['sha256']
 summary={'status':'PASS_SCOPED_KEPT_PARENT_CONSUMER','utc':datetime.now(timezone.utc).isoformat(),'author_manifest_sha256':AUTHOR_PIN,'author_entries':228,'candidate_contact_after_root_release':True,'source_only_no_copied_scientific_oleans':True,'positive_modules':46,'originating_declarations':2071,'literal_theorems_printed':1217,'actual_compiled_readout_comparisons':173,'unchanged_fixed_positive_checks':203,'unchanged_fixed_false_catches':30,'actual_generator_cache_uses':29,'explicit_false_propositions':15,'additional_custom_axiom_catches':3,'additional_toy_false_propositions':1,'standard_axiom_union':audit['audit']['axiom_union'],'new_nonauthor_consumer':'FreshConsumer.original_interface / retained_original_local / every_fixture_output / every_fixture_paid','failures_retained':['readiness nonclade hand trace correction','readiness lazy equation toy correction','unimported exploratory CheckAPI unknown identifier probe','literal private numeric-name parser attempt'],'model_diagnosed_exact_order_cases':['root-nonclade-A','root-nonclade-C'],'original_whole_source_cut_lift':'OPEN','paid_query_discount':'OPEN','all_main_milestones':'OPEN','replication_count_added':0,'author_contacts':0,'child_contacts':0,'prior_frozen_checks':prior}
 final=base/'algorithm-kept-parent-fresh-review-final-v1.json';assert not final.exists();final.write_text(json.dumps(summary,indent=2)+'\n')
 results=sorted(base.glob('algorithm-kept-parent-fresh-review-*.json'))
 files=sorted([p for p in HERE.rglob('*') if p.is_file() and '__pycache__' not in p.parts and not p.name.startswith('REVIEW-MANIFEST-')]+results)
 assert len(files)==len(set(files))
 rows=[{'path':str(p.relative_to(ROOT)),'realpath':str(p.resolve()),'sha256':sha(p),'bytes':p.stat().st_size} for p in files]
 manifest={'version':1,'stage':'FROZEN_NONAUTHOR_SCOPED_KEPT_PARENT_REVIEW','utc':datetime.now(timezone.utc).isoformat(),'immutable':True,'verdict':summary['status'],'author_manifest':str(AUTHOR.relative_to(ROOT)),'author_sha256':AUTHOR_PIN,'all_author_entries_match':True,'author_entries':228,'final_receipt':str(final.relative_to(ROOT)),'final_receipt_sha256':sha(final),'prior_preservation':prior,'all_main_milestones':'OPEN','replication_count_added':0,'same_provenance_lineage':True,'source_bound_positive_modules':audit['positive_modules'],'positive_origin_counts':audit['audit']['counts'],'full_origin_declarations':2071,'literal_theorem_axiom_prints':1217,'failures_retained':True,'model_diagnosed_exact_order_cases':summary['model_diagnosed_exact_order_cases'],'files':rows,'file_count':len(rows),'total_bytes':sum(x['bytes'] for x in rows)}
 out=HERE/'REVIEW-MANIFEST-v1.json';assert not out.exists();out.write_text(json.dumps(manifest,indent=2)+'\n')
 for p in files:p.chmod(0o444)
 out.chmod(0o444)
 print(json.dumps({'manifest':str(out.relative_to(ROOT)),'sha256':sha(out),'files':len(rows),'bytes':manifest['total_bytes'],'status':manifest['verdict']}))
if __name__=='__main__':main()
