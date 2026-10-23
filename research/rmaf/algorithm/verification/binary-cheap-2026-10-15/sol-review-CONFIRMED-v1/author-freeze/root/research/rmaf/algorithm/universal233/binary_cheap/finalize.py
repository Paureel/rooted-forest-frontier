"""One-shot author freeze; writes only this package and its new result receipts."""
from pathlib import Path
import datetime,hashlib,json
D=Path(__file__).resolve().parent;R=D.parents[4]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
out=Path((D/'LATEST-REPLAY.txt').read_text().strip());c=json.loads((out/'certificate.json').read_text())
assert c['status']=='PASS_AUTHOR_SOURCE_BOUND_REPLAY'
assert c['positive_source_modules']==102 and c['module_origin_declarations']==3590
assert c['literal_preproof_controls']==16
assert c['false_propositions_rejected']==4
assert c['missing_record_plant_caught'] and c['foreign_private_axiom_plant_caught'] and c['actual_source_pin_checker_corruption_caught_with_clean_twin']
for e in c['source_inputs']:assert sha(R/e['path'])==e['sha256'],e['path']
for v in ['v1','v2','v3']:
 m=json.loads((D/('CONTROLS-PIN-'+v+'.json')).read_text())
 for n,h in m['files'].items():
  p=D/('LiteralControls-'+v+'.lean') if n=='LiteralControls.lean' and v in ['v1','v2'] else D/n
  assert sha(p)==h,(v,n)
files=[]
for base in [D,out]:
 for p in sorted(base.rglob('*')):
  if not p.is_file() or p.suffix in ['.olean','.ilean','.pyc'] or 'build' in p.relative_to(base).parts or '__pycache__' in p.parts:continue
  if p.name in ['BINARY-CHEAP-MANIFEST-v1.json','BINARY-CHEAP-SEAL-v1.json']:continue
  files.append({'path':str(p.relative_to(R)),'sha256':sha(p),'bytes':p.stat().st_size})
manifest={'version':1,'frozen_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'FROZEN_AUTHOR_SCOPED_BINARY_CHEAP; fresh independent review pending','no_further_writes':True,'all_three_main_milestones':'OPEN','complete_algorithm_proved':False,'novelty_claim':False,'fresh_independent_acceptance':False,'canonical_receipt':str((out/'certificate.json').relative_to(R)),'positive_source_modules':c['positive_source_modules'],'module_origin_declarations':c['module_origin_declarations'],'standard_axioms_observed':c['axiom_union_observed'],'preproof_controls':16,'postproof_consumer_controls':c['postproof_consumer_controls'],'false_propositions_rejected':4,'audit_and_pin_plants_caught':3,'runtime_grade':'No new source-operation or compiled-machine cost result; actual values, graph checks, original LOCAL cut certificates and raw-LIST mass only.','scoped_target':'Original selected binary edge + actual sourceP + original topology/Cclear hypotheses + literal q3 acceptance derive exactfullclasses/source+targetvalid, localminimum1/pretestLOCALcut and foralloppositekeptsamecert/crossclear, or explicit2badactualcomponents. Exact sameedge symmetry; actualtwohighlistmass.','first_remaining_algorithm_use':'Actual grouped/ordinary query/reconstruction; original S|A local address to whole original S compatible-cut map/union/nonredundancy/combinedcharge; globalrecurrence/termination/runtime.','historical_failed_controls':'LiteralControls-v1.lean and -v2.lean preserve old pinned bytes; their logs and corrected v3 pin precede universal proof. Postproof supplement explicitly development.','negative_audit_sources':['FalseLiteral.lean','FalseLogic.lean','PlantPrivate.lean','PlantAudit.lean'],'excluded_files':'Only build/ generated development files and olean/ilean/pyc; canonical source copies/logs/certificate included.','entry_count':len(files),'immutable_files':files}
p=D/'BINARY-CHEAP-MANIFEST-v1.json';p.write_text(json.dumps(manifest,indent=2)+'\n')
s={'manifest':str(p.relative_to(R)),'sha256':sha(p),'entry_count':len(files),'no_further_writes':True,'all_three_main_milestones':'OPEN'}
(D/'BINARY-CHEAP-SEAL-v1.json').write_text(json.dumps(s,indent=2)+'\n')
for e in files:assert sha(R/e['path'])==e['sha256']
assert sha(p)==s['sha256']
print(json.dumps(s,indent=2))
