#!/usr/bin/env python3
"""Freeze thin author extension and failures, preserving both frozen inputs."""
from pathlib import Path
import datetime,hashlib,json
D=Path(__file__).resolve().parent;R=D.parents[4];M=D/'FINAL-MANIFEST-v1.json'
if M.exists():raise SystemExit('FROZEN_NO_WRITE_BOUNDARY')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
L=json.loads((D/'LATEST-REPLAY-v1.json').read_text());O=R/L['receipt'];assert sha(O/'certificate.json')==L['sha256'];c=json.loads((O/'certificate.json').read_text());assert c['status']=='PASS_AUTHOR_BUDGET_LOCAL_SELECTED_COMMON_OPEN'
inputs=json.loads((D/'INPUTS-v1.json').read_text())
for field in ['selector_manifest','local_ih_manifest']:
 p=R/inputs[field]['path'];assert sha(p)==inputs[field]['sha256']
 for e in json.loads(p.read_text())['immutable_files']:assert sha(R/e['path'])==e['sha256']
for e in c['dependency_modules']:assert sha(R/e['source'])==e['source_sha256'];assert sha(R/e['olean'])==e['olean_sha256']
for e in c['new_modules']:assert sha(R/e['source'])==e['sha256']
for p,h in c['input_hashes'].items():assert sha(R/p)==h
(D/'AUTHOR-READY-v1.json').write_text(json.dumps({'status':'AUTHOR_BUDGET_LOCAL_ONE_READY_REVIEW_PENDING','canonical_receipt':L,'new_source_builds':c['new_source_builds'],'pinned_dependency_modules':c['pinned_dependency_modules'],'independent_credit':0,'main_milestones':'ALL_OPEN'},indent=2)+'\n')
files={p for p in D.rglob('*') if p.is_file() and p!=M and '__pycache__' not in p.parts and ('build' not in p.relative_to(D).parts or p.suffix=='.source' or p.name.endswith('.log.gz'))}
for dr in (R/'results').glob('algorithm-universal233-rule5-common-ordinary-*'):files|={p for p in dr.rglob('*') if p.is_file()}
rows=[{'path':str(p.relative_to(R)),'sha256':sha(p),'bytes':p.stat().st_size} for p in sorted(files)]
rec={'version':1,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'FROZEN_AUTHOR_BUDGET_LOCAL_SELECTED_COMMON_REVIEW_PENDING','no_further_writes':True,'no_write_boundary':'This manifest and immutable_files. Continuations/reviews require new paths.','canonical_receipt':L,'new_source_builds':c['new_source_builds'],'pinned_dependency_modules':c['pinned_dependency_modules'],'stored_new_producer_occurrences':c['stored_new_producer_occurrences'],'axiom_union':c['axiom_union'],'main_milestones':'ALL_OPEN','independent_credit':0,'full_algorithm':False,'runtime_claim':False,'novelty':False,'global_ordinary_ih_premise':False,'runtime_ghost_used':False,'interfaces':c['interfaces'],'executable_direct_references':c['executable_direct_references'],'audit_scope':c['audit_scope'],'scope':'Actual flattened selected.one source program at current q; proper smaller-budget callback SourceIH derived only from forall r<q,LocalOrdinaryIH r actual; bounded soundness/global component minimum/completeness/none iff.','first_unprovided_main_call':c['first_unprovided_main_call'],'both_prior_frozen_releases_preserved':True,'excluded_mutable':['development build cached sources/oleans; exact attempt sources and compressed logs retained','Python __pycache__'],'immutable_files':rows}
M.write_text(json.dumps(rec,indent=2)+'\n')
for p in files:p.chmod(0o444)
M.chmod(0o444);print(rec['status'],len(rows),'files',sha(M))
