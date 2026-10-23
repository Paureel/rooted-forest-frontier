#!/usr/bin/env python3
"""Freeze author source consumer and every failure; independent review pending."""
from pathlib import Path
import datetime,hashlib,json
D=Path(__file__).resolve().parent;R=D.parents[4];M=D/'FINAL-MANIFEST-v1.json'
if M.exists():raise SystemExit('FROZEN_NO_WRITE_BOUNDARY')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
latest=json.loads((D/'LATEST-REPLAY-v1.json').read_text());O=R/latest['receipt'];assert sha(O/'certificate.json')==latest['sha256'];c=json.loads((O/'certificate.json').read_text());assert c['status']=='PASS_AUTHOR_ACTUAL_ONE_SOURCE_CONSUMER_OPEN'
for e in c['source_entries']:assert sha(R/e['source'])==e['source_sha256'];assert sha(O/(e['module']+'.lean'))==e['sha256']
for p,h in c['input_hashes'].items():assert sha(R/p)==h
old=R/'research/rmaf/algorithm/universal233/rule5_source_orientation_consumer/FINAL-MANIFEST-v1.json';assert sha(old)=='a27469192042dff5e1001961ed64bac312b3c0f527ba02056263bda19a3b5fd8'
for e in json.loads(old.read_text())['immutable_files']:assert sha(R/e['path'])==e['sha256'];assert not (R/e['path']).stat().st_mode&0o222
primitive=R/'research/rmaf/algorithm/universal233/rule5_common_split_source/COMMON-SPLIT-SOURCE-MANIFEST-v1.json';assert sha(primitive)=='ef0d3389b3f66d46ae6c40323bed34504a1e46a882ff9a945cac5ef4c25d5523'
for e in json.loads(primitive.read_text())['immutable_files']:assert sha(R/e['path'])==e['sha256']
(D/'AUTHOR-READY-v1.json').write_text(json.dumps({'status':'AUTHOR_READY_FRESH_REVIEW_PENDING','canonical_receipt':latest,'interfaces':c['interfaces'],'main_milestones':'ALL_OPEN','independent_credit':0},indent=2)+'\n')
files={p for p in D.rglob('*') if p.is_file() and p!=M and '__pycache__' not in p.parts and ('build' not in p.relative_to(D).parts or p.suffix=='.source' or p.name.endswith('.log.gz'))}
for dr in (R/'results').glob('algorithm-universal233-rule5-common-selector-*'):files|={p for p in dr.rglob('*') if p.is_file()}
rows=[{'path':str(p.relative_to(R)),'sha256':sha(p),'bytes':p.stat().st_size} for p in sorted(files)]
rec={'version':1,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'FROZEN_AUTHOR_ACTUAL_ONE_SOURCE_CONSUMER_REVIEW_PENDING','no_further_writes':True,'no_write_boundary':'This manifest and all immutable_files. Continuations/reviews require new paths.','canonical_receipt':latest,'source_builds':c['source_builds'],'stored_producer_occurrences':c['stored_producer_occurrences'],'resolved_unique_names':c['resolved_unique_names'],'axiom_union':c['axiom_union'],'main_milestones':'ALL_OPEN','independent_credit':0,'full_algorithm':False,'runtime_claim':False,'novelty':False,'interfaces':c['interfaces'],'scope':['actual selectFinal remaining.one source primitive consumption','all20 printed graph guards derived','ordered incident API equality','actual SourceIH on sourceJobs','nonrefusal and BoundedExact','proper source jobs and strict current-budget decrease exactly1'],'audit_scope':c['audit_scope'],'first_unprovided_main_call':c['first_unprovided_main_call'],'prior_orientation_and_primitive_preserved':True,'excluded_mutable':['build lean/olean copies; exact attempt sources and compressed logs retained','Python __pycache__'],'immutable_files':rows}
M.write_text(json.dumps(rec,indent=2)+'\n')
for p in files:p.chmod(0o444)
M.chmod(0o444);print(rec['status'],len(rows),'files',sha(M))
