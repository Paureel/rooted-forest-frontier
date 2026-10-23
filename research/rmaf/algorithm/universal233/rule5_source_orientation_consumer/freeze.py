#!/usr/bin/env python3
"""One-shot immutable author release; no independent/full-algorithm acceptance."""
from pathlib import Path
import datetime,hashlib,json
D=Path(__file__).resolve().parent;R=D.parents[4];M=D/'FINAL-MANIFEST-v1.json'
if M.exists():raise SystemExit('FROZEN_NO_WRITE_BOUNDARY')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
latest=json.loads((D/'LATEST-REPLAY-v1.json').read_text());O=R/latest['receipt'];assert sha(O/'certificate.json')==latest['sha256']
c=json.loads((O/'certificate.json').read_text());assert c['status']=='PASS_AUTHOR_SOURCE_ORIENTATION_CONSUMERS_OPEN'
for e in c['source_entries']:assert sha(R/e['source'])==e['sha256']
for p,h in c['input_hashes'].items():assert sha(R/p)==h
rel=json.loads((D/'STRUCTURAL-INPUT-RELEASE-v1.json').read_text());assert sha(R/rel['manifest'])==rel['sha256']
for e in json.loads((R/rel['manifest']).read_text())['immutable_files']:
 assert sha(R/e['snapshot'])==e['sha256']
 assert sha(R/e['original'])==e['sha256'],('ORIGINAL_INPUT_CHANGED',e['original'])
ready={'status':'AUTHOR_READY_FOR_FRESH_REVIEW','independent_credit':0,'main_milestones':'ALL_OPEN','canonical_receipt':latest,'interfaces':c['interfaces'],'scope':c['completed_author_scope'],'first_unprovided_full_rule_call':c['first_unprovided_full_rule_call']}
(D/'AUTHOR-READY-v1.json').write_text(json.dumps(ready,indent=2)+'\n')
files={p for p in D.rglob('*') if p.is_file() and p!=M and '__pycache__' not in p.parts and ('build' not in p.relative_to(D).parts or p.suffix=='.log')}
for dr in (R/'results').glob('algorithm-universal233-rule5-source-orientation-*'):files|={p for p in dr.rglob('*') if p.is_file()}
rows=[{'path':str(p.relative_to(R)),'sha256':sha(p),'bytes':p.stat().st_size} for p in sorted(files)]
rec={'version':1,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'FROZEN_AUTHOR_SOURCE_ORIENTATION_CONSUMERS_REVIEW_PENDING','no_further_writes':True,'no_write_boundary':'This manifest and immutable_files. Continuation/reviews require new paths.','canonical_receipt':latest,'source_builds':c['source_builds'],'stored_producer_occurrences':c['stored_producer_occurrences'],'axiom_union':c['axiom_union'],'main_milestones':'ALL_OPEN','independent_credit':0,'full_algorithm':False,'smaller_base':False,'novelty':False,'interfaces':c['interfaces'],'scope':c['completed_author_scope'],'first_unprovided_full_rule_call':c['first_unprovided_full_rule_call'],'structural_originals_preserved':True,'independence':'All author proof/control/reused source/audit contacts DEVELOPMENT. Fresh nonauthor semantic/interface/prose review required.','excluded_mutable':['build source/olean copies; all build logs retained','Python __pycache__'],'immutable_files':rows}
M.write_text(json.dumps(rec,indent=2)+'\n')
for p in files:p.chmod(0o444)
M.chmod(0o444)
print(rec['status'],len(rows),'files',sha(M))
