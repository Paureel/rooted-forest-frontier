#!/usr/bin/env python3
"""Seal the new author extension without chmod/writes to linked inputs."""
from pathlib import Path
import datetime,hashlib,json
D=Path(__file__).resolve().parent;R=next(p for p in D.parents if (p/'bootloops-lean').exists());M=D/'FINAL-MANIFEST-v1.json'
if M.exists():raise SystemExit('FROZEN_NO_WRITE_BOUNDARY')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
L=json.loads((D/'LATEST-REPLAY-v1.json').read_text());O=R/L['receipt'];C=R/L['certificate'];assert sha(C)==L['sha256'];c=json.loads(C.read_text());assert c['status']=='PASS_AUTHOR_PRIORITY_BRIDGE_EXACT_ADMISSION_GAP_OPEN'
spec=json.loads((D/'ROOT-v1.json').read_text());assert sha(D/'ROOT-v1.json')==c['root_pin_sha256']
assert sha(R/spec['frozen_manifest']['path'])==spec['frozen_manifest']['sha256']
linked=set()
for e in spec['dependencies']:
 for f in e['files']:
  for key in ['original','linked']:
   p=R/f[key];assert sha(p)==f['sha256'];s=p.stat();assert s.st_ino==f['inode'] and s.st_dev==f['device'] and s.st_nlink>1 and not s.st_mode&0o222
  linked.add(R/f['linked'])
for e in c['new_modules']:
 assert sha(R/e['source'])==e['source_sha256'];assert sha(R/e['compiled_source'])==e['source_sha256'];assert sha(R/e['olean'])==e['olean_sha256']
for p,h in c['input_hashes'].items():assert sha(R/p)==h
for e in c['producer_files']:assert sha(R/e['path'])==e['sha256']
assert c['stored_new_producer_occurrences']==31 and len(c['axiom_union'])==3
(D/'AUTHOR-READY-v1.json').write_text(json.dumps({'status':'AUTHOR_PRIORITY_BRIDGE_READY_REVIEW_PENDING','canonical_receipt':L,'new_source_modules':4,'pinned_dependency_modules':315,'independent_credit':0,'main_milestones':'ALL_OPEN','first_gap':'Actual first hard2 candidate need not be Rule5-admitted; named concrete source case stored.'},indent=2)+'\n')
files={p for p in D.rglob('*') if p.is_file() and p!=M and '__pycache__' not in p.parts}
files|={p for p in O.rglob('*') if p.is_file() and '__pycache__' not in p.parts}
assert len(linked)==630 and linked<=files
for p in files:
 if p not in linked:assert p.stat().st_nlink==1,'UNDECLARED_HARD_LINK|'+str(p)
rows=[{'path':str(p.relative_to(R)),'sha256':sha(p),'bytes':p.stat().st_size,'frozen_dependency_link':p in linked} for p in sorted(files)]
rec={'version':1,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'FROZEN_AUTHOR_PRIORITY_BRIDGE_EXACT_ADMISSION_GAP_REVIEW_PENDING','no_further_writes':True,'no_write_boundary':'This manifest and immutable_files. Continuations/reviews require new paths. Never rewrite or recompile dependency links.','canonical_receipt':L,'new_source_modules':4,'pinned_dependency_modules':315,'stored_new_producer_occurrences':31,'axiom_union':c['axiom_union'],'main_milestones':'ALL_OPEN','independent_credit':0,'full_algorithm':False,'runtime_claim':False,'novelty':False,'interfaces':c['interfaces']+['Universal233.OrdinaryPriorityBridge.Controls.actual_first_hard2_case','Universal233.OrdinaryPriorityBridge.Controls.actual_first_hard2_admission_gap'],'scope':'Actual hard2 selections to earlier-clear/cherry/two-cuts/Rule4 priority, literal Rule5 scan to actual Rule4 selection/refusal, exact Rule5 admission equivalence with automatic source embedding.','audit_scope':c['audit_scope'],'first_unprovided_main_call':'The first actual hard2 commonT/commonS candidate (3,4) fails literal target embedding and has good-block count 1. Both Rule4 selectors refuse, while (0,1) is admitted. Dispatcher selection requires a further argument/search.','all_failures_and_resource_stop_retained':True,'linked_dependencies_never_mutated_or_compiled':True,'prior_frozen_selector_manifest':spec['frozen_manifest'],'fresh_mathematical_false_rejections':6,'excluded_mutable':['Python __pycache__'],'immutable_files':rows}
M.write_text(json.dumps(rec,indent=2)+'\n')
for p in files:
 if p not in linked:p.chmod(0o444)
M.chmod(0o444)
for e in rows:assert sha(R/e['path'])==e['sha256']
print(rec['status'],len(rows),'files',sha(M),flush=True)
