#!/usr/bin/env python3
"""Seal the overlap author extension, leaving every dependency link untouched."""
from pathlib import Path
import datetime,hashlib,json
D=Path(__file__).resolve().parent;R=next(p for p in D.parents if (p/'bootloops-lean').exists());M=D/'FINAL-MANIFEST-v1.json'
if M.exists():raise SystemExit('FROZEN_NO_WRITE_BOUNDARY')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
L=json.loads((D/'LATEST-REPLAY-v1.json').read_text());O=R/L['receipt'];C=R/L['certificate'];assert sha(C)==L['sha256'];c=json.loads(C.read_text());assert c['status']=='PASS_AUTHOR_ACTUAL_HARD2_OVERLAP_SELECTOR_OPEN'
spec=json.loads((D/'ROOT-v1.json').read_text());priority=json.loads((D/'PRIORITY-INPUT-v1.json').read_text());dependencies=spec['dependencies']+priority['dependencies']
assert sha(D/'ROOT-v1.json')==c['root_pin_sha256'];assert sha(D/'PRIORITY-INPUT-v1.json')==c['priority_pin_sha256']
for f in [spec['frozen_manifest'],priority['manifest']]:assert sha(R/f['path'])==f['sha256']
linked=set()
for e in dependencies:
 for f in e['files']:
  for key in ['original','linked']:
   p=R/f[key];assert sha(p)==f['sha256'];s=p.stat();assert s.st_ino==f['inode'] and s.st_dev==f['device'] and s.st_nlink>1 and not s.st_mode&0o222
  linked.add(R/f['linked'])
for e in c['new_modules']:
 assert sha(R/e['source'])==e['source_sha256'];assert sha(R/e['compiled_source'])==e['source_sha256'];assert sha(R/e['olean'])==e['olean_sha256']
for p,h in c['input_hashes'].items():assert sha(R/p)==h
for e in c['producer_files']:assert sha(R/e['path'])==e['sha256']
assert c['stored_new_producer_occurrences']==193 and len(c['axiom_union'])==3 and c['fresh_source_control_rejections']==11
(D/'AUTHOR-READY-v1.json').write_text(json.dumps({'status':'AUTHOR_HARD2_OVERLAP_READY_REVIEW_PENDING','canonical_receipt':L,'new_source_modules':9,'pinned_dependency_modules':318,'independent_credit':0,'main_milestones':'ALL_OPEN','scope':'Actual exhaustive original three-hull selector, paid geometric consumers and isolated-pair guards; recursive dispatcher remains open.'},indent=2)+'\n')
files={p for p in D.rglob('*') if p.is_file() and p!=M and '__pycache__' not in p.parts}
files|={p for p in O.rglob('*') if p.is_file() and '__pycache__' not in p.parts}
assert len(linked)==636 and linked<=files
for p in files:
 if p not in linked:assert p.stat().st_nlink==1,'UNDECLARED_HARD_LINK|'+str(p)
rows=[{'path':str(p.relative_to(R)),'sha256':sha(p),'bytes':p.stat().st_size,'frozen_dependency_link':p in linked} for p in sorted(files)]
rec={'version':1,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'FROZEN_AUTHOR_ACTUAL_HARD2_OVERLAP_REVIEW_PENDING','no_further_writes':True,'no_write_boundary':'This manifest and immutable_files. Continuations/reviews require new paths. Never rewrite or recompile dependency links.','canonical_receipt':L,'new_source_modules':9,'pinned_dependency_modules':318,'stored_new_producer_occurrences':193,'axiom_union':c['axiom_union'],'fresh_source_control_rejections':11,'main_milestones':'ALL_OPEN','independent_credit':0,'full_algorithm':False,'runtime_claim':False,'novelty':False,'interfaces':c['interfaces'],'runtime_direct_references':c['runtime_direct_references'],'scope':'Actual first-hard2 source inputs and exhaustive three-hull overlap selection, original geometric guards and literal parent permutations, clique/four/diagonal/vertex-pair paid calls retaining original P/F/outputs/budgets, isolated pair actual choose/clearance guards, disjoint admission iff literal good-count=2.','audit_scope':c['audit_scope'],'first_unprovided_main_call':c['first_unprovided_main_call'],'all_failures_retained':True,'unexpected_fixture_failure_retained':'Wrong shorter vertex address failed; exact source/log and executed LiteralProbe correction retained. Universal selector/proof unchanged.','linked_dependencies_never_mutated_or_compiled':True,'frozen_inputs':[spec['frozen_manifest'],priority['manifest']],'excluded_mutable':['Python __pycache__'],'immutable_files':rows}
M.write_text(json.dumps(rec,indent=2)+'\n')
for p in files:
 if p not in linked:p.chmod(0o444)
M.chmod(0o444)
for e in rows:assert sha(R/e['path'])==e['sha256']
print(rec['status'],len(rows),'files',sha(M),flush=True)
