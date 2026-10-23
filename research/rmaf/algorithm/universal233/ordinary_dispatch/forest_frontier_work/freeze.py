#!/usr/bin/env python3
"""Freeze the qualified frontier/source-work extension and all stopped evidence."""
from pathlib import Path
import datetime,hashlib,json
D=Path(__file__).resolve().parent;R=next(p for p in D.parents if (p/'bootloops-lean').exists());M=D/'FINAL-MANIFEST-v1.json'
if M.exists():raise SystemExit('FROZEN_NO_WRITE_BOUNDARY')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
L=json.loads((D/'LATEST-REPLAY-v1.json').read_text());O=R/L['receipt'];C=R/L['certificate'];assert sha(C)==L['sha256'];c=json.loads(C.read_text());assert c['status']=='PASS_AUTHOR_FOREST_FRONTIER_BINDING_OPEN'
spec=json.loads((D/'ROOT-v2.json').read_text());assert sha(D/'ROOT-v2.json')==c['root_pin_sha256'];assert sha(D/'ROOT-v1.json')==spec['root_v1_sha256']
for m in spec['manifests']:assert sha(R/m['path'])==m['sha256']
dependencies=set()
for e in spec['dependencies']:
 for f in e['files']:
  p=R/f['original'];assert sha(p)==f['sha256'] and oct(p.stat().st_mode&0o777)==f['original_mode']
  p=R/f['linked'];st=p.stat();assert sha(p)==f['sha256'] and not st.st_mode&0o222;assert (st.st_ino,st.st_dev)==(f['inode'],f['device']);dependencies.add(p)
for e in c['new_modules']:
 assert sha(R/e['source'])==e['source_sha256'];assert sha(R/e['compiled_source'])==e['source_sha256'];assert sha(R/e['olean'])==e['olean_sha256']
for p,h in c['input_hashes'].items():assert sha(R/p)==h
for e in c['producer_files']:assert sha(R/e['path'])==e['sha256']
assert c['stored_new_producer_occurrences']==182 and len(c['axiom_union'])==3 and c['fresh_source_control_rejections']==10
(D/'AUTHOR-READY-v1.json').write_text(json.dumps({'status':'AUTHOR_FOREST_FRONTIER_READY_REVIEW_PENDING','canonical_receipt':L,'new_source_modules':7,'dependency_source_olean_pairs':92,'independent_credit':0,'main_milestones':'ALL_OPEN','public_import':'OverheadBound','public_namespace':'GenericForest.FrontierWork','ordinary_callback_coefficient_paid_once':True,'local_overhead_polynomial_proved':False,'compiled_runtime_trace_correspondence':False},indent=2)+'\n')
files={p for p in D.rglob('*') if p.is_file() and p!=M and '__pycache__' not in p.parts};files|={p for p in O.rglob('*') if p.is_file() and '__pycache__' not in p.parts}
assert len(dependencies)==184 and dependencies<=files
for p in files:
 if p not in dependencies:assert p.stat().st_nlink==1,'UNDECLARED_HARD_LINK|'+str(p)
rows=[{'path':str(p.relative_to(R)),'sha256':sha(p),'bytes':p.stat().st_size,'readonly_dependency_snapshot':p in dependencies} for p in sorted(files)]
rec={'version':1,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'FROZEN_AUTHOR_FOREST_FRONTIER_WORK_REVIEW_PENDING','no_further_writes':True,'no_write_boundary':'This manifest and immutable_files. Continuations/reviews require new paths. Never rewrite/rebuild/chmod frozen original dependencies.','canonical_receipt':L,'new_source_modules':7,'dependency_source_olean_pairs':92,'dependency_rebuilds':0,'stored_new_producer_occurrences':182,'axiom_union':c['axiom_union'],'fresh_source_control_rejections':10,'main_milestones':'ALL_OPEN','independent_credit':0,'full_algorithm':False,'runtime_claim':False,'qualified_source_work_bound':True,'local_overhead_polynomial_proved':False,'compiled_runtime_trace_correspondence':False,'novelty':False,'runtime_ghost_used':False,'global_ordinary_ih_premise':False,'interfaces':c['interfaces'],'runtime_direct_references':c['runtime_direct_references'],'scope':'Source-level actual forest guard frontier retains failed queries and all raw occurrences; proper bounded ordinary query pairs and frontier mass<=1; exact all-input sourceWork decomposition; zero-ordinary forest overhead factor1/(1-2/c) for c>2 and separate ordinary D*c^q charged once under two explicit printed bill premises.','audit_scope':c['audit_scope'],'broad_runtime_IR_scope':c['broad_runtime_IR_scope'],'first_unprovided_main_call':c['first_unprovided_main_call'],'all_failures_retained':True,'frozen_inputs':spec['manifests'],'excluded_mutable':['Python __pycache__'],'immutable_files':rows}
M.write_text(json.dumps(rec,indent=2)+'\n')
for p in files:
 if p not in dependencies:p.chmod(0o444)
M.chmod(0o444)
for e in rows:assert sha(R/e['path'])==e['sha256']
print(rec['status'],len(rows),'files',sha(M),flush=True)
print('CERTIFICATE',L['certificate'],L['sha256'],flush=True)
