#!/usr/bin/env python3
"""Seal the budget-local author extension and retained attempts only."""
from pathlib import Path
import datetime,hashlib,json
D=Path(__file__).resolve().parent;R=next(p for p in D.parents if (p/'bootloops-lean').exists());M=D/'FINAL-MANIFEST-v1.json'
if M.exists():raise SystemExit('FROZEN_NO_WRITE_BOUNDARY')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
L=json.loads((D/'LATEST-REPLAY-v1.json').read_text());O=R/L['receipt'];C=R/L['certificate'];assert sha(C)==L['sha256'];c=json.loads(C.read_text());assert c['status']=='PASS_AUTHOR_BOTH_BAD_LOCAL_BINDING_OPEN'
spec=json.loads((D/'ROOT-v2.json').read_text());confirmation=json.loads((D/'POOL-FREEZE-CONFIRM-v1.json').read_text());assert sha(D/'ROOT-v2.json')==c['root_pin_sha256'];assert sha(D/'POOL-FREEZE-CONFIRM-v1.json')==c['pool_freeze_confirmation_sha256']
for f in spec['frozen_manifests']+[spec['overlap_manifest'],confirmation['manifest']]:assert sha(R/f['path'])==f['sha256']
dependencies=set()
for e in spec['dependencies']:
 for f in e['files']:
  for k in ['pool_source','copied']:
   p=R/f[k];assert sha(p)==f['sha256'] and not p.stat().st_mode&0o222
  dependencies.add(R/f['copied'])
for e in c['new_modules']:
 assert sha(R/e['source'])==e['source_sha256'];assert sha(R/e['compiled_source'])==e['source_sha256'];assert sha(R/e['olean'])==e['olean_sha256']
for p,h in c['input_hashes'].items():assert sha(R/p)==h
for e in c['producer_files']:assert sha(R/e['path'])==e['sha256']
assert c['stored_new_producer_occurrences']==60 and len(c['axiom_union'])==3 and c['fresh_source_control_rejections']==9
(D/'AUTHOR-READY-v1.json').write_text(json.dumps({'status':'AUTHOR_BOTH_BAD_LOCAL_READY_REVIEW_PENDING','canonical_receipt':L,'new_source_modules':5,'dependency_source_olean_pairs':169,'independent_credit':0,'main_milestones':'ALL_OPEN','generic_interfaces':['ordinaryExecution_answer_congr_at','ordinary_candidate_local','ordinary_candidate_below'],'runtime_ghost_used':False,'global_ordinary_ih_premise':False},indent=2)+'\n')
files={p for p in D.rglob('*') if p.is_file() and p!=M and '__pycache__' not in p.parts};files|={p for p in O.rglob('*') if p.is_file() and '__pycache__' not in p.parts}
assert len(dependencies)==338 and dependencies<=files
for p in files:assert p.stat().st_nlink==1,'UNDECLARED_HARD_LINK|'+str(p)
rows=[{'path':str(p.relative_to(R)),'sha256':sha(p),'bytes':p.stat().st_size,'readonly_dependency_snapshot':p in dependencies} for p in sorted(files)]
rec={'version':1,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'FROZEN_AUTHOR_BOTH_BAD_LOCAL_BINDING_REVIEW_PENDING','no_further_writes':True,'no_write_boundary':'This manifest and immutable_files. Continuations/reviews require new paths. Never rewrite or rebuild dependency snapshots.','canonical_receipt':L,'new_source_modules':5,'dependency_source_olean_pairs':169,'dependency_rebuilds':0,'stored_new_producer_occurrences':60,'axiom_union':c['axiom_union'],'fresh_source_control_rejections':9,'main_milestones':'ALL_OPEN','independent_credit':0,'full_algorithm':False,'runtime_claim':False,'novelty':False,'runtime_ghost_used':False,'global_ordinary_ih_premise':False,'interfaces':c['interfaces'],'runtime_direct_references':c['runtime_direct_references'],'scope':'Literal solvePair(GenericForest.solve actual), BelowIH-only original-geometry conditional cover/minimum among parent-refining agreements, every planned entry budget+3<=q, strict actual calls and retained trace mass; reusable all-input ordinary answer locality and budget-local ordinary candidate.','audit_scope':c['audit_scope'],'first_unprovided_main_call':c['first_unprovided_main_call'],'all_failures_retained':True,'dependency_copies_confirmed_against_frozen_pool':confirmation['manifest'],'own_overlap_input':spec['overlap_manifest'],'excluded_mutable':['Python __pycache__'],'immutable_files':rows}
M.write_text(json.dumps(rec,indent=2)+'\n')
for p in files:
 if p not in dependencies:p.chmod(0o444)
M.chmod(0o444)
for e in rows:assert sha(R/e['path'])==e['sha256']
print(rec['status'],len(rows),'files',sha(M),flush=True)
