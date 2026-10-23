#!/usr/bin/env python3
"""Seal only new checker files/evidence; preserve all frozen input inodes/modes."""
from pathlib import Path
import datetime,hashlib,json
D=Path(__file__).resolve().parent;R=next(p for p in D.parents if (p/'bootloops-lean').exists());M=D/'FINAL-MANIFEST-v1.json'
if M.exists():raise SystemExit('FROZEN_NO_WRITE_BOUNDARY')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
L=json.loads((D/'LATEST-REPLAY-v1.json').read_text());O=R/L['receipt'];C=R/L['certificate'];assert sha(C)==L['sha256'];c=json.loads(C.read_text());assert c['status']=='PASS_AUTHOR_FOREST_SCALAR_REFERENCE_NATIVE_OPEN'
spec=json.loads((D/'ROOT-v1.json').read_text());assert sha(D/'ROOT-v1.json')==c['root_pin_sha256']
for m in spec['manifests']:assert sha(R/m['path'])==m['sha256']
dependencies=set()
for e in spec['dependencies']:
 for f in e['files']:
  p=R/f['original'];assert sha(p)==f['sha256'] and oct(p.stat().st_mode&0o777)==f['original_mode']
  p=R/f['linked'];st=p.stat();assert sha(p)==f['sha256'] and not st.st_mode&0o222;assert (st.st_ino,st.st_dev)==(f['inode'],f['device']);dependencies.add(p)
for e in spec['identical_source_contacts']:
 f=e['identical'];p=R/f['original'];assert sha(p)==f['sha256'] and oct(p.stat().st_mode&0o777)==f['original_mode']
for e in c['new_modules']:
 assert sha(R/e['source'])==e['source_sha256'];assert sha(R/e['compiled_source'])==e['source_sha256'];assert sha(R/e['olean'])==e['olean_sha256']
for p,h in c['input_hashes'].items():assert sha(R/p)==h
for e in c['producer_files']:assert sha(R/e['path'])==e['sha256']
assert c['stored_new_producer_occurrences']==614 and len(c['axiom_union'])==3 and c['fresh_source_control_rejections']==10
(D/'AUTHOR-READY-v1.json').write_text(json.dumps({'status':'AUTHOR_FOREST_SCALAR_REFERENCE_READY_REVIEW_PENDING','canonical_receipt':L,'new_source_modules':20,'dependency_source_olean_pairs':454,'independent_credit':0,'main_milestones':'ALL_OPEN','runtime_ghost_used':False,'public_import':'PolynomialBitBound','public_namespace':'GenericForest.ScalarBits','scalar_bit_lift':'PROVED_REFERENCE_PROVIDER_SCOPE_NATIVE_BINDING_OPEN'},indent=2)+'\n')
files={p for p in D.rglob('*') if p.is_file() and p!=M and '__pycache__' not in p.parts};files|={p for p in O.rglob('*') if p.is_file() and '__pycache__' not in p.parts}
assert len(dependencies)==908 and dependencies<=files
for p in files:
 if p not in dependencies:assert p.stat().st_nlink==1,'UNDECLARED_HARD_LINK|'+str(p)
rows=[{'path':str(p.relative_to(R)),'sha256':sha(p),'bytes':p.stat().st_size,'readonly_dependency_snapshot':p in dependencies} for p in sorted(files)]
rec={'version':1,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'FROZEN_AUTHOR_FOREST_SCALAR_REFERENCE_NATIVE_OPEN_REVIEW_PENDING','no_further_writes':True,'no_write_boundary':'This manifest and immutable_files. Continuations/reviews require new paths. Never rewrite/rebuild/chmod input dependencies.','canonical_receipt':L,'new_source_modules':20,'dependency_source_olean_pairs':454,'dependency_rebuilds':0,'stored_new_producer_occurrences':614,'axiom_union':c['axiom_union'],'fresh_source_control_rejections':10,'main_milestones':'ALL_OPEN','independent_credit':0,'full_algorithm':False,'runtime_claim':False,'binary_scalar_reference_values_proved':True,'binary_scalar_reference_work_proved':True,'binary_checker_reference_lift_proved':True,'actual_payload_bound_proved':True,'concrete_reference_checker_cap':'256*(L+14+8*labelBits(4*n+q+1))*4096*(4*n+q+1)^8 under actual proper/input-label/payload guards','native_scalar_runtime_correspondence_proved':False,'compiled_runtime_trace_correspondence':False,'novelty':False,'runtime_ghost_used':False,'interfaces':c['interfaces'],'runtime_direct_references':c['runtime_direct_references'],'scope':'Finite binary reference equality/order/add/sub/max/copy and list/index counters with exact values and concrete work; complete structural checker reference lift polynomial in input label bit cap plus log(volume) and degree8 shape factor. Actual FastOrdinary/scheduler/raw/initial payload bounds supplied before checking. Encode/decode are mathematical representation boundaries; native conversion/backend/provider binding and whole compiled runtime remain OPEN.','audit_scope':c['audit_scope'],'first_unprovided_main_call':c['first_unprovided_main_call'],'all_failures_retained':True,'frozen_inputs':spec['manifests'],'original_mode_qualification':'454 readonly exact frozen checker-closure source/olean pairs; preserve every original mode/hash/inode; parent checker release retains earlier writable-original qualification.','excluded_mutable':['Python __pycache__'],'immutable_files':rows}
M.write_text(json.dumps(rec,indent=2)+'\n')
for p in files:
 if p not in dependencies:p.chmod(0o444)
M.chmod(0o444)
for e in rows:assert sha(R/e['path'])==e['sha256']
print(rec['status'],len(rows),'files',sha(M),flush=True)
print('CERTIFICATE',L['certificate'],L['sha256'],flush=True)
