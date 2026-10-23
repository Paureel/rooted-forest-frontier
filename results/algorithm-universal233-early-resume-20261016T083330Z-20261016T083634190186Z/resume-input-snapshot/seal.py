#!/usr/bin/env python3
"""One-shot immutable local package seal; original files and dependency modes stay unchanged."""
from pathlib import Path
import datetime,hashlib,json,shutil
D=Path(__file__).resolve().parent;A=D.parent;R=A.parents[5];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
M=A/'FINAL-MANIFEST-v1.json';assert not M.exists(),'REFUSE_RESEAL'
O=R/json.loads((D/'ACTIVE-v1.json').read_text())['receipt'];c=O/'AUDIT-CERTIFICATE-v1.json';cert=json.loads(c.read_text());assert cert['status']=='PASS_AUTHOR_ACTUAL_EARLY_UNIT_SCALAR_OPEN'
target=R/'research/rmaf/monitoring/resume-20261016T083330Z/early-TARGET-v1.json';assert sha(target)=='6ce430dcb0d0e595c8e06728cc6ce959d0c28bd98a529d4416ed9e45b4f4aaca';t=json.loads(target.read_text())
originals={}
def original(p):
 st=p.stat();originals[str(p.relative_to(R))]={'path':str(p.relative_to(R)),'sha256':sha(p),'mode':oct(st.st_mode&0o777),'inode':st.st_ino,'device':st.st_dev}
for e in t['own_checkpoint_sha256']:
 p=R/e['path'];assert sha(p)==e['sha256'];original(p);q=O/'retained-checkpoint'/p.relative_to(A);q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(p.read_bytes())
for e in json.loads((D/'DEPENDENCY-INITIAL-v1.json').read_text())['members']:
 p=R/e['path'];st=p.stat();assert sha(p)==e['sha256'] and oct(st.st_mode&0o777)==e['mode'] and st.st_ino==e['inode'] and st.st_dev==e['device'];original(p)
for item in json.loads((D/'PRIOR-EVIDENCE-v1.json').read_text())['directories']:
 for e in item['files']:
  p=R/e['path'];assert sha(p)==e['sha256'];original(p);q=O/'prior-evidence'/p.relative_to(R/'results');q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(p.read_bytes())
ready={'version':1,'status':'FROZEN_AUTHOR_ACTUAL_EARLY_UNIT_SCALAR_OPEN_REVIEW_PENDING','canonical_receipt':str(O.relative_to(R)),'audit_certificate':str(c.relative_to(R)),'audit_certificate_sha256':sha(c),'canonical_import':'ERInterface','namespace':'OrdinaryDispatch.EarlyLocalWork','primitive_interfaces':['meterSelect','meterSelect_value','meterSelect_bound','meterRule4Select','meterRule4Select_value','meterRule4Select_bound','cherry_select_envelope','rule4_select_envelope','earlier_clear_primitive_envelopes'],'tree_premises':['treeNodes T<=N','treeNodes S<=N'],'cherry_cap':'2048*(N+1)^5','rule4_cap':'262144*(N+1)^6','both_primitive_orientations_cap':'1048576*(N+1)^6','prefix_cap':'2097152*(N+1)^6','budget_hypothesis':None,'scalar_interpretation':'OPEN; arbitrary fee multiplication is only a weighted structural model','native_trace_claim':False,'independent_credit':0,'full_algorithm_acceptance':False,'novelty':False,'first_gap':str((D/'FIRST-GAP-v1.md').relative_to(R))}
(D/'AUTHOR-READY-v1.json').write_text(json.dumps(ready,indent=2)+'\n')
(A/'PUBLIC-INTERFACE-v1.json').write_text(json.dumps(ready,indent=2)+'\n');original(A/'PUBLIC-INTERFACE-v1.json');(O/'PUBLIC-INTERFACE-v1.json').write_bytes((A/'PUBLIC-INTERFACE-v1.json').read_bytes())
for p in sorted(D.rglob('*')):
 if p.is_file() and '__pycache__' not in p.parts:
  original(p);q=O/'resume-input-snapshot'/p.relative_to(D);q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(p.read_bytes())
original(target);(O/'RESUME-TARGET-v1.json').write_bytes(target.read_bytes())
# Preserve the exact wrapper used for the successful audit, separately from later replay support.
(O/'AUDIT-EXECUTED-WRAPPER.py').write_bytes((D/'run-before-replay-support.py').read_bytes())
for p in O.rglob('*'):
 if p.is_file() and '__pycache__' not in p.parts:p.chmod(0o444)
files=[{'path':str(p.relative_to(R)),'sha256':sha(p),'bytes':p.stat().st_size,'readonly_source_snapshot':p.suffix in ['.lean','.olean']} for p in sorted(O.rglob('*')) if p.is_file() and '__pycache__' not in p.parts]
m={**ready,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'no_further_writes':True,'no_write_boundary':'Manifest, canonical receipt and all immutable_files. Continue in new disjoint paths; retain original hashes/modes/inodes.','immutable_files':files,'original_files':list(originals.values()),'source_modules':cert['modules'],'stored_new_producer_occurrences':cert['stored_new_occurrences'],'axiom_union':cert['axiom_union'],'controls':cert['controls'],'dependency_rebuilds':0,'reused_dependency_manifest_records':5711,'original_developments_unchanged':True,'prior_own_result_directories':len(json.loads((D/'PRIOR-EVIDENCE-v1.json').read_text())['directories']),'audit_scope':'Twelve owned stored producers only; full nonproof/opaque bodies, actual full-proof reference/axiom walk; no imported-all-stored or native semantic claim.','fresh_source_false_rejections':10,'other_corruption_controls':['changed source hash','missing producer','duplicate occurrence','custom axiom'],'full_algorithm_base_novelty':'ALL_OPEN','same_lineage':True,'fresh_nonauthor_review':'PENDING','skipped':cert['skipped']}
M.write_text(json.dumps(m,indent=2)+'\n');M.chmod(0o444);H=A/'FINAL-MANIFEST-v1.sha256';H.write_text(sha(M)+'  FINAL-MANIFEST-v1.json\n');H.chmod(0o444)
print('SEALED',len(files),'readonly members','manifest_sha256',sha(M))
