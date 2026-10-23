#!/usr/bin/env python3
"""One-shot optimizer readonly snapshot seal; never chmod or rewrite original dependencies."""
from pathlib import Path
import datetime,hashlib,json
D=Path(__file__).resolve().parent;R=D.parents[5];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();M=D/'FINAL-MANIFEST-v1.json';assert not M.exists(),'REFUSE_RESEAL'
O=R/json.loads((D/'ACTIVE-v1.json').read_text())['receipt'];C=O/'AUDIT-CERTIFICATE-v3.json';c=json.loads(C.read_text());assert c['status']=='PASS_AUTHOR_OPTIMIZER_WRAPPER_RECOVERY_PROVIDER_OPEN'
originals={}
def record(p):
 s=p.stat();e={'path':str(p.relative_to(R)),'sha256':sha(p),'mode':oct(s.st_mode&0o777),'inode':s.st_ino,'device':s.st_dev};originals[e['path']]=e
for n in ['DEPENDENCIES-BEFORE-v1.json','TRANSITIVE-EARLY-DEPS-v1.json']:
 for e in json.loads((D/n).read_text())['members']:
  p=R/e['path'];s=p.stat();assert sha(p)==e['sha256'] and oct(s.st_mode&0o777)==e['mode'] and s.st_ino==e['inode'] and s.st_dev==e['device'];record(p)
target=R/'research/rmaf/monitoring/next-20261016T085144Z/OPTIMIZER-LOCAL-TARGET-v1.json';assert sha(target)=='9fb3ecba7dc8cee1d26feecc789408d77dfc839277d0b17f1aa2f7b95fe0d49d';record(target);(O/'TARGET-v1.json').write_bytes(target.read_bytes())
for e in json.loads(target.read_text())['allowed_packages']:
 p=R/e['manifest'];assert sha(p)==e['sha256'];record(p)
ip=R/c['instrument']['path'];assert sha(ip)==c['instrument']['sha256'];record(ip)
ready={'version':1,'status':'FROZEN_AUTHOR_OPTIMIZER_WRAPPER_RECOVERY_PROVIDER_OPEN_REVIEW_PENDING','canonical_receipt':str(O.relative_to(R)),'canonical_import':'OWOptimize','budget_range_import':'OWBudgets','namespace':'OrdinaryDispatch.OptimizerLocalWork','audit_certificate':str(C.relative_to(R)),'audit_certificate_sha256':sha(C),'main_interface':'actual_wrapper_fees','value_interface':'meterOptimize_value','preflight_fee':'256*(N+1)^2','per_trial_fee':12,'final_record_fee':32,'wrapper_polynomial':'512*(N+1)^2','raw_recovery_guard':'2048*(R+1)^5 for R>=treeNodes S,P.length,P.flatten.length','callback_solve_work':'explicit w:Nat->Nat; no actual solve bound proved here','three_wrapper_fees':'DERIVED_STRUCTURAL_SOURCE_AUTHOR_LEVEL','recovery_value_correspondence':True,'recovery_source_provider':'OPEN: CoreWork.initialCharge and localCharge primitive interpretation','conditional_counter_interface':'conditional_233_derived_wrapper','first_gap':str((D/'FIRST-GAP-v1.md').relative_to(R)),'independent_credit':0,'scalar_bit_native':'OPEN','full_algorithm_base_novelty':'ALL_OPEN','no_children_or_peer_messages':True}
(D/'PUBLIC-INTERFACE-v1.json').write_text(json.dumps(ready,indent=2)+'\n')
for p in sorted(D.rglob('*')):
 if p.is_file() and '__pycache__' not in p.parts:
  record(p);q=O/'input-snapshot'/p.relative_to(D);q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(p.read_bytes())
for p in O.rglob('*'):
 if p.is_file() and '__pycache__' not in p.parts:p.chmod(0o444)
files=[{'path':str(p.relative_to(R)),'sha256':sha(p),'bytes':p.stat().st_size} for p in sorted(O.rglob('*')) if p.is_file() and '__pycache__' not in p.parts]
runs=[json.loads(p.read_text()) for p in O.glob('*.run.json')]
m={**ready,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'no_further_writes':True,'no_write_boundary':'This manifest, all immutable_files and pinned original files. Continue only in new disjoint paths. Preserve hashes/modes/inodes.','immutable_files':files,'original_files':list(originals.values()),'source_modules':c['modules'],'stored_new_occurrences':c['stored_occurrences'],'axiom_union':c['axiom_union'],'controls':c['controls'],'source_false_diagnoses':10,'dependency_rebuilds':0,'same_lineage':True,'maximum_measured_Lean_seconds':max(r['seconds'] for r in runs),'process_cap_seconds':60,'lean_memory_cap_MiB':3072,'live_disk_floor_GiB':3,'raw_output_cap_MiB':16,'skipped':c['skipped'],'source_qualification':c['source_boundary'],'audit_scope':'Five owned stored producers only; all nonproof/opaque bodies retained; actual full proof reference/axiom walk. No all-imported-body or native execution claim.','preserved_earlier_audits':['AUDIT-CERTIFICATE-v1.json failed control-count check','AUDIT-CERTIFICATE-v2.json passed original four modules','AUDIT-CERTIFICATE-v3.json passed five modules including all-trial budget bounds']}
M.write_text(json.dumps(m,indent=2)+'\n');M.chmod(0o444);h=D/'FINAL-MANIFEST-v1.sha256';h.write_text(sha(M)+'  FINAL-MANIFEST-v1.json\n');h.chmod(0o444)
print('SEALED_OPTIMIZER_LOCAL',len(files),'readonly members',sha(M))
