from pathlib import Path
import json,hashlib,datetime,shutil
D=Path(__file__).resolve().parent;R=D.parents[5]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def check(row):
 p=R/row['path'];s=p.stat()
 assert sha(p)==row['sha256'],row['path']
 assert s.st_size==row['bytes'],row['path']
 for key,val in [('mode',s.st_mode&0o7777),('inode',s.st_ino),('device',s.st_dev)]:
  if key in row:assert val==row[key],(row['path'],key)
assert not (D/'FINAL-MANIFEST-v1.json').exists()
assert shutil.disk_usage(D).free>=3*(1<<30)
target=R/'research/rmaf/monitoring/producer-assembly-next-20261016T110601Z/NUMERIC-PRODUCER-BINDING-TARGET-v1.json'
assert sha(target)=='867d2620961f9a974f0421ce8e7dd4615a6d020313417396327bede647bca862'
for row in json.loads((D/'DEPENDENCY-PINS-v1.json').read_text())['files']:check(row)
prior=json.loads((D/'PREVIOUS-PRESERVATION-v1.json').read_text())
for row in prior['files']:check(row)
C=json.loads((D/'author-audit-v1/certificate.json').read_text());assert C['status']=='PASS_AUTHOR_PRODUCER_SELECTOR_CANONICAL_BUDGET_AUDIT'
for p,h in C['inputs'].items():assert sha(R/p)==h
for row in C['sources']:assert sha(R/row['source'])==row['source_sha256'] and sha(R/row['olean'])==row['olean_sha256']
for row in C['current_compile_bindings']:
 p=R/row['receipt'];assert sha(p)==row['sha256'];j=json.loads(p.read_text());assert j['accepted'] and j['exit']==0 and j['expected']==0
 assert sha(D/(row['module']+'.lean'))==j['source_sha256'] and sha(D/(row['module']+'.olean'))==j['olean_sha256']
for row in C['new_producers']:assert sha(R/row['path'])==row['sha256']
interface=D/'INTERFACE-TRACE-v1.json';j=json.loads(interface.read_text());j['status']='FROZEN_LOCAL_INTERFACES';interface.write_text(json.dumps(j,indent=2)+'\n')
files=[]
for p in sorted(D.rglob('*')):
 if p.is_file():
  assert not p.is_symlink();s=p.stat();p.chmod(0o444);t=p.stat();assert (s.st_ino,s.st_dev)==(t.st_ino,t.st_dev)
  files.append({'path':str(p.relative_to(R)),'sha256':sha(p),'bytes':t.st_size,'mode':t.st_mode&0o7777,'inode':t.st_ino,'device':t.st_dev})
manifest={'version':1,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'role':'AUTHOR_SOURCE_SELECTORS_AND_PAID_CANONICAL_BUDGET_BINDING','status':'LOCAL_SOURCE_SITES_CLOSED_FULL_PRODUCER_AND_MATCHING_DEPTH_OPEN','no_further_writes':True,'target':str(target.relative_to(R)),'target_sha256':sha(target),'canonical_build':str(D.relative_to(R)),'canonical_certificate':str((D/'author-audit-v1/certificate.json').relative_to(R)),'certificate_sha256':sha(D/'author-audit-v1/certificate.json'),'previous_completed':{'manifest':'research/rmaf/algorithm/universal233/ordinary_dispatch/numeric_stored_width_20261016T103025Z/FINAL-MANIFEST-v1.json','sha256':'5cc4ad1f19e458ff5163a58b245d2b1fcb187fdf8378e68df06352e945276146'},'source_pool':'results/algorithm-universal233-binary-producer-costs-final-20261016T103025Z-20261016T105607Z','dependency_pins':str((D/'DEPENDENCY-PINS-v1.json').relative_to(R)),'dependency_pins_sha256':sha(D/'DEPENDENCY-PINS-v1.json'),'own_modules':[e['module'] for e in C['new_producers']],'actual_imported_modules':C['actual_imported_modules'],'actual_frozen_modules':C['actual_frozen_modules'],'owned_stored_occurrences':C['owned_stored_occurrences'],'all_new_proof_pretty_text':False,'all_executable_bodies':True,'actual_full_proof_reference_axiom_walk':True,'full_theorem_pretty_text_modules':['ProducerBudgetTrim'],'axiom_union':C['axiom_union'],'registered_runtime_roots':len(C['runtime_scan']['registered']),'runtime_visited_declarations':len(C['runtime_scan']['visited']),'standard_runtime_boundaries':len(C['runtime_scan']['standard_boundary']),'positive_closed_assertions':16,'negative_math_rejections':4,'previous_numeric_immutable_files_preserved':prior['count'],'semantic_objects_imported':0,'attained':['Exact finite common X/Y and first representative construction with copied scans and polynomial fees','Actual successful builder payload projection and local OrientedStep extension','Paid canonical-budget variant with no lineage-event D needed at its actual root/payment/allocation outputs','Raw/scheduler/concrete-generated source projections retain order, guards, duplicates and refusal under typed recursive refinement','Exact reached-callback normalization ledgers and concrete generated-parent work equation'],'remaining':json.loads((D/'INTERFACE-TRACE-v1.json').read_text())['remaining'],'old_padded_variant':'Preserved, old D gap open','retained_failures':'All failed source/log/receipt attempts, default recursion-depth pilot and four deliberate false math controls retained','unchanged_resource_controls':True,'same_author':True,'independent_credit':0,'native':False,'novelty':False,'full_bit':False,'full_233':False,'immutable_files':files,'self_hash':'FINAL-SEAL-v1.json; manifest and seal excluded recursively'}
p=D/'FINAL-MANIFEST-v1.json';p.write_text(json.dumps(manifest,indent=2)+'\n');p.chmod(0o444)
seal={'manifest':str(p.relative_to(R)),'sha256':sha(p),'immutable_files':len(files),'status':manifest['status'],'no_further_writes':True};f=D/'FINAL-SEAL-v1.json';f.write_text(json.dumps(seal,indent=2)+'\n');f.chmod(0o444)
for row in files:check(row)
for row in prior['files']:check(row)
print(json.dumps(seal))
