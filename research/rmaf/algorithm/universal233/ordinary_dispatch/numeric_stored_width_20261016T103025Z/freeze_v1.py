# One-shot own-package seal. All imported and previous frozen metadata rechecked.
from pathlib import Path
import datetime,hashlib,json,stat
D=Path(__file__).resolve().parent;R=D.parents[5]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
T=R/'research/rmaf/monitoring/next-20261016T103025Z/NUMERIC-STORED-WIDTH-TARGET-v1.json';assert sha(T)=='c0097c45a2dcb8928b30216c8f68a9f727be259b9971deae3b776e8624ee02a7'
t=json.loads(T.read_text());assert D==R/t['own_directory']
for key in ['binary_producers','numeric_semantic']:
 e=t['allowed_packages'][key];assert sha(R/e['manifest'])==e['sha256']
P=json.loads((D/'DEPENDENCY-PINS-v3.json').read_text())
for e in P['files']:
 p=R/e['path'];s=p.stat();assert (sha(p),s.st_size,s.st_ino,s.st_dev,stat.S_IMODE(s.st_mode))==(e['sha256'],e['bytes'],e['inode'],e['device'],e['mode'])
old=json.loads((R/t['previous_completed']['manifest']).read_text())
for e in old['immutable_files']:
 p=R/e['path'];s=p.stat();assert (sha(p),s.st_size,s.st_ino,s.st_dev,stat.S_IMODE(s.st_mode))==(e['sha256'],e['bytes'],e['inode'],e['device'],e['mode'])
C=D/'author-audit-v3/certificate.json';c=json.loads(C.read_text());assert c['status']=='PASS_AUTHOR_FINITE_BIT_FRESH_STORED_WIDTH_AUDIT'
assert c['original_metadata_preserved'] and c['all_new_nonproof_bodies_retained'] and c['actual_full_proof_reference_axiom_walk']
assert not c['all_new_proof_bodies_retained'] and set(c['axiom_union'])<=set(['Classical.choice','Quot.sound','propext'])
for e in c['sources']:
 for k,h in [('source','source_sha256'),('olean','olean_sha256')]:assert sha(R/e[k])==e[h]
for e in c['new_producers']:assert sha(R/e['path'])==e['sha256']
for e in c['current_compile_bindings']:assert sha(R/e['receipt'])==e['sha256']
ctrl=json.loads((D/'CONTROL-RESULTS-v1.json').read_text());assert ctrl['total_observed']==ctrl['total_expected']==7
for e in ctrl['mathematical_negative_controls']:
 assert sha(R/e['receipt'])==e['receipt_sha256'] and sha(R/e['log'])==e['log_sha256']
files=[]
for p in sorted(D.rglob('*')):
 if p.is_file() and p.name not in ['FINAL-MANIFEST-v1.json','FINAL-SEAL-v1.json'] and '__pycache__' not in p.parts:
  p.chmod(0o444);s=p.stat();files.append(dict(path=str(p.relative_to(R)),sha256=sha(p),bytes=s.st_size,mode=stat.S_IMODE(s.st_mode),inode=s.st_ino,device=s.st_dev))
m=dict(version=1,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),role='SAME_AUTHOR_FINITE_BIT_FRESH_MARKERS_AND_STORED_WIDTHS',status='FROZEN_AUTHOR_LOCAL_FINITE_BIT_MARKERS_CONDITIONAL_STORAGE_REVIEW_PENDING',no_further_writes=True,target=str(T.relative_to(R)),target_sha256=sha(T),canonical_build=str(D.relative_to(R)),canonical_certificate=str(C.relative_to(R)),certificate_sha256=sha(C),previous_completed=t['previous_completed'],previous_semantic_pins_rechecked=len(old['immutable_files']),source_pool=P['pool'],dependency_pins=str((D/'DEPENDENCY-PINS-v3.json').relative_to(R)),dependency_pins_sha256=sha(D/'DEPENDENCY-PINS-v3.json'),own_modules=[e['module'] for e in c['new_producers']],actual_imported_modules=c['actual_imported_modules'],frozen_imported_modules=c['inherited_exact_modules'],owned_stored_occurrences=c['owned_stored_occurrences'],all_owned_nonproof_opaque_bodies_retained=True,actual_full_proof_reference_axiom_walk=True,all_owned_theorem_text_retained=False,full_theorem_text_modules=['StoredMax'],body_qualification=str((D/'AUDIT-QUALIFICATION-v2.json').relative_to(R)),axiom_union=c['axiom_union'],runtime_roots=len(c['runtime_scan']['registered']),runtime_references=len(c['runtime_scan']['visited']),standard_boundary_names=len(c['runtime_scan']['standard_boundary']),runtime_mathematical_projection_references=0,initial_q='k-1',implicit_rho=False,initial_stored_label_width='B independent of semanticL',initial_stored_budget_width='Bq independent of decodedQ',state_label_width='B+2*(Q+N), conditional on matching OrientedPath and semantic Reach at depth<=Q+N',local_marker_width='B+2*(Q+N)+2 under same conditional trace binding',budget_width='Bq+(4*N+3)*D; explicit original-input budget-event boundD still OPEN',local_fees=['freshOneFee','freshPairFee','contractPairFee','markedFee','commonPayloadFee'],interfaces=str((D/'INTERFACE-TRACE-v1.json').relative_to(R)),result=str((D/'RESULT-v1.md').relative_to(R)),first_gap=str((D/'FIRST-GAP-v1.json').relative_to(R)),attained=['concrete copied finite-bit max, successor and double successor with actual commonFresh/Setup marker values','all8 represented common payload and contraction/marked relabel values/widths/fees','both orientations storage transport over completed represented constructors','input-storage-sensitive completed disjoint allocator budget cap and conditional budget-event composition','executed known and hostile controls; current source/object and qualified body/axiom/runtime-reference audit'],remaining=json.loads((D/'INTERFACE-TRACE-v1.json').read_text())['remaining'],full233=False,native=False,independent_credit=0,novelty=False,retained_failures=['author-audit-v1/certificate.json','all attempts/ source/log/receipt files','CONTROL-DIAGNOSIS-v3.json'],accepted_audits=['author-audit-v2/certificate.json','author-audit-v3/certificate.json'],source_pool_union=False,frozen_dependency_rebuilds=0,original_modes_inodes_preserved=True,immutable_files=files,no_write_boundary='This manifest, final seal, immutable_files. Continue/review in new paths only; preserve every frozen object/source/mode/inode and failure.')
f=D/'FINAL-MANIFEST-v1.json';assert not f.exists();f.write_text(json.dumps(m,indent=2)+'\n');f.chmod(0o444)
p=D/'FINAL-SEAL-v1.json';p.write_text(json.dumps(dict(version=1,manifest=str(f.relative_to(R)),sha256=sha(f),manifest_bytes=f.stat().st_size,immutable_files=len(files)),indent=2)+'\n');p.chmod(0o444)
print('FROZEN',sha(f),'files',len(files),'modules',len(m['own_modules']),'stored',m['owned_stored_occurrences'])
