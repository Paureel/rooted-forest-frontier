# One-shot final seal, touching new own files only. Frozen inputs are rechecked.
from pathlib import Path
import datetime,hashlib,json,os,stat
D=Path(__file__).resolve().parent;R=D.parents[5]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
T=R/'research/rmaf/monitoring/next-20261016T095230Z/NUMERIC-INVARIANT-TARGET-v1.json';assert sha(T)=='ceedfbc9f7e34d0ecdbfbf22d40de14cfb5313b2d8b3095fd014004083d88020'
t=json.loads(T.read_text());assert D==R/t['own_directory']
for v in t['allowed_packages'].values():assert sha(R/v['manifest'])==v['sha256']
P=json.loads((D/'DEPENDENCY-PINS-v2.json').read_text())
for e in P['files']:
 p=R/e['path'];s=p.stat();assert (sha(p),s.st_size,s.st_ino,s.st_dev,stat.S_IMODE(s.st_mode))==(e['sha256'],e['bytes'],e['inode'],e['device'],e['mode'])
C=D/'author-audit-v4/certificate.json';c=json.loads(C.read_text());assert c['status']=='PASS_AUTHOR_GLOBAL_NUMERIC_SOURCE_BODY_AXIOM_AUDIT'
assert c['original_metadata_preserved'] and c['all_new_proof_bodies_retained'] and set(c['axiom_union'])<=set(['Classical.choice','Quot.sound','propext'])
for e in c['sources']:
 for k,h in [('source','source_sha256'),('olean','olean_sha256')]:assert sha(R/e[k])==e[h]
for e in c['new_producers']:assert sha(R/e['path'])==e['sha256']
for e in c['current_compile_bindings']:assert sha(R/e['receipt'])==e['sha256']
own=[x['module'] for x in c['new_producers']]
files=[]
for p in sorted(D.rglob('*')):
 if p.is_file() and p.name not in ['FINAL-MANIFEST-v1.json','FINAL-SEAL-v1.json'] and '__pycache__' not in p.parts:
  p.chmod(0o444);s=p.stat();files.append(dict(path=str(p.relative_to(R)),sha256=sha(p),bytes=s.st_size,mode=stat.S_IMODE(s.st_mode),inode=s.st_ino,device=s.st_dev))
m=dict(version=1,created_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),role='AUTHOR_GLOBAL_NUMERIC_STATE_INVARIANTS',status='FROZEN_AUTHOR_SEMANTIC_NUMERIC_INVARIANTS_REVIEW_PENDING',no_further_writes=True,target=str(T.relative_to(R)),target_sha256=sha(T),canonical_build=str(D.relative_to(R)),canonical_certificate=str(C.relative_to(R)),certificate_sha256=sha(C),source_pool=P['pool'],dependency_pins=str((D/'DEPENDENCY-PINS-v2.json').relative_to(R)),dependency_pins_sha256=sha(D/'DEPENDENCY-PINS-v2.json'),own_proof_modules=own,actual_imported_modules=c['actual_imported_modules'],frozen_imported_modules=c['inherited_exact_modules'],owned_stored_occurrences=c['owned_stored_occurrences'],all_owned_proof_bodies_retained=True,axiom_union=c['axiom_union'],independent_credit=0,initial_q='k-1',implicit_rho=False,full233=False,native=False,novelty=False,interfaces=str((D/'INTERFACE-TRACE-v1.json').relative_to(R)),result=str((D/'RESULT-v1.md').relative_to(R)),attained=['literal one-step label maximum increment at most2 over all source arms/orientations','exact ordinary source trace Reach; d+q+leafcount<=Q+N; max label<=M0+2(Q+N)','semantic label and local marker bits W=L+2(Q+N)+3; budget width<=Q+1','tree nodes+1<=2N; valid unary source/target addresses and vertex counts<=2N','all8 checked common-builder trees bounded','exact occurrence-preserving source callback list equality and derived forest-entry/paid-descendant semantic caps','source indices, cut counts and original source address cells bounded','actual FastOrdinary initialq=k-1; successful payload blocks/cells<=N, semantic bitcells<=N*W'],remaining=['represented producer storage widths and padding invariants; semantic widths alone insufficient','consumer binding to forest-entry companion or source-site lemmas and whole source-bit bill integration','full2.33/native execution/independent verification/novelty acceptance'],inherited_body_qualification=c['inherited_audit_qualification'],retained_failures=['author-audit-v1/certificate.json','author-audit-v2/certificate.json','author-audit-v3/certificate.json','all attempts/ receipts and logs'],resource_amendment=str((D/'AUDIT-RESOURCE-AMENDMENT-v2.json').relative_to(R)),original_modes_inodes_preserved=True,immutable_files=files,no_write_boundary='This manifest, final seal, and immutable_files. Continue or review in new paths only; never rewrite/rebuild/chmod frozen imports or this package.')
f=D/'FINAL-MANIFEST-v1.json';assert not f.exists();f.write_text(json.dumps(m,indent=2)+'\n');f.chmod(0o444)
seal=D/'FINAL-SEAL-v1.json';seal.write_text(json.dumps(dict(version=1,manifest=str(f.relative_to(R)),sha256=sha(f),manifest_bytes=f.stat().st_size,immutable_files=len(files)),indent=2)+'\n');seal.chmod(0o444)
print('FROZEN',sha(f),'files',len(files),'owned modules',len(own),'declarations',c['owned_stored_occurrences'])
