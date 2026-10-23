# One-shot immutable continuation snapshot. Original writable development
# sources and all older frozen inodes/modes remain untouched.
from pathlib import Path
import datetime,hashlib,json,shutil
D=Path(__file__).resolve().parent;R=D.parents[6]
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1<<20),b''):h.update(b)
 return h.hexdigest()
T=R/'research/rmaf/monitoring/resume-20261016T083330Z/global-TARGET-v1.json'
assert sha(T)=='7f6447681ad1ffe4f98acdf7ee1b6120f713afcef701d66edc05b91b7079d30b'
t=json.loads(T.read_text());build=json.loads((D/'RESUME-BUILD-v1.json').read_text());B=R/build['directory']
audit=json.loads((D/'LATEST-AUDIT-v1.json').read_text());C=R/audit['certificate'];assert sha(C)==audit['certificate_sha256']
c=json.loads(C.read_text());assert c['status']=='PASS_AUTHOR_SOURCE_BOUND_ORDINARY_CALL_RECURRENCE'
assert c['fresh_producer_modules']==11 and c['fresh_full_body_modules']==7 and c['qualified_proof_text_omission_modules']==4
assert c['axiom_union']==['Classical.choice','Quot.sound','propext']
for p,h in c['inputs'].items():assert sha(R/p)==h
for e in c['sources']:
 assert sha(B/(e['module']+'.lean'))==e['source_sha256'];assert sha(B/(e['module']+'.olean'))==e['olean_sha256']
checkpoints=[]
for e in t['own_checkpoint_sha256']:
 p=R/e['path'];assert sha(p)==e['sha256'];s=p.stat()
 checkpoints.append(dict(e,original_mode=oct(s.st_mode&0o777),original_inode=s.st_ino,mutation='NONE'))
assert shutil.disk_usage(R).free>=3*(1<<30)
S=B/'continuation-source-snapshot';assert not S.exists();S.mkdir()
for p in sorted(D.iterdir()):
 if p.is_file() and p.name!='FINAL-MANIFEST-v1.json':
  q=S/p.name;shutil.copyfile(p,q);assert sha(p)==sha(q);q.chmod(0o444)
shutil.copyfile(T,S/'resumption-TARGET-v1.json');(S/'resumption-TARGET-v1.json').chmod(0o444)
files=[]
for p in sorted(B.rglob('*')):
 if not p.is_file():continue
 s=p.stat()
 if s.st_nlink>1:assert not s.st_mode&0o222,('SHARED_WRITABLE_FILE',str(p))
 else:p.chmod(s.st_mode&0o555)
 files.append(dict(path=str(p.relative_to(R)),sha256=sha(p),bytes=p.stat().st_size,mode=oct(p.stat().st_mode&0o777)))
for e in files:
 p=R/e['path'];assert sha(p)==e['sha256'] and not p.stat().st_mode&0o222
F=D/'FINAL-MANIFEST-v1.json';assert not F.exists()
manifest=dict(version=1,created_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
 status='FROZEN_AUTHOR_SOURCE_BOUND_ORDINARY_CALL_RECURRENCE_REVIEW_PENDING',no_further_writes=True,
 no_write_boundary='This manifest, its exact copy, and immutable_files; original writable development files are represented by exact readonly snapshots and were not chmodded.',
 target=str(T.relative_to(R)),target_sha256=sha(T),canonical_build=str(B.relative_to(R)),
 canonical_audit=audit['directory'],canonical_certificate=str(C.relative_to(R)),certificate_sha256=sha(C),
 source_snapshot=str(S.relative_to(R)),result=str((S/'RESULT-v1.md').relative_to(R)),
 interface_trace=str((S/'INTERFACE-TRACE-v1.json').relative_to(R)),
 all_main_milestones='OPEN',independent_acceptance=False,full_runtime_claim=False,improved_base=0,novelty='OPEN',
 initial_q='k-1',external_zero_guard=True,implicit_rho=False,
 theorem='OrdinaryDispatch.WorkRecursion.ordinaryCallNodes_bound',
 statement='For every proper ordinary pair: ordinaryCallNodes(q,T,S) <= 1024*(leafCount(T)+1)*(233/100)^q.',
 charged='Initial invocation and every ordered source ordinary callback occurrence, including failures, duplicates and same-q common contractions.',
 actual_imported_modules=c['actual_imported_modules'],fresh_producer_modules=c['fresh_producer_modules'],
 fresh_full_body_modules=c['fresh_full_body_modules'],qualified_proof_text_omission_modules=c['qualified_proof_text_omission_modules'],
 stored_declarations=c['stored_occurrences'],axiom_union=c['axiom_union'],body_qualification=c['body_qualification'],
 controls='Known-answer singleton/common/duplicate-failure controls passed. Two corrupt count-one claims rejected mathematically. Initial nonreducing decide attempt rejected as nonmathematical and retained. Guards reused original source controls; no independent credit.',
 retained_resource_failure=str((B/'author-source-audit-v1/certificate.json').relative_to(R)),
 metadata_amendment=c['metadata_amendment'],metadata_amendment_sha256=c['metadata_amendment_sha256'],
 first_missing_statement='Literal Nat local source bill/value correspondence for FastOrdinary.solve initial DepthOne.proper/pretest01 and ordered early evaluation, including refusing/empty-answer paths, with derived polynomial/label caps rather than a desired whole-local work record.',
 remaining=['Complete ordinary nonrecursive source sheet and full recursive source counter, including all local child/check/choice/Rule4/Rule5 work and forest overhead once per actual forest call.',
 'Numeric fresh-label/payload growth and bounded scalar/bit provider correspondence.',
 'Native or IR execution/cost correspondence and external/budget-iteration cost.',
 'Independent reconstruction/refutation/interface review and novelty review.'],
 original_checkpoints=checkpoints,immutable_files=files)
F.write_text(json.dumps(manifest,indent=2)+'\n');F.chmod(0o444)
Q=B/F.name;shutil.copyfile(F,Q);Q.chmod(0o444);assert sha(F)==sha(Q)
print(manifest['status']);print('manifest',str(F.relative_to(R)));print('sha256',sha(F));print('immutable_files',len(files))
