# One-shot immutable author package; never chmod or write linked input files.
from pathlib import Path
import datetime,hashlib,json,stat
D=Path(__file__).resolve().parent;R=D.parents[5]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
C=D/'build/author-audit-v8/certificate.json';c=json.loads(C.read_text());assert c['status']=='PASS_AUTHOR_ACTUAL_RULE4_SOURCE_POLYNOMIAL_BOUND'
logical={'Rule4PayloadBound','Rule4SourceBound','Rule4PolynomialCuts','Rule4PolynomialPartition','Rule4BoundInterface'}
for e in c['new_producers']:
 assert sha(R/e['path'])==e['sha256'];assert sha(D/(e['module']+'.lean'))==e['source_sha256'];assert sha(D/'build'/(e['module']+'.olean'))==e['olean_sha256']
 if e['module'] in logical:assert e['all_proof_bodies'] and e['raw_bytes']<64*(1<<20)
assert {e['module'] for e in c['new_producers'] if e['all_proof_bodies']}==logical
assert set(c['axiom_union'])=={'Classical.choice','Quot.sound','propext'}
pins=json.loads((D/'PINNED-PACKAGES-v1.json').read_text())
for n,e in pins.items():
 p=R/e['manifest'];s=p.stat();assert sha(p)==e['sha256'] and s.st_ino==e['inode'] and oct(stat.S_IMODE(s.st_mode))==e['mode'],n
ctx=json.loads((D/'DEPENDENCY-PROVENANCE-v1.json').read_text())
for e in ctx['modules']:
 for k in ['source','object']:
  x=e[k];p=R/x['path'];s=p.stat();assert sha(p)==x['sha256'] and s.st_ino==x['inode'] and oct(stat.S_IMODE(s.st_mode))==x['mode'],(e['module'],k)
  q=D/'build'/p.name;assert q.stat().st_ino==s.st_ino and sha(q)==x['sha256']
report={'version':1,'manifest_pins_preserved':len(pins),'canonical_source_object_pairs_preserved':len(ctx['modules']),'hashes_modes_inodes_preserved':True,'target_sha256':'d1e4e58b44a95eebcbf967d554f44655bc0b11bd99c02ccd4486db606ae1a444'}
T=R/'research/rmaf/monitoring/next-20261016T095230Z/RULE4-BOUND-TARGET-v1.json';assert sha(T)==report['target_sha256']
(D/'PIN-RECHECK-v1.json').write_text(json.dumps(report,indent=2)+'\n')
files=[]
for p in sorted(D.rglob('*')):
 if not p.is_file() or p.name=='FINAL-MANIFEST-v1.json':continue
 s=p.stat()
 if s.st_nlink>1:
  assert not s.st_mode&0o222;continue
 p.chmod(0o444);s=p.stat();files.append({'path':str(p.relative_to(R)),'sha256':sha(p),'bytes':s.st_size,'mode':oct(stat.S_IMODE(s.st_mode)),'inode':s.st_ino})
m={'version':1,'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'FROZEN_AUTHOR_ACTUAL_RULE4_SOURCE_BOUND_REVIEW_PENDING','no_further_writes':True,'target':str(T.relative_to(R)),'target_sha256':sha(T),'own_directory':str(D.relative_to(R)),'canonical_build':str((D/'build').relative_to(R)),'canonical_certificate':str(C.relative_to(R)),'certificate_sha256':sha(C),'source_interface':str((D/'INTERFACE-v1.json').relative_to(R)),'printed_interface':str((D/'PUBLIC-TYPES-v1.txt').relative_to(R)),'result':str((D/'RESULT-v1.md').relative_to(R)),'first_gap':str((D/'FIRST-GAP-v1.json').relative_to(R)),'dependency_provenance':str((D/'DEPENDENCY-PROVENANCE-v1.json').relative_to(R)),'dependency_provenance_sha256':sha(D/'DEPENDENCY-PROVENANCE-v1.json'),'source_context':ctx['single_canonical_context'],'owned_logical_modules':sorted(logical),'actual_imported_modules':c['actual_imported_modules'],'base':'233/100','coefficient':'1560*N^4+312*N^3+614*N^2+586*N+300+48*(2^50*(N+Q+2)^8)','general_theorem':'OrdinaryDispatch.FullSourceWork.rule4Source_bound','cutoff_theorem':'OrdinaryDispatch.FullSourceWork.rule4Source_cutoff_bound','extra_source_cost_premises':[],'body_qualification':'Full actual types, theorem proof text, nonproof bodies, references and axiom closure for all five logical modules. Control module full nonproof bodies and actual proof references/axiom closure with explicit theorem plaintext omission. Imported canonical body qualifications preserved unchanged.','axiom_union':c['axiom_union'],'controls':'Five known-answer source statements passed; three mathematical omissions rejected; clean/hash-corrupt twins distinguished; missing-row/custom-axiom/name-drift copies rejected; compile known/false arithmetic controls retained. Author checks only.','retained_audit_failures':[str((D/'build'/f'author-audit-v{i}'/'certificate.json').relative_to(R)) for i in range(1,8)],'pin_recheck':report,'owned_mathematical_gap':None,'independent_acceptance':False,'full_ordinary_algorithm_233':'OPEN','binary_native_ir':'OPEN','novelty':'OPEN','independent_review_required':True,'immutable_owned_files':files}
p=D/'FINAL-MANIFEST-v1.json';assert not p.exists();p.write_text(json.dumps(m,indent=2)+'\n');p.chmod(0o444)
print('FROZEN',str(p.relative_to(R)),sha(p));print('OWNED_RULE4_SOURCE_BOUND_PROVED_REVIEW_PENDING',len(files),'owned files')
