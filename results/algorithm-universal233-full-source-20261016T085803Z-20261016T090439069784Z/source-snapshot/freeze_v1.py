# One-shot readonly consumer-stage seal. Original writable development modes
# and all prior sealed packages remain unchanged; snapshot new source instead.
from pathlib import Path
import datetime,gzip,hashlib,json,re,shutil
D=Path(__file__).resolve().parent;R=D.parents[5]
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1<<20),b''):h.update(b)
 return h.hexdigest()
T=R/'research/rmaf/monitoring/global-next-20261016T085803Z/GLOBAL-SOURCE-TARGET-v2.json'
assert sha(T)=='1b20034e34b9e6902572af6273abdcccf121dd09f6257362e88b2c8c9a160db9';target=json.loads(T.read_text())
B=R/json.loads((D/'BUILD-v1.json').read_text())['directory'];O=B/'author-audit-v3';C=O/'certificate.json';c=json.loads(C.read_text())
assert c['status']=='PASS_AUTHOR_PREFIX_WEIGHTED_COMMON_AGREEMENT_SOURCE_STAGE'
assert c['full_proof_body_modules']==6 and len(c['version_compatibility'])==10
assert c['axiom_union']==['Classical.choice','Quot.sound','propext']
for p,h in c['inputs'].items():assert sha(R/p)==h
for e in c['sources']:
 assert sha(B/(e['module']+'.lean'))==e['source_sha256'] and sha(B/(e['module']+'.olean'))==e['olean_sha256']
for k in ['call_count','early','rule5_classifier','rule5common','checker']:
 e=target['allowed_packages'][k];assert sha(R/e['manifest'])==e['sha256']
names={'agreementMeter_value','agreementMeter_bound','measuredAgreement_K','agreement_domain_envelope',
 'common_real_pick_work_closed_checker','reconstruct_actual_agreement','common_candidate_agreement_envelope',
 'budgetTreeWork_eq','budgetTreeWork_bound','prefixTreeWork_eq','prefixTreeWork_bound','prefixTreeMeter_value',
 'commonPairMeter_value','commonPairMeter_bound','expandCommonMeter_value','expandCommonMeter_bound',
 'commonBranchMeter_value','commonBranchMeter_work_split','commonBranchMeter_local_bound'}
interfaces=[]
for e in c['new_producers']:
 if not e['full_proof_bodies']:continue
 p=R/e['path'];assert sha(p)==e['sha256']
 with gzip.open(p,'rt') as f:rows=json.load(f)
 for r in rows:
  short=r['actual_name'].split('.')[-1]
  if short in names:
   assert r['has_body'] and r['body_text_scope']=='FULL_ALL_BODY' and r['body']!='<none>'
   source=B/(e['module']+'.lean');match=re.search(r'^.*theorem '+re.escape(short)+r'\b',source.read_text(),re.M);assert match
   interfaces.append(dict(name=r['actual_name'],module=e['module'],source=str(source.relative_to(R)),line=source.read_text()[:match.start()].count('\n')+1,
    type_sha256=hashlib.sha256(r['type'].encode()).hexdigest(),body_sha256=hashlib.sha256(r['body'].encode()).hexdigest(),body_bytes=len(r['body']),axioms=r['axiom_references'],record=e['path'],record_sha256=e['sha256']))
assert {e['name'].split('.')[-1] for e in interfaces}==names
(D/'INTERFACE-TRACE-v1.json').write_text(json.dumps(dict(version=1,status='AUTHOR_SCOPED_SOURCE_INTERFACES_REVIEW_PENDING',canonical_certificate=str(C.relative_to(R)),certificate_sha256=sha(C),interfaces=interfaces,
 boundary='Nat prefix recursive subtotal plus full common local bill and concrete general agreement K consumer; weighted ordinary budget reservoir is not yet a complete actual forest-debit source counter.',full_runtime_claim=False,independent_acceptance=False),indent=2)+'\n')
gap=dict(version=1,first_unprovided_source_statement='Literal child-building/caller source bill at FastOrdinary.solve .one: pendantChild -> makeChild -> sourceForest/restrict filterMap; the shared selected Rule5 builders are separately owned and were not read unfinished.',
 required_value_interface='Meter value equals the unchanged actual builder; bills every restriction/filterMap and label/partition copy, including empty/refused cases; derived payload/source caps.',
 still_owned_caller_assembly='Actual affordable childAnswers traversal, original ordinaryAccepted agreement/budget checking, best List.length; Rule4 and full hard2 local assembly.',
 global_induction='Build the complete Nat source subtotal with each actual forest local debit exactly once, then use its Nat-to-Rat split and budgetTreeWork weighted envelope. Do not multiply a worst exponential overhead by the total unweighted call count.',
 other_open=['Complete selected Rule5 execution source sheet','Numeric growth in every ordinary branch and bounded scalar/bit provider','Native/IR and external recovery/budget iteration','Independent acceptance and novelty'],no_full_runtime_acceptance=True)
(D/'FIRST-GAP-v1.json').write_text(json.dumps(gap,indent=2)+'\n')
roots=sorted((R/'results').glob('algorithm-universal233-full-source-20261016T085803Z-*'));assert B in roots
failure_roots=[str(p.relative_to(R)) for p in roots if p!=B]
(D/'SETUP-FAILURES-v1.json').write_text(json.dumps(dict(version=1,roots=failure_roots,preserved=True,
 attempts=[dict(script='setup_v1.py',error='AssertionError: ActualInspection; allowed checker-root dependency fallback absent'),dict(script='setup_v2.py',error='UNSEALED_SOURCE ClosedPayload.lean; readonly snapshots required instead of hardlinking pinned writable originals')],resolution='setup_v3.py verifies manifest pins and creates new readonly copies of pinned writable originals. Failed seed records remain unchanged.'),indent=2)+'\n')
assert shutil.disk_usage(R).free>=3*(1<<30)
S=B/'source-snapshot';assert not S.exists();S.mkdir()
originals=[]
for p in sorted(D.iterdir()):
 if not p.is_file() or p.name=='FINAL-MANIFEST-v1.json':continue
 s=p.stat();q=S/p.name;shutil.copyfile(p,q);assert sha(p)==sha(q);q.chmod(0o444)
 originals.append(dict(path=str(p.relative_to(R)),sha256=sha(p),mode=oct(s.st_mode&0o777),inode=s.st_ino,snapshot=str(q.relative_to(R))))
shutil.copyfile(T,S/'GLOBAL-SOURCE-TARGET-v2.json');(S/'GLOBAL-SOURCE-TARGET-v2.json').chmod(0o444)
files=[]
for root in roots:
 for p in sorted(root.rglob('*')):
  if not p.is_file():continue
  s=p.stat()
  if s.st_nlink>1:assert not s.st_mode&0o222
  else:p.chmod(s.st_mode&0o555)
  files.append(dict(path=str(p.relative_to(R)),sha256=sha(p),bytes=p.stat().st_size,mode=oct(p.stat().st_mode&0o777)))
for e in files:assert sha(R/e['path'])==e['sha256'] and not (R/e['path']).stat().st_mode&0o222
m=dict(version=1,created_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='FROZEN_AUTHOR_PREFIX_WEIGHTED_COMMON_AGREEMENT_SOURCE_STAGE_REVIEW_PENDING',no_further_writes=True,
 target=str(T.relative_to(R)),target_sha256=sha(T),canonical_build=str(B.relative_to(R)),canonical_certificate=str(C.relative_to(R)),certificate_sha256=sha(C),source_snapshot=str(S.relative_to(R)),
 result=str((S/'RESULT-v1.md').relative_to(R)),interfaces=str((S/'INTERFACE-TRACE-v1.json').relative_to(R)),first_gap=str((S/'FIRST-GAP-v1.json').relative_to(R)),
 all_main_milestones='OPEN',full_ordinary_source_counter='OPEN',full_recursive_source_bit_payload='OPEN',native_or_ir='OPEN',independent_acceptance=False,improved_base=0,novelty='OPEN',initial_q='k-1',implicit_rho=False,
 attained=['Actual Nat prefix subtotal on the complete literal ordinary query tree, exact value and universal polynomial*(233/100)^q bound for arbitrary current q.',
 'Correct sum-of-(233/100)^residual-budget reservoir with universal 1024*(n+1)*(233/100)^q bound; actual full forest-debit assembly remains open.',
 'Literal common freshness/contraction/guard/callback/expansion value/work split; local actual bill <=256*(2n+1)^2.',
 'General RMAF.agreement full-scan unit-source value/K bridge; actual common candidates at cells<=12n+1 and labels<2^(L+2); frozen common checker premise discharged.'],
 actual_imported_modules=c['actual_imported_modules'],fresh_producer_modules=c['fresh_producer_modules'],full_proof_body_modules=c['full_proof_body_modules'],stored_declarations=c['stored_declarations'],axiom_union=c['axiom_union'],
 version_compatibility=dict(modules=len(c['version_compatibility']),decision='Exact source/type/nonproof-body comparisons in original contexts; complete datatype/constructor/recursor metadata bridge where required.',evidence=c['version_compatibility']),
 body_qualification='Full exact Expr repr for all six new proof modules. Remaining new and inherited qualified producer records retain full nonproof bodies and actual proof references/axiom closure, with explicit theorem-proof-text omission.',
 controls='Known-answer general agreement, common construction/expansion/failure charge, singleton prefix and weighted q=0/q=1 fixtures passed. Both corrupt claims rejected mathematically. Original compiler/resource controls reused; no independent credit.',
 retained_audit_failures=[str((B/'author-audit-v1/certificate.json').relative_to(R)),str((B/'author-audit-v2/certificate.json').relative_to(R))],retained_setup_failures=failure_roots,
 first_unprovided_source_statement=gap['first_unprovided_source_statement'],remaining=gap,
 original_development_sources=originals,no_write_boundary='Manifest and exact copy plus immutable_files. Original development modes/inodes are preserved through readonly exact snapshots.',immutable_files=files)
F=D/'FINAL-MANIFEST-v1.json';assert not F.exists();F.write_text(json.dumps(m,indent=2)+'\n');F.chmod(0o444);Q=B/F.name;shutil.copyfile(F,Q);Q.chmod(0o444)
print(m['status']);print('manifest',str(F.relative_to(R)));print('sha256',sha(F));print('immutable_files',len(files));print('interfaces',len(interfaces))
