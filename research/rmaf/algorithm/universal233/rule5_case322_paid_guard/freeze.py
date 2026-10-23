#!/usr/bin/env python3
"""Package the audited local proof; no scientific source changes."""
from pathlib import Path
import json,hashlib,datetime,shutil
R=Path('/Users/paurel/Documents/ChatGPT/bootscience');D=R/'research/rmaf/algorithm/universal233/rule5_case322_paid_guard'
M=D/'RULE5-CASE322-PAID-GUARD-MANIFEST-v1.json'
if M.exists():raise SystemExit('FROZEN_NO_WRITE_BOUNDARY')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
ptr=json.loads((D/'LATEST-REPLAY-v1.json').read_text());O=R/ptr['receipt'];cert=json.loads((O/'certificate.json').read_text())
assert sha(O/'certificate.json')==ptr['certificate_sha256']
assert cert['status']=='PASS_AUTHOR_KERNEL_LOCAL_CASE322'
assert cert['source_builds']==106 and cert['controls']['false_math']['rejected']==4
for e in cert['source_entries']:assert sha(R/e['path'])==e['sha256']
for p,h in cert['input_hashes'].items():assert sha(R/p)==h,p
priors=[]
for rel,h,n in [('rule5_case322/RULE5-CASE322-MANIFEST-v1.json','2d5f9c672e7d2a2dc23e7a7c5434200ccd46bcb053188ff51c4954623d164763',647),('rule5_case322_extraction/RULE5-CASE322-EXTRACTION-MANIFEST-v1.json','d99afd406d82e857f4d5035d9ee7a052883c0732769960709a99f171f73029b4',393)]:
 p=D.parent/rel;assert sha(p)==h
 rows=json.loads(p.read_text())['immutable_files'];assert len(rows)==n
 for e in rows:
  f=R/e['path'];assert sha(f)==e['sha256'] and f.stat().st_size==e['bytes']
 priors.append(dict(manifest=str(p.relative_to(R)),sha256=h,immutable_files_verified=n))
shutil.copyfile('/tmp/case322-paid-guard-final-replay.log',O/'progress.log')
files=[p for p in D.rglob('*') if p.is_file() and not any(x in {'build','__pycache__'} for x in p.relative_to(D).parts)]
for parent in sorted((R/'results').glob('algorithm-universal233-rule5-case322-paid-guard-*')):
 files.extend(p for p in parent.rglob('*') if p.is_file())
files=sorted(set(files));rows=[dict(path=str(p.relative_to(R)),sha256=sha(p),bytes=p.stat().st_size) for p in files]
m=dict(version=1,frozen_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PROVED_LOCAL_GUARD_CONDITIONAL_QUERY_AUTHOR',
 no_further_writes=True,no_write_boundary='All listed immutable_files and this manifest. New review evidence belongs in new results paths.',
 original_AF_plan_cover=True,universal_paid_current_guards=True,arbitrary_source_sibling_order=True,operational_role_transport=True,
 complete_local_case322_at_displayed_geometry=True,global_admission_extraction=False,complete_rule5=False,
 global_milestones='ALL_OPEN',full_algorithm=False,improved_base=0,novelty=False,independent_acceptance=False,
 canonical_receipt=ptr,source_builds=cert['source_builds'],stored_producer_occurrences=cert['stored_producer_occurrences'],axiom_union=cert['axiom_union'],
 conditional_consumer='PaidCaller.guardedQuery_spec retains explicit recursive child-query correctness IH.',
 first_external_gap='FIRST-GAP-v1.md: global selector to actual LiteralGeometry; whole recursive solver and source-work model remain outside scope.',
 preserved_predecessors=priors,
 source_work='SOURCE-WORK-v1.md: source/bit/payload correspondence qualifications; final original cut recovery one-time and separate',
 independence='AUTHOR DEVELOPMENT; completed inputs and detector consulted. No unfinished classifier/common-source/reviewer implementation read. No children.',
 excluded_mutable=['build/','__pycache__/'],immutable_files=rows)
M.write_text(json.dumps(m,indent=2)+'\n')
for p in files+[M]:p.chmod(0o444)
print('FROZEN',len(files),'immutable files;',M.relative_to(R));print('MANIFEST_SHA256',sha(M));print('RECEIPT',ptr['receipt']);print('SOURCE_BUILDS',cert['source_builds'],'STORED_OCCURRENCES',cert['stored_producer_occurrences'])
