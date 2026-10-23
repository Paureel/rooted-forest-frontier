#!/usr/bin/env python3
"""One-shot author packaging only; scientific sources stay untouched."""
from pathlib import Path
import json,hashlib,datetime,shutil,os
R=Path('/Users/paurel/Documents/ChatGPT/bootscience');D=R/'research/rmaf/algorithm/universal233/rule5_case322'
M=D/'RULE5-CASE322-MANIFEST-v1.json'
if M.exists():raise SystemExit('FROZEN_NO_WRITE_BOUNDARY')
ptr=json.loads((D/'LATEST-REPLAY-v1.json').read_text());O=R/ptr['receipt'];cert=json.loads((O/'certificate.json').read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(O/'certificate.json')==ptr['certificate_sha256']
assert cert['status']=='PASS_AUTHOR_KERNEL_OPEN'
assert cert['source_builds']==85 and cert['controls']['false_math']['rejected']==2
for e in cert['source_entries']:assert sha(R/e['path'])==e['sha256']
for p,h in cert['input_hashes'].items():assert sha(R/p)==h,p
shutil.copyfile('/tmp/case322-final-replay.log',O/'progress.log')
shutil.copyfile(__file__,D/'freeze.py')
files=[p for p in D.rglob('*') if p.is_file() and not any(x in {'build','__pycache__'} for x in p.relative_to(D).parts)]
for parent in sorted((R/'results').glob('algorithm-universal233-rule5-case322-*')):
 files.extend(p for p in parent.rglob('*') if p.is_file())
files=sorted(set(files));rows=[dict(path=str(p.relative_to(R)),sha256=sha(p),bytes=p.stat().st_size) for p in files]
m=dict(version=1,frozen_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='OPEN_LOCAL_GEOMETRY_EXTRACTION',
 no_further_writes=True,no_write_boundary='All listed immutable_files and this manifest. New replay/review receipts belong in new results directories.',
 complete_local_case322=False,complete_rule5=False,global_milestones='ALL_OPEN',full_algorithm=False,improved_base=0,novelty=False,
 independent_acceptance=False,canonical_receipt=ptr,source_builds=cert['source_builds'],stored_producer_occurrences=cert['stored_producer_occurrences'],axiom_union=cert['axiom_union'],
 first_gap='FIRST-GAP-v1.md: literal source path extraction, source sibling normalization, universal currentGuard proofs',
 source_work='SOURCE-WORK-v1.md: source/bit/payload qualifications; final cut recovery remains one-time and separate',
 independence='Author DEVELOPMENT; completed evaluator/audit contacts; incidental broad-search reviewer snippet contact retained in CONTACT-LEDGER-v1.md.',
 preserved_failed_receipt='results/algorithm-universal233-rule5-case322-replay-20261015T132305031180Z',
 excluded_mutable=['build/','__pycache__/'],immutable_files=rows)
M.write_text(json.dumps(m,indent=2)+'\n')
for p in files+[M]:p.chmod(0o444)
print('FROZEN',len(files),'immutable files;',M.relative_to(R));print('MANIFEST_SHA256',sha(M));print('RECEIPT',ptr['receipt']);print('SOURCE_BUILDS',cert['source_builds'],'STORED_OCCURRENCES',cert['stored_producer_occurrences'])
