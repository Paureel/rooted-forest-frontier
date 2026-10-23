#!/usr/bin/env python3
"""One-shot packaging of the author OPEN guard release; no proof edits."""
from pathlib import Path
import json,hashlib,datetime,shutil
R=Path('/Users/paurel/Documents/ChatGPT/bootscience');D=R/'research/rmaf/algorithm/universal233/rule5_case322_extraction'
M=D/'RULE5-CASE322-EXTRACTION-MANIFEST-v1.json'
if M.exists():raise SystemExit('FROZEN_NO_WRITE_BOUNDARY')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
ptr=json.loads((D/'LATEST-REPLAY-v1.json').read_text());O=R/ptr['receipt'];cert=json.loads((O/'certificate.json').read_text())
assert sha(O/'certificate.json')==ptr['certificate_sha256']
assert cert['status']=='PASS_AUTHOR_KERNEL_OPEN'
assert cert['source_builds']==99 and cert['controls']['false_math']['rejected']==3
for e in cert['source_entries']:assert sha(R/e['path'])==e['sha256']
for p,h in cert['input_hashes'].items():assert sha(R/p)==h,p
prior=R/'research/rmaf/algorithm/universal233/rule5_case322/RULE5-CASE322-MANIFEST-v1.json'
assert sha(prior)=='2d5f9c672e7d2a2dc23e7a7c5434200ccd46bcb053188ff51c4954623d164763'
for e in json.loads(prior.read_text())['immutable_files']:
 p=R/e['path'];assert sha(p)==e['sha256'] and p.stat().st_size==e['bytes']
shutil.copyfile('/tmp/case322-extraction-final-replay.log',O/'progress.log')
shutil.copyfile(__file__,D/'freeze.py')
files=[p for p in D.rglob('*') if p.is_file() and not any(x in {'build','__pycache__'} for x in p.relative_to(D).parts)]
for parent in sorted((R/'results').glob('algorithm-universal233-rule5-case322-extraction-*')):
 files.extend(p for p in parent.rglob('*') if p.is_file())
files=sorted(set(files));rows=[dict(path=str(p.relative_to(R)),sha256=sha(p),bytes=p.stat().st_size) for p in files]
m=dict(version=1,frozen_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='OPEN_UNIVERSAL_PAID_CURRENT_GUARD',
 no_further_writes=True,no_write_boundary='All listed immutable_files and this manifest. New replay/review evidence belongs in new results paths.',
 original_AF_plan_cover=True,arbitrary_source_sibling_order=True,operational_role_transport=True,
 complete_local_case322=False,complete_rule5=False,global_milestones='ALL_OPEN',full_algorithm=False,improved_base=0,novelty=False,independent_acceptance=False,
 canonical_receipt=ptr,source_builds=cert['source_builds'],stored_producer_occurrences=cert['stored_producer_occurrences'],axiom_union=cert['axiom_union'],
 first_gap='CURRENT-GUARD-TARGET-v1.lean.txt / FIRST-GAP-v1.md: universal nonredundancy, source partition binding and nonroot fallback from exact X-hull frontier',
 preserved_predecessor=dict(manifest=str(prior.relative_to(R)),sha256=sha(prior),immutable_files_verified=647),
 source_work='SOURCE-WORK-v1.md: explicit source/bit/payload qualifications; final original cut recovery remains one-time and separate',
 independence='Author DEVELOPMENT; completed evaluator/theorem/detector contacts; no unfinished classifier/common-split/reviewer source read, no children.',
 excluded_mutable=['build/','__pycache__/'],immutable_files=rows)
M.write_text(json.dumps(m,indent=2)+'\n')
for p in files+[M]:p.chmod(0o444)
print('FROZEN',len(files),'immutable files;',M.relative_to(R));print('MANIFEST_SHA256',sha(M));print('RECEIPT',ptr['receipt']);print('SOURCE_BUILDS',cert['source_builds'],'STORED_OCCURRENCES',cert['stored_producer_occurrences'])
