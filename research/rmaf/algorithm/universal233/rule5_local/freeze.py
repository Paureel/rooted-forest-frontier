#!/usr/bin/env python3
"""Seal an immutable OPEN author research release; no acceptance promotion."""
from pathlib import Path
import json,hashlib,datetime
D=Path(__file__).resolve().parent;R=D.parents[4];M=D/'RULE5-LOCAL-MANIFEST-v1.json'
if M.exists():raise SystemExit('FROZEN_NO_WRITE_BOUNDARY')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
latest=json.loads((D/'LATEST-REPLAY-v1.json').read_text());O=R/latest['receipt']
assert sha(O/'certificate.json')==latest['certificate_sha256']
cert=json.loads((O/'certificate.json').read_text());assert cert['status']=='PASS_AUTHOR_KERNEL_OPEN'
for rel,h in cert['input_hashes'].items():assert sha(R/rel)==h,('FINAL_INPUT_CHANGED',rel)
files={p for p in D.glob('*') if p.is_file() and p!=M}
files|={p for p in (D/'source-read').rglob('*') if p.is_file()}
for p in (D/'history').rglob('*'):
 if p.is_file():files.add(p)
dirs=[O]
for name in ['PREPROOF-RECEIPT-v1.json','POST-RECEIPT-v1.json','CLAIMS-CONTROLS-v1.json']:
 dirs.append(R/json.loads((D/name).read_text())['receipt'])
dirs += list((R/'results').glob('algorithm-universal233-rule5-local-*'))
for dr in dirs:files|={p for p in dr.rglob('*') if p.is_file()}
rows=[dict(path=str(p.relative_to(R)),sha256=sha(p),bytes=p.stat().st_size) for p in sorted(files)]
record=dict(version=1,frozen_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
 status='OPEN_RESEARCH_RELEASE',no_further_writes=True,
 no_write_boundary='All immutable_files and this manifest; only new results replay/review paths may be added. Author development helpers that write local sources must not run after freeze.',
 complete_local_rule5=False,all_three_main_milestones='OPEN',full_algorithm=False,smaller_base=False,novelty=False,
 fresh_nonauthor_acceptance=False,canonical_receipt=latest,source_builds=cert['source_builds'],
 stored_producer_occurrences=cert['stored_producer_occurrences'],axiom_union=cert['axiom_union'],
 first_gap='FIRST-GAP-v1.md: admitted guards imply unique-cherry/caterpillar/attachment geometry',
 qualified_source_work='SOURCE-WORK-v1.md; no extracted whole recursive source-work theorem',
 independence='Author sources/evaluators/proofs/controls are DEVELOPMENT. No fresh review or independent certification.',
 excluded_mutable=['build/','empty/failed replay directories'],immutable_files=rows)
M.write_text(json.dumps(record,indent=2)+'\n')
print('FROZEN_OPEN_RESEARCH_RELEASE',len(rows),'immutable files',sha(M))
