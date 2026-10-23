#!/usr/bin/env python3
"""Immutable author prefix release; no full Rule5 acceptance promotion."""
from pathlib import Path
import json,hashlib,datetime
D=Path(__file__).resolve().parent;R=D.parents[4];M=D/'CLASSIFICATION-MANIFEST-v1.json'
if M.exists():raise SystemExit('FROZEN_NO_WRITE_BOUNDARY')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
latest=json.loads((D/'LATEST-REPLAY-v1.json').read_text());O=R/latest['receipt']
assert sha(O/'certificate.json')==latest['certificate_sha256']
cert=json.loads((O/'certificate.json').read_text());assert cert['status']=='PASS_AUTHOR_KERNEL_OPEN'
for p,h in cert['input_hashes'].items():assert sha(R/p)==h,('INPUT_CHANGED_AFTER_REPLAY',p)
old=D.parent/'rule5_local/RULE5-LOCAL-MANIFEST-v1.json'
assert sha(old)=='411981d5b35caf6b79b576247baa99af4bd5ae2da8d1884c084a0dfb7a9d2386'
for e in json.loads(old.read_text())['immutable_files']:assert sha(R/e['path'])==e['sha256']
files={p for p in D.iterdir() if p.is_file() and p!=M}
files|={p for p in (D/'build').glob('*.log') if p.is_file()}
for dr in sorted((R/'results').glob('algorithm-universal233-rule5-classification-*')):
 files|={p for p in dr.rglob('*') if p.is_file()}
rows=[dict(path=str(p.relative_to(R)),sha256=sha(p),bytes=p.stat().st_size) for p in sorted(files)]
rec=dict(version=1,frozen_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='OPEN_AUTHOR_PREFIX_RELEASE',
 no_further_writes=True,no_write_boundary='This manifest and all immutable_files. Continuation/reviews require new paths; development/replay helpers must not write these files after freeze.',
 complete_local_rule5=False,all_three_main_milestones='OPEN',full_algorithm=False,smaller_base=False,novelty=False,
 fresh_nonauthor_acceptance=False,canonical_receipt=latest,source_builds=cert['source_builds'],
 stored_producer_occurrences=cert['stored_producer_occurrences'],axiom_union=cert['axiom_union'],
 completed_author_scope=cert['completed_author_scope'],first_gap=cert['first_gap'],
 original_manifest_preserved=dict(path=str(old.relative_to(R)),sha256=sha(old),files=len(json.loads(old.read_text())['immutable_files'])),
 independence='All author proof/control/evaluator contacts DEVELOPMENT. Fresh semantic/interface/prose review required.',
 excluded_mutable=['build source copies and oleans; retained build logs are immutable','Python __pycache__'],immutable_files=rows)
M.write_text(json.dumps(rec,indent=2)+'\n')
for row in rows:(R/row['path']).chmod(0o444)
M.chmod(0o444)
print('FROZEN_OPEN_AUTHOR_PREFIX_RELEASE',len(rows),'files',sha(M))
