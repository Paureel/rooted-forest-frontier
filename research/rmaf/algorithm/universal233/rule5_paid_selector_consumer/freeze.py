#!/usr/bin/env python3
"""Problem-specific immutable author paid-selector freeze."""
from pathlib import Path
import datetime,hashlib,json,shutil
D=Path(__file__).resolve().parent;R=D.parents[4]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def pin(p,h):assert sha(p)==h,(p,h,sha(p))
assert shutil.disk_usage(D).free>=3*1024**3,'DISK_FLOOR_3GIB'
latest=json.loads((D/'LATEST-REPLAY-v1.json').read_text());O=R/latest['receipt'];pin(O/'certificate.json',latest['certificate_sha256'])
c=json.loads((O/'certificate.json').read_text());assert c['status']=='PASS_AUTHOR_KERNEL_SOURCE_PRODUCER'
for e in c['source_entries']:pin(R/e['path'],e['sha256']);pin(O/(e['module']+'.lean'),e['adapted_sha256'])
for p,h in c['input_hashes'].items():pin(R/p,h)
for dep in c['dependency_manifests']:
 M=R/dep['path'];pin(M,dep['sha256'])
 for e in json.loads(M.read_text())['immutable_files']:pin(R/e['path'],e['sha256'])
for n in ['README.md','SOURCE-WORK-v1.md','INTERFACE-v1.md','RESULT-v1.md','FIRST-OPEN-v1.md','WORKFILE-FINAL-v1.md','CONTACT-LEDGER-FINAL-v1.md']:
 (O/n).write_bytes((D/n).read_bytes())
files=[p for p in D.iterdir() if p.is_file() and p.name not in ['LATEST-REPLAY-v1.json'] and p.suffix in ['.lean','.py','.md','.json']]
receipts=sorted(R.glob('results/algorithm-universal233-rule5-paid-selector-*'))
for p in receipts:
 if p.is_dir():files += [f for f in p.iterdir() if f.is_file()]
rows=[dict(path=str(p.relative_to(R)),sha256=sha(p),bytes=p.stat().st_size) for p in sorted(set(files))]
m=dict(version=1,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='FROZEN_AUTHOR_ACTUAL_SECOND_PAID_SELECTOR_REVIEW_PENDING',
 no_further_writes=True,no_write_boundary='This manifest and immutable_files; continuation requires new paths.',all_three_main_milestones='OPEN',
 independent_acceptance=False,improved_base=0,novelty=False,q='k-1',implicit_rho=False,canonical_receipt=str(O.relative_to(R)),certificate_sha256=sha(O/'certificate.json'),
 source_modules=c['source_builds'],own_modules=len(c['own_modules']),stored_producer_occurrences=c['stored_producer_occurrences'],
 own_producer_occurrences=sum(e['occurrences'] for e in c['producer_audits'] if e['module'] in c['own_modules']),axiom_union=c['axiom_union'],
 interfaces=c['interfaces'],controls=c['controls'],body_qualification=c['body_qualification'],dependency_manifests=c['dependency_manifests'],
 first_unprovided_call='solve (some Q.target) Q.sources Q.residual, exact at each actual emitted residual budget; parent generic callback binding remains explicit.',
 source_work='rows_linear_bound proves16 rows/source vertex; source primitive/bit/payload qualifications explicit, no full instruction or compiled machine bill.',
 excluded_mutable=['build source/olean copies','LATEST-REPLAY-v1.json','Python __pycache__'],immutable_files=rows)
F=D/'FINAL-MANIFEST-v1.json';assert not F.exists(),'REFUSE_REPLACE_FROZEN_MANIFEST';F.write_text(json.dumps(m,indent=2)+'\n')
for e in rows:pin(R/e['path'],e['sha256'])
print('PASS_IMMUTABLE_AUTHOR_FREEZE',len(rows),sha(F),O)
