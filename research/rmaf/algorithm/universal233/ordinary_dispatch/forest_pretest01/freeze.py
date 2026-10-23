#!/usr/bin/env python3
"""Problem-specific immutable author freeze; never mutates prior sources."""
from pathlib import Path
import datetime,hashlib,json
D=Path(__file__).resolve().parent;R=D.parents[5]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def pin(p,h):assert sha(p)==h,(p,h,sha(p))
latest=json.loads((D/'LATEST-REPLAY-v1.json').read_text());O=R/latest['receipt'];pin(O/'certificate.json',latest['certificate_sha256'])
c=json.loads((O/'certificate.json').read_text());assert c['status']=='PASS_AUTHOR_KERNEL_SOURCE_PRODUCER'
for e in c['source_entries']:pin(R/e['path'],e['sha256']);pin(O/(e['module']+'.lean'),e['adapted_sha256'])
for p,h in c['input_hashes'].items():pin(R/p,h)
M=R/'research/rmaf/algorithm/universal233/forest_solver/FOREST-SOLVER-MANIFEST-v3.json';pin(M,c['frozen_manifest_sha256'])
for e in json.loads(M.read_text())['immutable_files']:pin(R/e['path'],e['sha256'])
for n in ['SOURCE-WORK-v1.md','README.md','INTERFACE-v1.md','RESULT-v1.md','CONTACT-LEDGER-RESUME-v1.md','WORKFILE-RESUME-v1.md','FIRST-OPEN-v1.md']:
 (O/n).write_bytes((D/n).read_bytes())
files=[p for p in D.iterdir() if p.is_file() and p.suffix in ['.lean','.py','.md']]
receipts=sorted(R.glob('results/algorithm-universal233-forest-pretest01-pilot-*'))+[O]
for p in receipts:files += [f for f in p.iterdir() if f.is_file()]
rows=[dict(path=str(p.relative_to(R)),sha256=sha(p),bytes=p.stat().st_size) for p in sorted(set(files))]
manifest=dict(version=1,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
 status='AUTHOR_KERNEL_SOURCE_PRODUCER_CHECKED_PENDING_FRESH_REVIEW',all_three_main_milestones='OPEN',
 novelty=False,improved_base=0,independent_acceptance=False,q='k-1',implicit_rho=False,
 canonical_receipt=str(O.relative_to(R)),certificate_sha256=sha(O/'certificate.json'),
 source_modules=c['source_builds'],own_modules=len(c['own_modules']),stored_producer_occurrences=c['stored_producer_occurrences'],
 own_producer_occurrences=sum(e['occurrences'] for e in c['producer_audits'] if e['module'] in c['own_modules']),
 axiom_union=c['axiom_union'],controls=c['controls'],source_work='Exact candidate count plus explicit primitive/bit/payload qualifications; no formal complete instruction or compiled-machine bill.',
 completed_dependency_manifest=dict(path=str(M.relative_to(R)),sha256=sha(M),immutable_files_verified=len(json.loads(M.read_text())['immutable_files'])),
 preserved_development_receipts=[str(p.relative_to(R)) for p in receipts[:-1]],immutable_files=rows)
F=D/'FOREST-PRETEST01-MANIFEST-v1.json';assert not F.exists(),'REFUSE_REPLACE_FROZEN_MANIFEST'
F.write_text(json.dumps(manifest,indent=2)+'\n')
for e in rows:pin(R/e['path'],e['sha256'])
print('PASS_IMMUTABLE_AUTHOR_FREEZE',len(rows),sha(F),O)
