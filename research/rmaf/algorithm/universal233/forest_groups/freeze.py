#!/usr/bin/env python3
"""One-shot author no-write manifest. Does not modify any frozen input."""
from pathlib import Path
import datetime,hashlib,json
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[4]
manifest=HERE/'FOREST-GROUPS-MANIFEST-v1.json'
assert not manifest.exists(),'freeze already exists'
OUT=Path((HERE/'LATEST-REPLAY.txt').read_text().strip())
c=json.loads((OUT/'certificate.json').read_text())
assert c['status']=='PASS_AUTHOR_KERNEL_REPLAY'
assert c['all_three_main_milestones']=='OPEN' and not c['fresh_nonauthor_acceptance']
for rel,sha in c['input_hashes'].items():
 assert hashlib.sha256((ROOT/rel).read_bytes()).hexdigest()==sha,rel
paths=[]
for p in HERE.rglob('*'):
 if p.is_file() and 'build' not in p.relative_to(HERE).parts and '__pycache__' not in p.parts and p.name not in ['FOREST-GROUPS-MANIFEST-v1.json','FOREST-GROUPS-MANIFEST-v1.sha256']:
  paths.append(p)
receipts=sorted((ROOT/'results').glob('algorithm-universal233-forest-groups-*'))
for directory in receipts:
 assert directory.is_dir()
 paths += [p for p in directory.rglob('*') if p.is_file()]
rows=[dict(path=str(p.relative_to(ROOT)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size) for p in sorted(set(paths))]
d=dict(version=1,frozen_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='FROZEN_AUTHOR_CLOSED_UNVERIFIED',
 scope='Literal actual ForestState grouped decomposition/reconstruction, exact cost and retained A paid1 plus arbitrary residual Bforest; child-specific conditional q-1 query.',
 no_further_writes=True,all_three_main_milestones='OPEN',full_algorithm_proved=False,novelty='NOT_CLAIMED',
 fresh_nonauthor_review='PENDING_ROOT_COORDINATED',canonical_receipt=str((OUT/'certificate.json').relative_to(ROOT)),
 source_modules=c['source_modules'],module_origin_declarations=c['module_origin_total'],axiom_union_observed=c['axiom_union_observed'],
 first_unproved_consumer='FIRST-GAP.md: establish the exact child-specific ResidualSolverContract in a well-founded complete solver; original full source-cut reconstruction remains separate.',
 no_write_boundary='Every immutable_files entry and this manifest/seal are frozen. build/ is excluded mutable development output. New replay receipt directories are permitted; replay does not rewrite LATEST-REPLAY after freeze.',
 preserved_receipt_directories=[str(p.relative_to(ROOT)) for p in receipts],immutable_files=rows)
manifest.write_text(json.dumps(d,indent=2)+'\n')
seal=hashlib.sha256(manifest.read_bytes()).hexdigest()
(HERE/'FOREST-GROUPS-MANIFEST-v1.sha256').write_text(seal+'  '+str(manifest.relative_to(ROOT))+'\n')
print(json.dumps(dict(manifest=str(manifest.relative_to(ROOT)),sha256=seal,immutable_files=len(rows),canonical_receipt=d['canonical_receipt'],status=d['status'],all_three_main_milestones='OPEN'),indent=2))
