#!/usr/bin/env python3
"""One-shot immutable author record. Does not claim fresh nonauthor acceptance."""
from pathlib import Path
import hashlib,json,datetime
D=Path(__file__).resolve().parent;R=D.parents[4]
receipt=Path((D/'LATEST-REPLAY.txt').read_text().strip());cert=json.loads((receipt/'certificate.json').read_text())
assert cert['status']=='PASS_AUTHOR_SOURCE_BOUND_REPLAY'
for e in cert['source_inputs']:
 assert hashlib.sha256((R/e['path']).read_bytes()).hexdigest()==e['sha256'],e['path']
rows=[]
for base in [D,receipt]:
 for p in sorted(base.rglob('*')):
  if not p.is_file() or 'build' in p.relative_to(base).parts or '__pycache__' in p.parts or p.suffix in ['.olean','.ilean','.pyc'] or p.name=='OUTPUT-STATE-MANIFEST-v1.json':continue
  rows.append(dict(path=str(p.relative_to(R)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
# Preproof executed logs are retained even though build caches are excluded.
for p in sorted((D/'build').glob('*-preproof.log')):
 rows.append(dict(path=str(p.relative_to(R)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
manifest=dict(version=1,frozen_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='FROZEN_AUTHOR_SCOPED_OUTPUT_STATE; fresh nonauthor acceptance pending',no_further_writes=True,all_three_main_milestones='OPEN',fresh_nonauthor_acceptance=False,full_solver=False,full_runtime=False,novelty_claim=False,canonical_receipt=str((receipt/'certificate.json').relative_to(R)),positive_source_modules=cert['positive_source_modules'],module_origin_declarations=cert['module_origin_declarations'],standard_axioms_observed=cert['standard_axioms_observed'],public_interfaces=['OutputState.sourceForest','OutputState.checked_materialization','OutputState.sourceForest_proper','OutputState.exact_additional_cost','OutputState.agrees_iff_original','OutputState.generated_source_bridge','OutputState.source_permutation','OutputState.cost_permutation','OutputState.opposite_grouping','OutputState.opposite_local_certificates','OutputState.every_opposite_residual_query'],first_gap='Fresh nonauthor acceptance; algorithm: exact reached whole-Bforest child ResidualSolverContract without assuming it.',source_work='Qualified conservative O(n^3) source materialization/selection; no compiled correspondence or recursive runtime theorem.',excluded='build caches except executed preproof logs; olean/ilean/pyc. Manifest excludes itself.',entry_count=len(rows),immutable_files=rows)
p=D/'OUTPUT-STATE-MANIFEST-v1.json';assert not p.exists();p.write_text(json.dumps(manifest,indent=2)+'\n')
for e in rows:assert hashlib.sha256((R/e['path']).read_bytes()).hexdigest()==e['sha256'],e['path']
print('FROZEN',len(rows),'immutable records;',cert['positive_source_modules'],'source modules;',cert['module_origin_declarations'],'module-origin declarations')
print('Manifest',p);print('Manifest SHA256',hashlib.sha256(p.read_bytes()).hexdigest())
