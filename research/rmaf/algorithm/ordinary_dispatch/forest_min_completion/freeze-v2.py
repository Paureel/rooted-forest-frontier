#!/usr/bin/env python3
"""One-shot packaging of proof-only minimum/ghost completion."""
from pathlib import Path
import json,hashlib,datetime,shutil
R=Path('/Users/paurel/Documents/ChatGPT/bootscience');D=R/'research/rmaf/algorithm/ordinary_dispatch/forest_min_completion'
M=D/'FOREST-MIN-COMPLETION-MANIFEST-v1.json'
if M.exists():raise SystemExit('FROZEN_NO_WRITE_BOUNDARY')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
ptr=json.loads((D/'LATEST-REPLAY-v1.json').read_text());O=R/ptr['receipt'];cert=json.loads((O/'certificate.json').read_text())
assert sha(O/'certificate.json')==ptr['certificate_sha256']
assert cert['status']=='PASS_AUTHOR_KERNEL_PROOF_ONLY'
assert cert['source_builds']==79 and cert['controls']['false_math']['rejected']==4
for e in cert['source_entries']:assert sha(R/e['path'])==e['sha256']
for p,h in cert['input_hashes'].items():assert sha(R/p)==h,p
priors=[]
for rel,h,n in [
 ('research/rmaf/algorithm/universal233/forest_solver/FOREST-SOLVER-MANIFEST-v3.json','89937a6f71bceb2dbeb64917b4b805e8f193fa485b00ec28acecdc95d047dcf5',540),
 ('research/rmaf/algorithm/universal233/rule5_case322_paid_guard/RULE5-CASE322-PAID-GUARD-MANIFEST-v1.json','a1c3805010404da55836b2762b732c48c96132b4038edd074ac3da384a4bc0c1',422)]:
 p=R/rel;assert sha(p)==h
 rows=json.loads(p.read_text())['immutable_files'];assert len(rows)==n
 for e in rows:
  f=R/e['path'];assert sha(f)==e['sha256']
  if 'bytes' in e:assert f.stat().st_size==e['bytes']
 priors.append(dict(manifest=rel,sha256=h,immutable_files_verified=n))
shutil.copyfile('/tmp/forest-min-completion-final-replay.log',O/'progress.log')
files=[p for p in D.rglob('*') if p.is_file() and not any(x in {'build','__pycache__'} for x in p.relative_to(D).parts)]
for parent in sorted((R/'results').glob('algorithm-ordinary-dispatch-forest-min-completion-*')):
 files.extend(p for p in parent.rglob('*') if p.is_file())
files=sorted(set(files));rows=[dict(path=str(p.relative_to(R)),sha256=sha(p),bytes=p.stat().st_size) for p in files]
m=dict(version=1,frozen_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PROVED_MATHEMATICAL_GHOST_EXTENSION_AUTHOR',
 no_further_writes=True,no_write_boundary='All listed immutable_files and this manifest. New review evidence belongs in new paths.',
 minimum_from_actual_original_AF=True,global_IH_from_budget_local_IH=True,all_pairs_low_budget_equality=True,
 improper_pairs_preserved=True,ghost_noncomputable=True,ghost_erased_proof_support_only=True,
 actual_callback_global_IH=False,executable_solver=False,runtime_claim=False,source_work_claim=False,
 global_milestones='ALL_OPEN',improved_base=0,novelty=False,independent_acceptance=False,
 canonical_receipt=ptr,source_builds=cert['source_builds'],stored_producer_occurrences=cert['stored_producer_occurrences'],axiom_union=cert['axiom_union'],
 external_consumer='FIRST-GAP-v1.md: parent owns bounded solve/disjoint/schedule callback congruence; not proved or inspected here.',
 preserved_predecessors=priors,
 independence='AUTHOR DEVELOPMENT. Completed GenericForest v3/dependency sources and author detector consulted. No children or unfinished caller/classifier/reviewer implementations.',
 excluded_mutable=['build/','__pycache__/'],immutable_files=rows)
M.write_text(json.dumps(m,indent=2)+'\n')
for p in files+[M]:p.chmod(0o444)
print('FROZEN',len(files),'immutable files;',M.relative_to(R));print('MANIFEST_SHA256',sha(M));print('RECEIPT',ptr['receipt']);print('SOURCE_BUILDS',cert['source_builds'],'STORED_OCCURRENCES',cert['stored_producer_occurrences'])
