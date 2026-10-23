#!/usr/bin/env python3
"""Freeze this one-task author receipt; does not grant independent acceptance."""
from pathlib import Path
import hashlib,json,datetime
D=Path(__file__).resolve().parent;R=D.parents[4]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
out=Path((D/'LATEST-REPLAY.txt').read_text().strip());c=json.loads((out/'certificate.json').read_text())
assert c['status']=='PASS_AUTHOR_SOURCE_BOUND_REPLAY'
for e in c['source_inputs']:
 assert sha(R/e['path'])==e['sha256']
 assert sha(out/(e['module']+'.lean'))==e['adapted_sha256']
for p,h in c['input_hashes'].items():assert sha(R/p)==h
files=[]
for p in sorted(D.iterdir()):
 if p.is_file() and p.suffix in ['.lean','.py','.md','.json','.log','.txt'] and not p.name.startswith(('FOREST-SOLVER-MANIFEST','freeze')) and p.name!='LATEST-REPLAY.txt':
  files.append(p)
files+=sorted(p for p in out.iterdir() if p.is_file())
rows=[dict(path=str(p.relative_to(R)),sha256=sha(p)) for p in files]
rows.append(dict(path=str((D/'freeze.py').relative_to(R)),sha256=sha(D/'freeze.py')))
prior=D/'FOREST-SOLVER-MANIFEST-v2.json'
record=dict(version=3,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),scope='Actual generic ForestState solver, exact-minimum conditional only on OrdinaryIH; qualified source bill recurrence under LocalBillBound.',status='AUTHOR_KERNEL_CHECKED_PENDING_FRESH_REVIEW',all_three_main_milestones='OPEN',independent_acceptance=False,ordinary_only_conditional_exact=True,unconditional_local_cost_coefficient=False,compiled_machine_semantics=False,amends=dict(path=str(prior.relative_to(R)),sha256=sha(prior),reason='Exclude mutable LATEST-REPLAY pointer; fixed canonical receipt path retained; v1 and v2 preserved.'),canonical_receipt=str(out.relative_to(R)),source_modules=c['positive_source_modules'],module_origin_declarations=c['module_origin_declarations'],local_authored_modules=c['local_authored_modules'],local_declarations=c['local_declarations'],standard_axioms=c['standard_axioms_observed'],controls=c['controls'],immutable_files=rows)
p=D/'FOREST-SOLVER-MANIFEST-v3.json';p.write_text(json.dumps(record,indent=2)+'\n')
(D/'FOREST-SOLVER-MANIFEST-v3.sha256').write_text(sha(p)+'  '+p.name+'\n')
print('FROZEN AUTHOR',record['source_modules'],'modules;',record['module_origin_declarations'],'declarations;',len(rows),'immutable files; all main milestones OPEN')
