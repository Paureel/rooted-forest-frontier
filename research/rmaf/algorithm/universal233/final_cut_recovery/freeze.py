#!/usr/bin/env python3
"""One-shot immutable author checkpoint. Refuses to replace a prior manifest."""
from pathlib import Path
import datetime,hashlib,json
D=Path(__file__).resolve().parent
ROOT=D.parents[4]
MANIFEST=D/'FINAL-CUTS-MANIFEST-v1.json'
assert not MANIFEST.exists(),'Preserve frozen v1; later repairs require v2.'
O=Path((D/'LATEST-REPLAY.txt').read_text().strip())
j=json.loads((O/'certificate.json').read_text())
assert j['status']=='PASS_AUTHOR_SOURCE_BOUND_FINAL_CUT_RECOVERY'
assert j['independent_acceptance'] is False and j['all_three_main_algorithm_milestones']=='OPEN'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert digest(D/'replay.py')==j['runner_sha256']
now=datetime.datetime.now(datetime.timezone.utc)
stamp=now.strftime('%Y%m%dT%H%M%SZ')
result=ROOT/'results'/('algorithm-universal233-final-cuts-'+stamp+'.json')
record={k:j[k] for k in ['status','positive_source_modules','module_origin_declarations','axiom_union_observed','positive_compile_seconds','preproof_positive_statements','postproof_interface_regressions','false_propositions_rejected','missing_audit_record_plant_caught','foreign_private_axiom_plant_caught','source_pin_corruption_plant_caught','source_cost_qualification']}
record.update(created_utc=now.isoformat(),canonical_receipt=str((O/'certificate.json').relative_to(ROOT)),canonical_receipt_sha256=digest(O/'certificate.json'),manifest=str(MANIFEST.relative_to(ROOT)),all_three_main_algorithm_milestones='OPEN',fresh_nonauthor_acceptance='PENDING_COORDINATOR',novelty='NO_CLAIM',first_gap='Fresh nonauthor proof/interface/source-cost acceptance; then complete well-founded solver selection and global recurrence, charging this recovery once.',executable='Guarded actual generate at literal P.length-1 with distinct executable P-block colors, then literal outputs.head?',conclusions=['Original nonredundant valid nonroot distinct cuts','Exact original residual components covering every original/suppressed vertex with no leafless component','Actual block/label permutation to P','Exact original cost P.length-1','Original target/source agreement preserved','Qualified polynomial(n,labelbits)*2^actual_cost final-call source-operation bound'])
result.write_text(json.dumps(record,indent=2)+'\n')
with (D/'RESULT.md').open('a') as f:
 f.write('\nCanonical author receipt: `'+str(O.relative_to(ROOT))+'`. It rebuilt '+str(j['positive_source_modules'])+' exact source modules, audited '+str(j['module_origin_declarations'])+' declarations by full actual module origin, and observed only '+', '.join(j['axiom_union_observed'])+'. All four false propositions were rejected; missing-record, private custom-axiom, and source-pin corruption plants were caught. Positive source compilation took '+str(j['positive_compile_seconds'])+' seconds on this host. The scoped `./bootloops-check emitall --par 1` selftest passed; no unrelated full toolkit suite or external engine was run.\n')
with (D/'WORKFILE.md').open('a') as f:
 f.write('\n## Final author replay and freeze\nThe initial PENDING skeleton above is historical. Canonical receipt: `'+str(O.relative_to(ROOT))+'`. Verbatim replay verdict:\n\n    '+(O/'VERDICT.txt').read_text().strip()+'\n\nExact positive source compilation: '+str(j['positive_compile_seconds'])+' s. Runner self-pin and complete completed rank/core receipt lineage are retained. Full positive sources are rebuilt with only the isolated directory on LEAN_PATH; all private/generated module-origin declarations are audited. All four false propositions and all three audit/pin corruption controls behaved correctly.\n\nThe second replay compiled all positive modules and correctly rejected all three authored false propositions, then stopped at an overly specific diagnostic matcher; that failed receipt and log remain preserved. The matcher correction changed no proposition. Subsequent successful receipts were preserved. The final runner checks its own hash and leaves all owned files untouched whenever the v1 frozen manifest exists, so independent replays create only fresh results evidence.\n\nThe scoped emitall supplied selftest passed; no unrelated toolkit suite, optional external mathematical engine or broad census was run. Author prose pass1 checked meaning/assumptions and pass2 checked register/counts and scope; AUTHOR-SCOPE-CHECK records the author precheck. This does not supply fresh-context referee-sim. Parent coordination must arrange independent proof/interface/source-cost/prose acceptance.\n\nGrade: AUTHOR_LEAN_PROVED / qualified source-operation result, CLOSED-UNVERIFIED. All three main milestones OPEN. FIRST-GAP: fresh nonauthor acceptance, then complete well-founded solver and full recurrence; final recovery must be called once after selection. The v1 manifest fixes the no-write boundary for every listed source, note and evidence file. Later repairs require a new version.\n')
files=[]
for p in sorted(D.rglob('*')):
 if p.is_file() and p!=MANIFEST and p.suffix not in {'.olean','.ilean','.pyc'}:
  files.append(p)
for base in sorted((ROOT/'results').glob('algorithm-universal233-final-cuts-*')):
 if base.is_dir(): files.extend(p for p in sorted(base.rglob('*')) if p.is_file() and p.suffix not in {'.olean','.ilean','.pyc'})
 elif base.is_file(): files.append(base)
files.append(result)
rows=[{'path':str(p.relative_to(ROOT)),'sha256':digest(p),'bytes':p.stat().st_size} for p in sorted(set(files))]
m={'version':1,'created_utc':now.isoformat(),'status':'FROZEN_AUTHOR_FINAL_ORIGINAL_CUT_RECOVERY','all_three_main_algorithm_milestones':'OPEN','independent_acceptance':False,'novelty':'NO_CLAIM','canonical_receipt':str((O/'certificate.json').relative_to(ROOT)),'result':str(result.relative_to(ROOT)),'source_cost_qualification':j['source_cost_qualification'],'first_gap':record['first_gap'],'no_write_boundary':'All listed files are immutable. Derived olean/ilean/pyc files are excluded. Replays after freeze create new results only; repairs require a new version.','immutable_files':rows,'exact_source_import_pins':{r['source']:r['source_sha256'] for r in j['source_inputs']},'dependency_manifests':j['upstream_manifest_checks'],'dependency_receipts':j['dependency_receipts']}
MANIFEST.write_text(json.dumps(m,indent=2)+'\n')
for r in rows:assert digest(ROOT/r['path'])==r['sha256']
print('FROZEN',MANIFEST)
print('RESULT',result)
print('IMMUTABLE_FILES',len(rows))
