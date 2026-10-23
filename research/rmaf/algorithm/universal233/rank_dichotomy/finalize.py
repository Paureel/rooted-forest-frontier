#!/usr/bin/env python3
"""One-shot immutable author checkpoint from already executed receipts."""
from pathlib import Path
import datetime, hashlib, json, os, subprocess
D=Path(__file__).resolve().parent
ROOT=D.parents[4]
REPLAY=Path((D/'LATEST-REPLAY.txt').read_text().strip())
m=json.loads((REPLAY/'certificate.json').read_text())
assert m['status']=='PASS_AUTHOR_SOURCE_BOUND_REPLAY'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for row in m['source_inputs']:
    assert digest(ROOT/row['source'])==row['source_sha256'],row['source']
    assert digest(REPLAY/(row['compiled_module']+'.lean'))==row['compiled_sha256'],row['compiled_module']
OUT=ROOT/'results'/('algorithm-universal233-rank-freeze-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'))
OUT.mkdir()
checks=[]
for name,cmd in [
    ('statement-interface',[str(ROOT/'bootloops-lean'),str(D/'Statements.lean')]),
    ('emitall-selftest',[str(ROOT/'bootloops-check'),'emitall','--par','1']),
    ('lake-version',[str(ROOT/'bootloops-lake'),'--version'])]:
    p=subprocess.run(cmd,cwd=ROOT,env=dict(os.environ,LEAN_PATH=str(REPLAY)),text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=30)
    (OUT/(name+'.log')).write_text(p.stdout)
    checks.append({'name':name,'exit':p.returncode,'log':str((OUT/(name+'.log')).relative_to(ROOT))})
    assert p.returncode==0,p.stdout
pre=Path((D/'CONTROLS-RECEIPT.txt').read_text().strip())
files=[p for p in D.iterdir() if p.is_file() and p.suffix in {'.lean','.py','.md','.json','.txt'} and p.name!='RANK-MANIFEST-v1.json']
files += [p for folder in [REPLAY,pre,OUT] for p in folder.rglob('*') if p.is_file()]
rows=[{'path':str(p.relative_to(ROOT)),'sha256':digest(p),'bytes':p.stat().st_size} for p in sorted(set(files))]
manifest={'version':1,'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'FROZEN_AUTHOR_LEAN_PROVED; independent acceptance pending','all_three_main_algorithm_milestones':'OPEN','independent_acceptance':False,'novelty':'NOT_CLAIMED','scope':'Actual frozen source-generator minimum rank dichotomy, literal unique output, exact color-class membership, infeasible stronger actual cut cost, and literal raw-LIST rational tail mass.','proof_route':'Allowed source coverage + actual dyadic saturation + positive literal entries; coordinator accepted equivalent route; no operational forced-step trace theorem.','canonical_receipt':str((REPLAY/'certificate.json').relative_to(ROOT)),'statement_interface_log':str((OUT/'statement-interface.log').relative_to(ROOT)),'preproof_controls_receipt':str((pre/'receipt.json').relative_to(ROOT)),'positive_source_modules':m['positive_source_modules'],'module_origin_declarations':m['module_origin_declarations'],'axiom_union_observed':m['axiom_union_observed'],'preproof_positive_statements':m['preproof_positive_statements'],'false_propositions_rejected':m['false_propositions_rejected'],'audit_corruption_controls_caught':3,'checks':checks,'first_remaining_condition':'Fresh nonauthor reconstruction/refutation and exact consuming-interface review. Canonical test complexity explained but no new Lean work model.','contact_limitations':m['contact_limitations'],'immutable_files':rows}
(D/'RANK-MANIFEST-v1.json').write_text(json.dumps(manifest,indent=2)+'\n')
for r in rows:assert digest(ROOT/r['path'])==r['sha256'],r['path']
print('PASS frozen author rank checkpoint:',len(rows),'immutable files;',m['positive_source_modules'],'source modules;',m['module_origin_declarations'],'declarations.')
print(D/'RANK-MANIFEST-v1.json')
