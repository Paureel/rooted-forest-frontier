#!/usr/bin/env python3
"""One-shot immutable pre-candidate ledger-readiness snapshot."""
from datetime import datetime,timezone
import hashlib
import json
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[4];OUT=ROOT/'research/rmaf/results'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
freeze=json.loads((HERE/'PRE-CANDIDATE-FREEZE.json').read_text())
for name,h in freeze['files_sha256'].items():assert sha(ROOT/name)==h,name
old=ROOT/'research/rmaf/algorithm/verification/integration-2026-10-15/ARTIFACTS.json'
assert sha(old)=='4cbbba186a546ac48e5f27736b7a537a5d83d3b0bec40a2156b15d80040b1c65'
receipts=[]
for phase in ['pilot','size-pilot','controls']:
 p=OUT/f'algorithm-core-work-fresh-review-{phase}-v1.json'
 r=json.loads(p.read_text());assert r['all_passed']
 assert r['source_sha256']==sha(HERE/'work_ledger.py')
 assert r['controls_sha256']==sha(HERE/'CONTROL-PIN.json')
 assert r['freeze_sha256']==sha(HERE/'PRE-CANDIDATE-FREEZE.json')
 receipts.append({'path':str(p.relative_to(ROOT)),'sha256':sha(p),
                  'log_sha256':sha(p.with_suffix('.log'))})
full=json.loads((OUT/'algorithm-core-work-fresh-review-controls-v1.json').read_text())
assert full['declared_controls']==full['completed']==full['clean_passed']==29
assert full['plants_declared']==full['plants_caught']==61
by_id={r['id']:r for r in full['rows']}
assert by_id['combine-left-output-length-eight']['report']['counts']['append.receipt_outputs.left_cells']==8
assert by_id['combine-left-output-length-sixteen']['report']['counts']['append.receipt_outputs.left_cells']==16
assert by_id['run-zero-budget-local-work']['report']['counts']['normalize.visit']==3
assert by_id['generate-zero-budget-initial-check-and-colors']['report']['counts']['initial.nodup_calls']==1
assert by_id['generate-zero-budget-initial-check-and-colors']['report']['counts']['oracle.color_calls']==2
assert all(p['caught'] for row in full['rows'] for p in row['plants'])
same_value=sum(p['value_unchanged'] for row in full['rows'] for p in row['plants'])
kernel=json.loads((HERE/'KERNEL-GATES.json').read_text())
assert kernel['execution_status']=='UNEXECUTED-until-root-release'
receipt={'created_utc':datetime.now(timezone.utc).isoformat(),
         'status':'READY-TO-RECEIVE-FROZEN-CORE-WORK-CANDIDATE',
         'scope':'finite structural work-ledger readiness only; no source-work theorem or machine-time acceptance',
         'clean_controls':29,'corrupt_reports_caught':61,'value_preserving_corrupt_reports_caught':same_value,
         'source_and_control_hashes_unchanged_since_pre_candidate_freeze':True,
         'receipts':receipts,'freeze_sha256':sha(HERE/'PRE-CANDIDATE-FREEZE.json'),
         'kernel_plants_preregistered':len(kernel['plants']),'kernel_plants_executed':False,
         'candidate_content_inspected':False,'candidate_paths_located':False,
         'candidate_or_Lean_compilation_performed':False,'child_agents_used':0,
         'additional_independent_replications':0,
         'all_main_milestones':freeze['all_main_milestones'],
         'old_integration_manifest_identity_only':sha(old),
         'next_action':'wait for exact author freeze and root release'}
dest=HERE/'PRE-CANDIDATE-RECEIPT.json';assert not dest.exists()
dest.write_text(json.dumps(receipt,indent=2)+'\n')
files=sorted([p for p in HERE.rglob('*') if p.is_file() and p.name!='READY-ARTIFACTS.json'
              and '__pycache__' not in p.parts]+list(OUT.glob('algorithm-core-work-fresh-review-*')))
manifest={'created_utc':datetime.now(timezone.utc).isoformat(),
          'scope':'immutable pre-candidate readiness snapshot; later review uses new phase-specific files/logs',
          'file_hashes':{str(p.relative_to(ROOT)):sha(p) for p in files},
          'manifest_excludes_itself_and_python_caches':True}
target=HERE/'READY-ARTIFACTS.json';assert not target.exists()
target.write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'status':receipt['status'],'clean_controls':29,'corrupt_reports_caught':61,
                  'value_preserving_corrupt_reports_caught':same_value,'files_hashed':len(files),
                  'manifest_sha256':sha(target),'candidate_content_inspected':False}))
