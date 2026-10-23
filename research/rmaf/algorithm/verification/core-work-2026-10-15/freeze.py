#!/usr/bin/env python3
"""Exact-path pre-candidate readiness freeze; no author package discovery."""
from datetime import datetime,timezone
import hashlib
import json
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[4]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
sources={
 'research/rmaf/algorithm/TARGET.md':{'read':'main target/status :5-13; prior full read', 'expected':None},
 'research/rmaf/lean/RMAF.lean':{'read':'leaves :13-15; prior full source contact', 'expected':'4960d5be9a5f1eb6b15d11c76130bee5263125631314a4eb2d43d500d5b513a9'},
 'research/rmaf/algorithm/universal233/core/CoreProgram.lean':{'read':'reopened complete executable body :1-126; prior full source contact', 'expected':'9aa92355dfecf6e0e3d7707c1c284cabcb2f3846b6682e3b55b719e35cb7311f'},
 'research/rmaf/algorithm/universal233/core/CoreGraph.lean':{'read':'source support/singleton interfaces :185-258; prior full source contact', 'expected':'7099d4aa48a771f1d56e11bd36447a51d7e3c57094a6779c0d40acec11dca7a0'}}
copies=HERE/'frozen-inputs';copies.mkdir(exist_ok=False)
contacts=[]
for name,info in sources.items():
 p=ROOT/name;h=sha(p)
 if info['expected']:assert h==info['expected'],name
 dest=copies/p.name;dest.write_bytes(p.read_bytes())
 contacts.append({'path':name,'sha256':h,'read_locator':info['read'],
                  'copy':str(dest.relative_to(ROOT)),'copy_sha256':sha(dest),
                  'role':'permitted contacted specification/dependency, not an independent oracle'})
old=ROOT/'research/rmaf/algorithm/verification/integration-2026-10-15/ARTIFACTS.json'
assert sha(old)=='4cbbba186a546ac48e5f27736b7a537a5d83d3b0bec40a2156b15d80040b1c65'
contact={'new_permitted_source_contacts':contacts,
         'prior_lineage':'same independent reviewer; graph/partition checks and complete module-origin/private-axiom audit experience are previously contacted/burned inputs',
         'additional_independent_replications':0,
         'new_code':'work_ledger.py is independently organized event/cost accounting; standard-library imports only, no author/other-verifier imports',
         'candidate_content_inspected':False,'candidate_paths_located':False,
         'old_integration_manifest_identity_only':{'path':str(old.relative_to(ROOT)),'sha256':sha(old)},
         'forbidden_content_not_read':['core_work proof/COST-MODEL/receipts','assembly','whole_source_mass','pair proofs','other completion verifier']}
(HERE/'SOURCE-CONTACTS.json').write_text(json.dumps(contact,indent=2)+'\n')
controls=json.loads((HERE/'CONTROL-PIN.json').read_text())
assert controls['declared_controls']==len(controls['controls'])==29
assert controls['declared_plants']==sum(len(c['plants']) for c in controls['controls'])==61
files=[ROOT/p for p in sources]+list(copies.iterdir())
files += [HERE/p for p in ['OPERATION-SPEC.md','CONTROL-PIN.json','work_ledger.py','define_controls.py',
                           'KERNEL-GATES.json','SOURCE-CONTACTS.json','freeze.py']]
freeze={'created_utc':datetime.now(timezone.utc).isoformat(),
        'phase':'pre-candidate before first event-ledger execution',
        'declared_controls':29,'declared_report_corruptions':61,
        'candidate_content_inspected':False,'candidate_compilation_performed':False,
        'comparison':'literal value fields AND structural work/metadata fields, plus record-ID and exported-total integrity',
        'timing_plan':'first3 micro controls, four declared size-pilot cases, slowest measured row times29 before fixed full battery; no census',
        'additional_independent_replications':0,
        'all_main_milestones':{'complete_algorithm':'OPEN','universal_correctness':'OPEN','smaller_base':'OPEN'},
        'files_sha256':{str(p.relative_to(ROOT)):sha(p) for p in files}}
dest=HERE/'PRE-CANDIDATE-FREEZE.json';assert not dest.exists()
dest.write_text(json.dumps(freeze,indent=2)+'\n')
print(json.dumps({'declared_controls':29,'report_corruptions':61,'files_pinned':len(files),
                  'freeze_sha256':sha(dest),'ledger_executed':False,'candidate_content_inspected':False}))
