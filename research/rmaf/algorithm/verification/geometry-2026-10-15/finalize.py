#!/usr/bin/env python3
"""One-shot final source/log integrity snapshot of the scoped geometry review."""
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[4];OUT=ROOT/'research/rmaf/results'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
pre=json.loads((HERE/'PRE-CANDIDATE-FREEZE.json').read_text())
for p,h in pre['files_sha256'].items():assert sha(ROOT/p)==h,p
author=json.loads((HERE/'AUTHOR-SOURCE-FREEZE.json').read_text())
for r in author['source_pin_checks']:assert sha(ROOT/r['path'])==r['expected']==r['actual'],r['path']
for p,h in author['extra_first_contact_hashes'].items():assert sha(ROOT/p)==h,p
lean=json.loads((OUT/'algorithm-geometry-fresh-review-lean.json').read_text())
assert lean['all_passed'] and all(r['passed'] for r in lean['rows'])
for r in lean['rows']:
    assert sha(ROOT/r['source'])==r['source_sha256']
    assert sha(ROOT/r['log'])==r['log_sha256']
assert all(set(a)<= {'propext','Classical.choice','Quot.sound'} for a in lean['axiom_inventory'].values())
assert sha(HERE/'replay.py')==lean['source_sha256']
assert sha(HERE/'prepare_replay.py')==lean['generation_adapter_sha256']
mapping=json.loads((HERE/'LEAN-CONTROL-MAP.json').read_text())
for p,h in mapping['generated_sources_sha256'].items():assert sha(ROOT/p)==h,p
trace=json.loads((HERE/'CONSUMER-TRACE.json').read_text())
assert len(trace['claims'])==15 and all(v=='OPEN' for v in trace['all_main_milestones'].values())
review=(HERE/'referee_sim_VERDICT.md').read_text()
assert sha(HERE/'VERDICT.md') in review and sha(HERE/'CONSUMER-TRACE.json') in review
files=sorted([p for p in HERE.rglob('*') if p.is_file() and p.name!='ARTIFACTS.json' and '__pycache__' not in p.parts]
             +list(OUT.glob('algorithm-geometry-fresh-review-*')))
receipt={'review':'frozen original-address geometry constituents; same reviewer lineage, zero extra independent replications',
         'created_utc':datetime.now(timezone.utc).isoformat(),'scope':'CONFIRMED-SCOPED geometry and kernel finite/source review; no full algorithm acceptance',
         'open_obligations':['OPEN-STATE-ORIGINAL','OPEN-CORE-REALIZATION','complete rules/termination/reconstruction/runtime'],
         'all_main_milestones':trace['all_main_milestones'],
         'report':str((HERE/'VERDICT.md').relative_to(ROOT)),
         'consumer_trace':str((HERE/'CONSUMER-TRACE.json').relative_to(ROOT)),
         'file_hashes':{str(p.relative_to(ROOT)):sha(p) for p in files},'manifest_excludes_itself':True,
         'all_pre_candidate_author_source_and_executed_log_identities_match':True}
dest=HERE/'ARTIFACTS.json';assert not dest.exists();dest.write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'files_hashed':len(files),'manifest_sha256':sha(dest),'scope':receipt['scope']}))
