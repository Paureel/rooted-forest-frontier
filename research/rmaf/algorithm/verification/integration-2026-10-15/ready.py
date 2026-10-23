#!/usr/bin/env python3
"""Retain pre-candidate source/control/log integrity and readiness snapshot."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
OUT = ROOT / 'research/rmaf/results'

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

freeze = json.loads((HERE / 'PRE-CANDIDATE-FREEZE.json').read_text())
for name, expected in freeze['files_sha256'].items():
    assert sha(ROOT / name) == expected, name
controls = json.loads((OUT / 'algorithm-integration-fresh-review-controls-v1.json').read_text())
assert controls['all_passed']
for name in ['declared_controls', 'completed', 'clean_passed', 'false_expectations', 'false_expectations_caught']:
    assert controls[name] == 49, name
assert controls['source_sha256'] == sha(HERE / 'original_graph.py')
assert controls['control_sha256'] == sha(HERE / 'CONTROL-PIN.json')
assert controls['freeze_sha256'] == sha(HERE / 'PRE-CANDIDATE-FREEZE.json')
by_id = {r['id']: r['actual'] for r in controls['rows']}
assert by_id['attempt-stale-valid-edge-not-a-current-group']['continuation_called']
assert not by_id['attempt-stale-valid-edge-not-a-current-group']['chosen_is_current_group']
assert by_id['leafless-support-satisfies-weak-structure']['valid']
assert not by_id['distinct-actual-cuts-leafless-root-trap']['exact_partition_and_cost']
kernel = json.loads((HERE / 'KERNEL-CONTROL-PIN.json').read_text())
receipt = {'created_utc': datetime.now(timezone.utc).isoformat(),
           'status': 'READY-TO-RECEIVE-FROZEN-CANDIDATE',
           'scope': 'finite instrument/control readiness; no integration content reviewed or accepted',
           'controls': 49, 'clean_passed': 49, 'false_expected_twins_caught': 49,
           'source_and_frozen_dependency_hashes_unchanged': True,
           'candidate_content_inspected': False, 'candidate_path_metadata_exposed': True,
           'additional_independent_replications': 0,
           'kernel_detector_plants_preregistered': [r['id'] for r in kernel['plants']],
           'kernel_detector_plants_executed': False,
           'all_main_milestones': freeze['all_main_milestones'],
           'freeze_sha256': sha(HERE / 'PRE-CANDIDATE-FREEZE.json'),
           'control_receipt_sha256': sha(OUT / 'algorithm-integration-fresh-review-controls-v1.json'),
           'control_log_sha256': sha(OUT / 'algorithm-integration-fresh-review-controls-v1.log'),
           'next_action': 'wait for root candidate release; do not inspect integration or unfinished research'}
dest = HERE / 'PRE-CANDIDATE-RECEIPT.json'
assert not dest.exists()
dest.write_text(json.dumps(receipt, indent=2) + '\n')
files = sorted([p for p in HERE.rglob('*') if p.is_file() and p.name != 'READY-ARTIFACTS.json'
                and '__pycache__' not in p.parts] + list(OUT.glob('algorithm-integration-fresh-review-*')))
manifest = {'created_utc': datetime.now(timezone.utc).isoformat(),
            'scope': 'pre-candidate readiness snapshot; future review files do not alter this record',
            'file_hashes': {str(p.relative_to(ROOT)): sha(p) for p in files},
            'manifest_excludes_itself': True}
manifest_path = HERE / 'READY-ARTIFACTS.json'
assert not manifest_path.exists()
manifest_path.write_text(json.dumps(manifest, indent=2) + '\n')
print(json.dumps({'status': receipt['status'], 'controls': 49, 'false_expected_twins_caught': 49,
                  'files_hashed': len(files), 'manifest_sha256': sha(manifest_path),
                  'candidate_content_inspected': False}))
