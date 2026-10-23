#!/usr/bin/env python3
"""One-shot final file-integrity snapshot for this continued review only."""
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
OUT = ROOT/'research/rmaf/results'
def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

rec_path = OUT/'algorithm-review-continue-reconciliation-v4.json'
rec = json.loads(rec_path.read_text())
for path, expected in rec['evidence_hashes'].items():
    assert sha(ROOT/path) == expected, path
trace = json.loads((HERE/'CONSUMER-TRACE.json').read_text())
verdict = json.loads((OUT/'algorithm-review-continue-verdict.json').read_text())
assert len(trace['consumer_trace']) == 26 and len(verdict['claims']) == 29
assert all(x == 'OPEN' for x in verdict['all_three_main_milestones'].values())
slow = json.loads((OUT/'algorithm-review-continue-slow-source-replay.json').read_text())
for path, expected in slow['source_hashes'].items():
    assert sha(ROOT/path) == expected, path
assert (HERE/'referee_sim_VERDICT.md').exists()
files = sorted([p for p in HERE.iterdir() if p.is_file() and p.name != 'ARTIFACTS.json']
               + list(OUT.glob('algorithm-review-continue-*')))
manifest = {
    'review': 'continued frozen A/B and balanced/Q review; no extra independent replication',
    'created_utc': datetime.now(timezone.utc).isoformat(),
    'final_scientific_state': verdict['all_three_main_milestones'],
    'scope': 'finite exact evidence, source-bound kernel constituents and consumer review; no universal algorithm acceptance',
    'final_records': {
        'report': str((HERE/'VERDICT.md').relative_to(ROOT)),
        'consumer_trace': str((HERE/'CONSUMER-TRACE.json').relative_to(ROOT)),
        'claim_ledger': str((OUT/'algorithm-review-continue-verdict.json').relative_to(ROOT)),
        'reconciliation': str(rec_path.relative_to(ROOT)),
        'new_bounded_source_replay': str((OUT/'algorithm-review-continue-slow-source-replay.json').relative_to(ROOT)),
        'transcription_check': str((OUT/'algorithm-review-continue-transcription-v3.json').relative_to(ROOT)),
        'fresh_frame_review': str((HERE/'referee_sim_VERDICT.md').relative_to(ROOT)),
        'false_control_provenance': str((HERE/'FALSE-CONTROL-PROVENANCE.json').relative_to(ROOT)),
    },
    'file_hashes': {str(p.relative_to(ROOT)):sha(p) for p in files},
    'manifest_excludes_itself': True,
    'all_reconciled_source_log_identities_still_match': True,
}
dest = HERE/'ARTIFACTS.json'
assert not dest.exists()
dest.write_text(json.dumps(manifest, indent=2)+'\n')
print(json.dumps({'files_hashed':len(files), 'manifest':str(dest.relative_to(ROOT)),
                  'manifest_sha256':sha(dest), 'all_main_milestones':'OPEN'}))
