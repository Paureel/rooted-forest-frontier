#!/usr/bin/env python3
"""One-shot local pin/copy of this agent's own frozen forest instruments."""
import hashlib
import json
from pathlib import Path
import shutil

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[5]
OLD = ROOT / 'research/rmaf/algorithm/verification/forest-solver-2026-10-15/sol-pre-candidate'
items = [
    ('graph_partition_v2.py', 'reused/graph_partition_v2.py'),
    ('post-release-v1/producer_audit_v4.lean', 'reused/producer_audit_v4.lean'),
    ('toy-src/Clean.lean', 'producer-base/Clean.lean'),
]
rows = []
for old, new in items:
    source, target = OLD / old, HERE / new
    assert not target.exists(), str(target)
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(source, target)
    data = source.read_bytes()
    assert target.read_bytes() == data
    target.chmod(0o444)
    rows.append({'source': str(source.relative_to(ROOT)), 'copy': new,
                 'sha256': hashlib.sha256(data).hexdigest(), 'bytes': len(data)})
result = {
    'scope': 'classification/prefix new prerelease controls; no classification candidate contact',
    'original_forest_READY_sha256': hashlib.sha256((OLD/'READY-v1.json').read_bytes()).hexdigest(),
    'original_forest_final_manifest_sha256': hashlib.sha256((OLD/'post-release-v1/FINAL-MANIFEST-v1.json').read_bytes()).hexdigest(),
    'items': rows,
    'shared_layers': 'same author/model family, earlier public RMAF definitions, exact own graph/producer code, local Python/Lean/std runtime and hardware',
    'limits': 'graph/producer code is reused, never called fresh for this arm; no statistical independence or extra replication credit; new scoped controls are required',
    'candidate_contacts': [],
}
(HERE/'REUSE-PINS-v1.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps({'copied': len(rows), 'classification_candidate_contacts': 0}))
