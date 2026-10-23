#!/usr/bin/env python3
"""Exact manifest-only pin and isolated source copies; no directory discovery."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
MANIFEST = ROOT / 'research/rmaf/algorithm/universal233/INTEGRATION-MANIFEST-v1.json'
EXPECTED = 'e4b8f631a98a1c059656da04e497d66e7703d076e18b7db9a22d86e98ad3ca93'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(MANIFEST) == EXPECTED
payload = json.loads(MANIFEST.read_text())
assert len(payload['immutable_files']) == 72
rows = []
for item in payload['immutable_files']:
    p = ROOT / item['path']
    actual = sha(p)
    rows.append({'path': item['path'], 'expected_sha256': item['sha256'],
                 'actual_sha256': actual, 'bytes': p.stat().st_size,
                 'matched': actual == item['sha256'] and p.stat().st_size == item['bytes']})
assert all(r['matched'] for r in rows)
build = HERE / 'isolated'
build.mkdir(exist_ok=False)
modules = {}
for row in rows:
    path = row['path']
    if path.endswith('.lean') and '/replay/' not in path:
        source = ROOT / path
        dest = build / source.name
        assert not dest.exists(), str(dest)
        dest.write_bytes(source.read_bytes())
        assert sha(dest) == row['actual_sha256']
        modules[source.stem] = {'source': path, 'copy': str(dest.relative_to(ROOT)), 'sha256': sha(dest)}
(HERE / 'AUTHOR-MANIFEST-FROZEN.json').write_bytes(MANIFEST.read_bytes())
receipt = {'created_utc': datetime.now(timezone.utc).isoformat(),
           'manifest_sha256': sha(MANIFEST), 'matched': len(rows), 'rows': rows,
           'isolated_source_modules': modules,
           'author_audit_executed_or_reused': False,
           'candidate_scope': payload['scope'], 'all_main_milestones': 'OPEN'}
(HERE / 'CANDIDATE-PIN.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps({'immutable_files_matched': len(rows), 'isolated_source_modules': len(modules),
                  'manifest_sha256': sha(MANIFEST), 'author_audit_executed': False}))
