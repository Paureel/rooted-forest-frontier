#!/usr/bin/env python3
"""One-shot deterministic byte-adapter/control pin preparation, before execution."""
import hashlib
import json
from pathlib import Path
HERE = Path(__file__).resolve().parent
spec = json.loads((HERE/'PRODUCER-EXPECTATIONS-v1.json').read_text())
base = (HERE/'producer-base/Clean.lean').read_bytes()
for directory, old, new in [('producer-import', 'original', 'adapted'), ('producer-body', 'body_original', 'body_false')]:
    target = HERE/directory/'Clean.lean'
    assert not target.exists()
    target.parent.mkdir(parents=True, exist_ok=True)
    a, b = spec['adapter'][old].encode(), spec['adapter'][new].encode()
    assert base.count(a) == 1
    target.write_bytes(base.replace(a,b,1))
paths = [HERE/'PRODUCER-EXPECTATIONS-v1.json'] + sorted(p for p in HERE.glob('producer-*/*.lean'))
rows = [{'path':str(p.relative_to(HERE)), 'bytes':p.stat().st_size,
         'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in paths]
(HERE/'PRODUCER-CONTROLS-PIN-v1.json').write_text(json.dumps({'candidate_contact':False, 'entries':rows},indent=2)+'\n')
for p in paths + [HERE/'PRODUCER-CONTROLS-PIN-v1.json']:
    p.chmod(0o444)
print(json.dumps({'pinned_control_files':len(rows), 'candidate_contact':False}))
