#!/usr/bin/env python3
"""Verify authorized v3 bytes and copy sources/evidence, never scientific oleans."""
import hashlib
import json
from pathlib import Path
import time
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[6]
manifest=ROOT/'research/rmaf/algorithm/universal233/forest_solver/FOREST-SOLVER-MANIFEST-v3.json'
sha=lambda b:hashlib.sha256(b).hexdigest()
b=manifest.read_bytes()
assert sha(b)=='89937a6f71bceb2dbeb64917b4b805e8f193fa485b00ec28acecdc95d047dcf5'
m=json.loads(b)
assert m['version']==3 and len(m['immutable_files'])==540
assert len({r['path'] for r in m['immutable_files']})==540
dst=HERE/'pinned-payload'
dst.mkdir(exist_ok=False)
rows=[]
started=time.perf_counter()
for row in m['immutable_files']:
    src=(ROOT/row['path']).resolve()
    assert src.is_relative_to(ROOT), 'outside-workspace payload path'
    data=src.read_bytes()
    assert sha(data)==row['sha256'], 'candidate hash mismatch '+row['path']
    excluded=src.suffix in ['.olean','.ilean','.ir']
    if not excluded:
        target=dst/row['path']
        target.parent.mkdir(parents=True,exist_ok=True)
        target.write_bytes(data)
        target.chmod(0o444)
    rows.append({**row,'size':len(data),'copied':not excluded,'reason':'no scientific copied olean/IR' if excluded else 'exact byte copy'})
receipt={'manifest_sha256':sha(b),'verified':len(rows),'copied':sum(r['copied'] for r in rows),
         'excluded_scientific_binaries':sum(not r['copied'] for r in rows),
         'seconds':time.perf_counter()-started,'entries':rows}
(HERE/'payload-copy-v1.json').write_text(json.dumps(receipt,indent=2)+'\n')
(HERE/'EXACT-AUTHOR-MANIFEST-v3.json').write_bytes(b)
print(json.dumps({k:v for k,v in receipt.items() if k!='entries'}))
