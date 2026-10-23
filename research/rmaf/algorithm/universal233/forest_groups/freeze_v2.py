#!/usr/bin/env python3
"""One-shot append-only freeze metadata correction; preserve all v1 records."""
from pathlib import Path
import datetime,hashlib,json
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[4]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
oldpath=HERE/'FOREST-GROUPS-MANIFEST-v1.json'
old=json.loads(oldpath.read_text())
expected_log=str((HERE/'freeze.log').relative_to(ROOT))
bad=[x['path'] for x in old['immutable_files'] if sha(ROOT/x['path'])!=x['sha256']]
assert bad==[expected_log],bad
newpath=HERE/'FOREST-GROUPS-MANIFEST-v2.json'
assert not newpath.exists()
paths=[ROOT/x['path'] for x in old['immutable_files']]
paths += [oldpath,HERE/'FOREST-GROUPS-MANIFEST-v1.sha256',HERE/'FREEZE-AMENDMENT-v2.md',Path(__file__)]
rows=[dict(path=str(p.relative_to(ROOT)),sha256=sha(p),bytes=p.stat().st_size) for p in sorted(set(paths))]
new=dict(old)
new.update(version=2,frozen_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),supersedes=str(oldpath.relative_to(ROOT)),
 amendment='FREEZE-AMENDMENT-v2.md: correct the sole freeze.log entry hashed while stdout was still writing; mathematical sources and canonical replay unchanged.',
 prior_manifest_sha256=sha(oldpath),
 no_write_boundary='Every v2 immutable_files entry and this v2 manifest/seal are frozen. build/ is excluded mutable development output. New replay receipt directories are permitted; replay does not rewrite LATEST-REPLAY after the preserved v1 manifest exists.',immutable_files=rows)
newpath.write_text(json.dumps(new,indent=2)+'\n')
seal=sha(newpath)
(HERE/'FOREST-GROUPS-MANIFEST-v2.sha256').write_text(seal+'  '+str(newpath.relative_to(ROOT))+'\n')
print(json.dumps(dict(manifest=str(newpath.relative_to(ROOT)),sha256=seal,immutable_files=len(rows),corrected_entry=expected_log,canonical_receipt=new['canonical_receipt'],status=new['status'],all_three_main_milestones='OPEN'),indent=2))
