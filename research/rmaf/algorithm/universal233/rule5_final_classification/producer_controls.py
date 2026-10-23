#!/usr/bin/env python3
"""Freeze fresh Std-only producer controls before scientific module replay."""
from pathlib import Path
import sys,json,hashlib,datetime
sys.dont_write_bytecode=True
import audit
D=Path(__file__).resolve().parent;R=D.parents[4]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
out=R/'results'/('algorithm-universal233-rule5-final-classification-producer-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'));out.mkdir()
(out/'lean-toolchain').write_bytes((D.parent/'cherry_branching/lean-toolchain').read_bytes())
checks=audit.detector_controls(out)
record=dict(status='PASS_AUTHOR_STD_ONLY_PRODUCER_PREFLIGHT',post_contact=True,independent_credit=0,
 instrument_sha256=sha(D/'audit.py'),wrapper_sha256=sha(Path(__file__)),controls=checks,
 immutable_files=[dict(path=str(p.relative_to(R)),sha256=sha(p)) for p in sorted(out.iterdir()) if p.is_file()])
(out/'manifest.json').write_text(json.dumps(record,indent=2)+'\n')
for p in out.iterdir():
 if p.is_file():p.chmod(0o444)
(D/'PRODUCER-PREFLIGHT-v1.json').write_text(json.dumps(dict(receipt=str(out.relative_to(R)),sha256=sha(out/'manifest.json')),indent=2)+'\n')
print(record['status'],out)
