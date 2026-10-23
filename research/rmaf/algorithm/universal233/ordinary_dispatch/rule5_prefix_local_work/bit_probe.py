#!/usr/bin/env python3
"""Fresh copied-byte corruption controls; immutable objects never modified."""
from pathlib import Path
import datetime,hashlib,json,shutil
D=Path(__file__).resolve().parent;R=D.parents[5]
O=R/'results'/('algorithm-universal233-rule5-prefix-local-work-bits-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'));O.mkdir()
def sha(b):return hashlib.sha256(b).hexdigest()
def require(b,h):
 if sha(b)!=h:raise ValueError('BYTE_PIN_MISMATCH')
def rejected(b,h):
 try:require(b,h)
 except ValueError:return True
 return False
assert shutil.disk_usage(O).free>=3*1024**3
require(b'abc','ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad')
assert rejected(b'abd','ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad')
deps=json.loads((D/'DEPENDENCIES.json').read_text());e=min(deps,key=lambda e:(R/e['olean']).stat().st_size)
rows=[]
for kind,key in [('source','source'),('object','olean')]:
 p=R/e[key];raw=p.read_bytes();expected=e[key+'_sha256'];require(raw,expected)
 changed=bytearray(raw);index=len(changed)//2;changed[index]^=1
 q=O/('one-bit-'+p.name);q.write_bytes(changed)
 assert rejected(q.read_bytes(),expected)
 assert sha(p.read_bytes())==expected
 rows.append(dict(kind=kind,original=str(p.relative_to(R)),original_sha256=expected,original_bytes=len(raw),copied_corrupt=str(q.relative_to(R)),copied_sha256=sha(changed),flipped_byte_index=index,flipped_mask=1,caught=True))
rec=dict(status='PASS_FRESH_COPIED_SOURCE_OBJECT_ONE_BIT_CONTROLS',planted_clean=True,planted_corrupt_caught=True,rows=rows,immutable_originals_unchanged=True,free_bytes=shutil.disk_usage(O).free,qualification='Byte/source binding control only, no mathematical or machine-code equivalence acceptance')
(O/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n');print(rec['status'],O)
