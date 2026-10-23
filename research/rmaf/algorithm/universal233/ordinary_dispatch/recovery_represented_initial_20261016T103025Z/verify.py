#!/usr/bin/env python3
"""One-shot seal identity check; identity is not independent scientific acceptance."""
from pathlib import Path
import hashlib,json
D=Path(__file__).resolve().parent;R=D.parents[5];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();m=json.loads((D/'FINAL-MANIFEST-v1.json').read_text())
for e in m['immutable_files']:
 p=R/e['path'];assert sha(p)==e['sha256'] and not p.stat().st_mode&0o222,str(p)
for e in m['original_files']:
 p=R/e['path'];s=p.stat();assert sha(p)==e['sha256'] and oct(s.st_mode&0o777)==e['mode'] and s.st_ino==e['inode'] and s.st_dev==e['device'],str(p)
assert (D/'FINAL-MANIFEST-v1.sha256').read_text().split()[0]==sha(D/'FINAL-MANIFEST-v1.json')
print('PASS_REPRESENTED_INITIAL_NORMALIZE_SEAL_IDENTITY',len(m['immutable_files']),'readonly members',len(m['original_files']),'preserved originals',sha(D/'FINAL-MANIFEST-v1.json'))
