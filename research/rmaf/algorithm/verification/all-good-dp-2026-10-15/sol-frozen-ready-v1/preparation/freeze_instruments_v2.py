#!/usr/bin/env python3
"""Freeze preparation inputs/code before scientific execution; one-shot only."""
import datetime,hashlib,json,os,pathlib
H=pathlib.Path(__file__).resolve().parent;mp=H/'INSTRUMENTS-MANIFEST-v2.json';assert not mp.exists()
files=[]
for p in sorted(H.rglob('*')):
 if p.is_file() and p.suffix in {'.py','.json','.lean','.md'}:
  files.append({'path':str(p.relative_to(H)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size})
manifest={'status':'SOURCE-FROZEN-BEFORE-EXECUTION','freezeUTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':files,'candidateContact':False,'independentReplicaIncrement':0}
mp.write_text(json.dumps(manifest,indent=2)+'\n')
for r in files:os.chmod(H/r['path'],0o444)
os.chmod(mp,0o444)
print(json.dumps({'status':manifest['status'],'files':len(files),'manifestSHA256':hashlib.sha256(mp.read_bytes()).hexdigest()}))
