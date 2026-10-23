#!/usr/bin/env python3
"""One-shot development build; frozen v1 oleans are DEVELOPMENT cache only.
The final replay must rebuild every original source in a new isolated path.
"""
from pathlib import Path
import json,hashlib,subprocess,os,time
D=Path(__file__).resolve().parent;R=D.parents[4];V=D.parent/'rule5_local';O=D/'build';O.mkdir(exist_ok=True)
if (D/'CLASSIFICATION-MANIFEST-v1.json').exists():raise SystemExit('FROZEN_NO_WRITE_BOUNDARY')
M=json.loads((V/'RULE5-LOCAL-MANIFEST-v1.json').read_text());C=R/M['canonical_receipt']['receipt']
entries=json.loads((V/'STACK-PINS.json').read_text())
locals=['Attachment','AdmittedGeometry','UniqueCherry','FiveBranches','AdmittedCases','OutsideCore','LargePendant','LargeExchange','LargeAdmitted','SourceWork','LocalSelector','ClassificationControls']
entries += [dict(module=n,path=str((D/(n+'.lean')).relative_to(R)),adaptations={}) for n in locals if (D/(n+'.lean')).exists()]
(O/'lean-toolchain').write_bytes((C/'lean-toolchain').read_bytes())
for e in entries:
 p=R/e['path'];src=p.read_text();e['sha256']=hashlib.sha256(p.read_bytes()).hexdigest()
 for a,b in e.get('adaptations',{}).items():src=src.replace('import '+a+'\n','import '+b+'\n')
 e['adapted_sha256']=hashlib.sha256(src.encode()).hexdigest();n=e['module'];f=O/(n+'.lean')
 changed=not f.exists() or f.read_text()!=src;f.write_text(src)
 (D/'STACK-PINS.json').write_text(json.dumps(entries,indent=2)+'\n')
 if not p.is_relative_to(D):
  assert (C/(n+'.lean')).read_text()==src
  if not (O/(n+'.olean')).exists():(O/(n+'.olean')).write_bytes((C/(n+'.olean')).read_bytes())
  continue
 t=time.monotonic();q=subprocess.run([str(R/'bootloops-lean'),'-o',str(O/(n+'.olean')),str(f)],cwd=O,env=dict(os.environ,LEAN_PATH=str(O)),text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=60)
 stamp=str(time.time_ns());(O/(n+'-'+stamp+'.log')).write_text(q.stdout)
 print(n,q.returncode,round(time.monotonic()-t,3),flush=True)
 if q.returncode:print(q.stdout);raise SystemExit(q.returncode)
