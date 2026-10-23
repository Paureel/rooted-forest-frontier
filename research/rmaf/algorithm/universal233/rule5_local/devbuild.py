#!/usr/bin/env python3
"""One-shot source-bound Rule5 development build; completed contacts only."""
from pathlib import Path
import subprocess,os,json,hashlib,time
D=Path(__file__).resolve().parent;R=D.parents[4];O=D/'build';O.mkdir(exist_ok=True)
if (D/'RULE5-LOCAL-MANIFEST-v1.json').exists():raise SystemExit('FROZEN_NO_WRITE_BOUNDARY')
entries=json.loads((D.parent/'cherry_branching/DEV-STACK.json').read_text())
entries += [dict(module=n,path=str((D/(n+'.lean')).relative_to(R)),adaptations={})
            for n in ['Rule5Defs','Rule5PreControls','Rule5Graph','Rule5Triples','Rule5Exchange','Rule5Case323','Rule5Case321','Rule5GraphControls'] if (D/(n+'.lean')).exists()]
(O/'lean-toolchain').write_bytes((D.parent/'cherry_branching/lean-toolchain').read_bytes())
for e in entries:
 p=R/e['path'];src=p.read_text();e['sha256']=hashlib.sha256(p.read_bytes()).hexdigest()
 for a,b in e.get('adaptations',{}).items():src=src.replace('import '+a+'\n','import '+b+'\n')
 e['adapted_sha256']=hashlib.sha256(src.encode()).hexdigest();n=e['module'];target=O/(n+'.lean')
 changed=not target.exists() or target.read_text()!=src;target.write_text(src)
 (D/'STACK-PINS.json').write_text(json.dumps(entries,indent=2)+'\n')
 if not changed and (O/(n+'.olean')).exists():continue
 t=time.monotonic();q=subprocess.run([str(R/'bootloops-lean'),'-o',str(O/(n+'.olean')),str(target)],cwd=O,
  env=dict(os.environ,LEAN_PATH=str(O)),text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=60)
 (O/(n+'.log')).write_text(q.stdout);print(n,q.returncode,round(time.monotonic()-t,3),flush=True)
 if q.returncode:print(q.stdout);raise SystemExit(q.returncode)
