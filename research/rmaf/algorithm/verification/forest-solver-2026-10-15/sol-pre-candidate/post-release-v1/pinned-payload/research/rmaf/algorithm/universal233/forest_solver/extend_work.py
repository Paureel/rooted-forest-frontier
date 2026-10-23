#!/usr/bin/env python3
"""One-task completed source work adapters; proof bodies unchanged."""
from pathlib import Path
import hashlib,json,os,subprocess
D=Path(__file__).resolve().parent;R=D.parents[4];U=D.parent;B=D/'build'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
assert sha(B/'Work.lean')==sha(U/'core_work/Work.lean'), 'existing Work must be the actual completed core-work source'
for n,p,adapts in [
 ('ForestColorWork',U/'whole_source_work/ColorWork.lean',{}),
 ('ForestGeometryWork',U/'whole_source_work/GeometryWork.lean',{'ColorWork':'ForestColorWork'})]:
 s=p.read_text()
 for old,new in adapts.items():
  assert s.count('import '+old+'\n')==1;s=s.replace('import '+old+'\n','import '+new+'\n',1)
 (B/(n+'.lean')).write_text(s)
 rows.append(dict(module=n,path=str(p.relative_to(R)),sha256=sha(p),adaptations=adapts,adapted_sha256=sha(B/(n+'.lean'))))
 p=subprocess.run([str(R/'bootloops-lean'),'-o',str(B/(n+'.olean')),str(B/(n+'.lean'))],cwd=B,env=dict(os.environ,LEAN_PATH=str(B)),capture_output=True,text=True,timeout=60)
 (B/(n+'-setup.log')).write_text(p.stdout+p.stderr);assert p.returncode==0,(n,p.stdout,p.stderr)
(D/'WORK-PINS.json').write_text(json.dumps(dict(entries=rows),indent=2)+'\n')
print('PASS completed work support',len(rows),'modules')
