#!/usr/bin/env python3
"""One-task source-bound setup; no expected mathematical outputs generated."""
from pathlib import Path
import hashlib,json,os,subprocess,time,datetime
D=Path(__file__).resolve().parent;R=D.parents[4];U=D.parent;B=D/'build';B.mkdir(exist_ok=True)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
entries=[]
for f in ['STACK-PINS.json','BINARY-STACK-PINS.json']:
 for e in json.loads((U/'output_state'/f).read_text())['entries']:
  p=R/e['path'];assert sha(p)==e['sha256'];s=p.read_text()
  for old,new in e['adaptations'].items():
   assert s.count('import '+old+'\n')==1;s=s.replace('import '+old+'\n','import '+new+'\n',1)
  assert hashlib.sha256(s.encode()).hexdigest()==e['adapted_sha256']
  (B/(e['module']+'.lean')).write_text(s);entries.append(e)
def add(n,p,adapts={}):
 s=p.read_text()
 for old,new in adapts.items():
  assert s.count('import '+old+'\n')==1;s=s.replace('import '+old+'\n','import '+new+'\n',1)
 (B/(n+'.lean')).write_text(s)
 entries.append(dict(module=n,path=str(p.relative_to(R)),sha256=sha(p),adaptations=adapts,adapted_sha256=sha(B/(n+'.lean'))))
for n in ['OutputDefs','Materialize','Equivalence']:add(n,U/'output_state'/(n+'.lean'))
names=['Caller','Specification','Budgets','Mass','Work']
for i,n in enumerate(names):add('Query'+n,U/'query_scheduler'/(n+'.lean'),{names[i-1]:'Query'+names[i-1]} if i else {})
assert len(entries)==len({e['module'] for e in entries})
(D/'STACK-PINS.json').write_text(json.dumps(dict(entries=entries),indent=2)+'\n')
(B/'lean-toolchain').write_bytes((R/'research/rmaf/lean/lean-toolchain').read_bytes())
runs=[]
for e in entries:
 n=e['module'];t=time.monotonic();p=subprocess.run([str(R/'bootloops-lean'),'-o',str(B/(n+'.olean')),str(B/(n+'.lean'))],cwd=B,env=dict(os.environ,LEAN_PATH=str(B)),capture_output=True,text=True,timeout=60)
 (B/(n+'.log')).write_text(p.stdout+p.stderr);runs.append(dict(module=n,exit=p.returncode,seconds=time.monotonic()-t))
 (D/'SETUP.json').write_text(json.dumps(runs,indent=2)+'\n')
 assert p.returncode==0,(n,p.stdout,p.stderr)
print('PASS completed-source setup',len(entries),'modules',round(sum(x['seconds'] for x in runs),3),'seconds')
