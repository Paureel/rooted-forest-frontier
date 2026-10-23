#!/usr/bin/env python3
"""One-shot development build from completed frozen source copies only."""
from pathlib import Path
import hashlib,json,os,re,subprocess,time
D=Path(__file__).resolve().parent;ROOT=D.parents[4];OUT=D/'dev';OUT.mkdir(exist_ok=True)
H=ROOT/'results/algorithm-universal233-hard-refinement-20261015T084225Z'
O=ROOT/'results/algorithm-universal233-output-state-20261015T105826Z'
F=ROOT/'results/algorithm-universal233-final-cuts-replay-20261015T105812Z'
seen=[];rows=[]
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def add(n):
 if n in seen:return
 p=H/(n+'.lean')
 if not p.exists():p=O/(n+'.lean')
 if not p.exists():p=F/(n+'.lean')
 if not p.exists():raise RuntimeError('UNAVAILABLE_COMPLETED_MODULE '+n)
 text=p.read_text()
 for name in re.findall(r'^import ([A-Za-z0-9_]+)\s*$',text,re.M):
  if name not in ('Std','Lean'):add(name)
 seen.append(n)
 target=OUT/(n+'.lean')
 if not target.exists() or target.read_bytes()!=p.read_bytes(): target.write_bytes(p.read_bytes())
 rows.append({'module':n,'source':str(p.relative_to(ROOT)),'sha256':digest(p)})
for n in ['Safety','Forest','GroupEmbedding','Parents','Equivalence','Recovery','FinalWork']:add(n)
(OUT/'source-inputs.json').write_text(json.dumps(rows,indent=2)+'\n')
(OUT/'lean-toolchain').write_bytes((ROOT/'research/rmaf/lean/lean-toolchain').read_bytes())
env=dict(os.environ,LEAN_PATH=str(OUT));runs=[]
for n in seen:
 out=OUT/(n+'.olean')
 if out.exists() and out.stat().st_mtime>(OUT/(n+'.lean')).stat().st_mtime:continue
 start=time.monotonic();p=subprocess.run([str(ROOT/'bootloops-lean'),'-o',str(out),str(OUT/(n+'.lean'))],cwd=ROOT,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=60)
 (OUT/(n+'.log')).write_text(p.stdout);runs.append({'module':n,'exit':p.returncode,'seconds':time.monotonic()-start})
 if p.returncode:raise RuntimeError(n+'\n'+p.stdout)
(OUT/'builds.json').write_text(json.dumps(runs,indent=2)+'\n')
print(len(seen),'completed source modules prepared;',round(sum(r['seconds'] for r in runs),3),'compile seconds')
