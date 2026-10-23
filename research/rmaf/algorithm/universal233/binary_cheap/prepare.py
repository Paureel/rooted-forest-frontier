"""One-shot binary-cheap author stack. Existing toolkit lacks rooted-MAF Lean assembly;
wrap the completed frozen actual modules rather than reimplementing their kernel.
"""
from pathlib import Path
import hashlib,json,re,subprocess,os,time,datetime
D=Path(__file__).resolve().parent;R=D.parents[4];U=D.parent
B=D/'build';B.mkdir(exist_ok=True)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest_paths=[U/'pair_assembly/PAIR-ASSEMBLY-MANIFEST-v1.json',U/'rank_dichotomy/RANK-MANIFEST-v1.json',U/'rank_consumer/RANK-CONSUMER-MANIFEST-v1.json',U/'kept_parent/HANDOFF-MANIFEST-v1.json',U/'depth_one/DEPTH-ONE-MANIFEST-v1.json']
checks=[]
for p in manifest_paths:
 m=json.loads(p.read_text());rows=m.get('immutable_files',m.get('entries',[]))
 assert rows
 for e in rows:assert sha(R/e['path'])==e['sha256'],e['path']
 checks.append({'path':str(p.relative_to(R)),'sha256':sha(p),'checked':len(rows)})
dirs=[R/'results/algorithm-universal233-pair-assembly-20261015T093218Z',R/'results/algorithm-universal233-rank-consumer-20261015T094545Z',R/'results/algorithm-universal233-kept-20261015T094548Z',U/'depth_one/replay/20261015T101515Z']
candidates={}
for b in dirs:
 for p in b.glob('*.lean'):candidates.setdefault(p.stem,[]).append(p)
candidates['DepthRestriction']=[dirs[-1]/'Restriction.lean']
roots=['GoodPair','FourProbe','KeptConsumers','Witness01'];seen={};order=[]
def add(n):
 if n in seen:return
 assert n in candidates,n
 ps=candidates[n];p=ps[0];seen[n]=p
 data=p.read_text().replace('import Restriction\n','import DepthRestriction\n',1) if n=='Embedding' else p.read_text()
 for dep in re.findall(r'^import (\w+)\s*$',data,re.M):
  if dep not in ['Std','Lean']:add(dep)
 order.append(n)
for n in roots:add(n)
entries=[]
for n in order:
 p=seen[n];data=p.read_bytes()
 if n=='Embedding':data=data.replace(b'import Restriction\n',b'import DepthRestriction\n',1)
 (B/(n+'.lean')).write_bytes(data);entries.append({'module':n,'path':str(p.relative_to(R)),'sha256':sha(p),'compiled_sha256':hashlib.sha256(data).hexdigest(),'adapter':('first import Restriction->DepthRestriction' if n=='Embedding' else 'filename Restriction->DepthRestriction' if n=='DepthRestriction' else None)})
(B/'lean-toolchain').write_bytes((R/'research/rmaf/lean/lean-toolchain').read_bytes())
runs=[]
for n in order:
 s=time.monotonic();p=subprocess.run([str(R/'bootloops-lean'),'-o',str(B/(n+'.olean')),str(B/(n+'.lean'))],cwd=R,env=dict(os.environ,LEAN_PATH=str(B)),capture_output=True,text=True,timeout=45)
 (B/(n+'.log')).write_text(p.stdout+p.stderr);runs.append({'module':n,'exit':p.returncode,'seconds':time.monotonic()-s});assert p.returncode==0,(n,p.stdout,p.stderr)
(D/'STACK-PINS.json').write_text(json.dumps({'development_only':True,'manifests':checks,'entries':entries,'order':order,'runs':runs},indent=2)+'\n')
print('Prepared',len(order),'completed source modules in',sum(x['seconds'] for x in runs),'seconds')
