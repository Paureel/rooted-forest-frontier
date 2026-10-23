from pathlib import Path
import hashlib,json,subprocess,os,time
D=Path(__file__).resolve().parent;R=D.parents[4];U=D.parent;O=D/'stack';O.mkdir(exist_ok=True)
C=R/'results/algorithm-universal233-assembly-completion-20261015T090155Z';cert=json.loads((C/'certificate.json').read_text());spec=[(n,C/(n+'.lean'),None) for n in cert['positive_order']]
V=R/'research/rmaf/algorithm/verification/pair-case-2026-10-15/frozen-review-v2';v=json.loads((V/'MANIFEST.json').read_text());assert len(v['files'])==196
for f,h in v['files'].items():assert hashlib.sha256((V/f).read_bytes()).hexdigest()==h
J=V/'isolated-review-v1/joint'
spec += [('ExchangeRestriction',J/'Restriction.lean','filename only Restriction -> ExchangeRestriction'),('Cluster',J/'Cluster.lean','first import only Restriction -> ExchangeRestriction')]
spec += [(n,J/(n+'.lean'),None) for n in ['Descendant','Forest','Surgery','Count','Parents','Exchange','SourceEdge','Selector','Interface']]
entries=[];env=dict(os.environ,LEAN_PATH=str(O));runs=[]
for n,p,a in spec:
 data=p.read_bytes()
 if n=='Cluster':
  assert data.startswith(b'import Restriction\n');data=data.replace(b'import Restriction\n',b'import ExchangeRestriction\n',1)
 (O/(n+'.lean')).write_bytes(data);entries.append({'module':n,'source':str(p.relative_to(R)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'compiled_sha256':hashlib.sha256(data).hexdigest(),'adapter':a})
(O/'lean-toolchain').write_bytes((R/'research/rmaf/lean/lean-toolchain').read_bytes())
for n,p,a in spec:
 s=time.monotonic();r=subprocess.run([str(R/'bootloops-lean'),'-o',str(O/(n+'.olean')),str(O/(n+'.lean'))],cwd=R,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=30);(O/(n+'.log')).write_text(r.stdout);runs.append({'module':n,'exit':r.returncode,'seconds':time.monotonic()-s})
 if r.returncode:raise SystemExit(r.stdout)
(D/'STACK-PINS.json').write_text(json.dumps({'development_only':True,'pair_review_manifest':hashlib.sha256((V/'MANIFEST.json').read_bytes()).hexdigest(),'entries':entries,'runs':runs},indent=2)+'\n');print('PASS frozen pair integration stack',len(spec))
