from pathlib import Path
import hashlib,json,os,subprocess,time
D=Path(__file__).resolve().parent;R=D.parents[4];U=D.parent;O=D/'stack';O.mkdir(exist_ok=True)
A=U/'assembly/replay/20261015T084051Z'; ac=json.loads((A/'certificate.json').read_text());order=ac['positive_order'];spec=[(n,A/(n+'.lean')) for n in order]
H=R/'results/algorithm-universal233-hard-refinement-20261015T084225Z'
spec += [(n,H/(n+'.lean')) for n in ['Executable','Endpoint','Restriction','PendantExclusion','Refinement','Components','Safety']]
M=R/'results/algorithm-universal233-whole-mass-20261015T082345Z'
spec += [(n,M/(n+'.lean')) for n in ['WholeColors','OriginalColors','WholeMass','MassControls']]
# No source bodies are changed. Existing Coverage copy adapter is already exact
# in the independently frozen assembly v1 receipt.
entries=[];env=dict(os.environ,LEAN_PATH=str(O));runs=[]
for n,p in spec:
 q=O/p.name;q.write_bytes(p.read_bytes());entries.append({'module':n,'source':str(p.relative_to(R)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
(O/'lean-toolchain').write_bytes((R/'research/rmaf/lean/lean-toolchain').read_bytes())
for n,p in spec:
 s=time.monotonic();r=subprocess.run([str(R/'bootloops-lean'),'-o',str(O/(n+'.olean')),str(O/(n+'.lean'))],cwd=R,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=30);(O/(n+'.log')).write_text(r.stdout);runs.append({'module':n,'exit':r.returncode,'seconds':time.monotonic()-s})
 if r.returncode:raise SystemExit(r.stdout)
(D/'STACK-PINS.json').write_text(json.dumps({'development_only':True,'entries':entries,'runs':runs},indent=2)+'\n');print('PASS combined frozen development stack',len(spec))
