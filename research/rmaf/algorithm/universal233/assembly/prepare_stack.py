"""One-shot integration adapter and development build, frozen sources unchanged.
The authors used Coverage for different modules. Only a COPY's module filename
and InitialCoverage import are adapted; every proof body remains byte-identical.
A final assembled source/axiom audit remains a separate gate.
"""
from pathlib import Path
import json,hashlib,subprocess,os,time
D=Path(__file__).resolve().parent;U=D.parent;ROOT=U.parents[3];OUT=D/'stack';OUT.mkdir(exist_ok=True)
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for f in [U/'source_coverage/SOURCE-COVERAGE-MANIFEST-v1.json',U/'cut_realization/CUT-REALIZATION-MANIFEST-v1.json']:
 m=json.loads(f.read_text())
 rows=m.get('immutable_files')
 if rows is None:rows=[{'path':k,'sha256':v} for k,v in m['owned_files'].items()]
 for row in rows:assert digest(ROOT/row['path'])==row['sha256'],row['path']
entries=[];order=[]
for package,stamp in [('source_coverage','20261015T075710Z'),('cut_realization','20261015T080042Z')]:
 p=U/package/'replay'/stamp;cert=json.loads((p/'certificate.json').read_text());mods=cert.get('module_origin_counts',cert.get('module_counts'));assert mods
 for build in cert['builds']:
  name=build['module']
  if name not in mods:continue
  source=p/(name+'.lean');assert source.exists(),source
  newname='CutCoverage' if package=='cut_realization' and name=='Coverage' else name
  data=source.read_bytes();adapter=None
  if package=='cut_realization' and name=='InitialCoverage':
   assert data.startswith(b'import Coverage\n');data=data.replace(b'import Coverage\n',b'import CutCoverage\n',1);adapter='single import module path Coverage -> CutCoverage; proof body unchanged'
  if newname in order:
   assert (OUT/(newname+'.lean')).read_bytes()==data,(package,name,'conflicting source')
  else:
   (OUT/(newname+'.lean')).write_bytes(data);order.append(newname)
  entries.append({'package':package,'module':name,'compiled_module':newname,'source':str(source.relative_to(ROOT)),'source_sha256':digest(source),'compiled_sha256':hashlib.sha256(data).hexdigest(),'adapter':adapter or ('module filename only Coverage -> CutCoverage' if newname!=name else None)})
(OUT/'lean-toolchain').write_bytes((ROOT/'research/rmaf/lean/lean-toolchain').read_bytes());env=dict(os.environ,LEAN_PATH=str(OUT));runs=[]
for name in order:
 start=time.monotonic();p=subprocess.run([str(ROOT/'bootloops-lean'),'-o',str(OUT/(name+'.olean')),str(OUT/(name+'.lean'))],cwd=ROOT,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=30);(OUT/(name+'.log')).write_text(p.stdout);runs.append({'module':name,'exit':p.returncode,'seconds':time.monotonic()-start})
 if p.returncode:
  (OUT/'FAILED.json').write_text(json.dumps({'runs':runs,'sources':entries},indent=2)+'\n');raise SystemExit(p.stdout)
(OUT/'PREPARED.json').write_text(json.dumps({'status':'PASS-development-import-stack-only','sources':entries,'order':order,'runs':runs,'modules':len(order),'scope':'All frozen original sources unchanged; renamed cut Coverage copy and InitialCoverage import only. New assembly proof/final source-bound audit pending.'},indent=2)+'\n');print('PASS adapted assembled dependency stack:',len(order),'modules, seconds',sum(x['seconds'] for x in runs))
