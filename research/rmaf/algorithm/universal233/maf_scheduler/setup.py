"""Copy completed source inputs, retaining exact filename/import-only adapters."""
from pathlib import Path
import hashlib,json,re,os,subprocess,time
D=Path(__file__).resolve().parent;R=D.parents[4];U=D.parent;B=D/'build';B.mkdir(exist_ok=True)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifests=[U/'depth_one/DEPTH-ONE-MANIFEST-v1.json',U/'query_scheduler/QUERY-SCHEDULER-MANIFEST-v1.json',U/'restriction_bridge/RESTRICTION-MANIFEST-v1.json']
checks=[]
for p in manifests:
 m=json.loads(p.read_text());rows=m.get('immutable_files')
 if rows is None:rows=[{'path':k,'sha256':v} for k,v in m.get('owned_files',{}).items()]
 for e in rows:assert sha(R/e['path'])==e['sha256'],e['path']
 checks.append({'path':str(p.relative_to(R)),'sha256':sha(p),'entries_checked':len(rows)})
entries=[]
def add(module,path,old_import=None,new_import=None):
 data=path.read_text()
 if old_import:
  assert data.startswith('import '+old_import+'\n')
  data=data.replace('import '+old_import+'\n','import '+new_import+'\n',1)
 (B/(module+'.lean')).write_text(data)
 entries.append({'module':module,'source':str(path.relative_to(R)),'original_sha256':sha(path),'copy_sha256':sha(B/(module+'.lean')),'first_import_adapter':([old_import,new_import] if old_import else None)})
for e in json.loads((U/'depth_one/STACK-PINS.json').read_text())['entries']:
 p=R/e['path'];assert sha(p)==e['sha256'];add(e['module'],p)
for n in ['Pretest','Controls','Lemmas','Reconstruction01','Optimality01','Witness01','Runtime01','ConsumerControls','SourceColorControls']:
 add(n,U/'depth_one'/(n+'.lean'))
for n in ['Cost','Forward','Reconstruction']:
 add('RestrictionCost' if n=='Cost' else n,U/'restriction_bridge'/(n+'.lean'),'Cost' if n=='Forward' else None,'RestrictionCost' if n=='Forward' else None)
qs=['Caller','Specification','Budgets','Mass','Work']
for i,n in enumerate(qs):add('Query'+n,U/'query_scheduler'/(n+'.lean'),qs[i-1] if i else None,'Query'+qs[i-1] if i else None)
assert len(set(e['module'] for e in entries))==len(entries)
(D/'SOURCE-PINS-v1.json').write_text(json.dumps({'completed_manifests':checks,'entries':entries,'adapter_scope':'Only module filename and first import; all proof bodies unchanged. Namespace declarations retain original identities.'},indent=2)+'\n')
runs=[]
for e in entries:
 n=e['module'];st=time.monotonic();p=subprocess.run([str(R/'bootloops-lean'),'-o',str(B/(n+'.olean')),str(B/(n+'.lean'))],cwd=R,env=dict(os.environ,LEAN_PATH=str(B)),text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=30)
 (B/(n+'.log')).write_text(p.stdout);runs.append({'module':n,'exit':p.returncode,'seconds':time.monotonic()-st})
 (D/'SETUP-v1.json').write_text(json.dumps(runs,indent=2)+'\n')
 assert p.returncode==0,(n,p.stdout)
print('PASS completed-source assembly',len(entries),'modules')
