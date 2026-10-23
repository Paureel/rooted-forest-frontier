#!/usr/bin/env python3
"""One-shot source-only exact release rebuild, checkpointed per module."""
import argparse,hashlib,json,os,pathlib,subprocess,time
HERE=pathlib.Path(__file__).resolve().parent; ROOT=HERE.parents[5]; BUILD=HERE/'isolated'; LEAN=ROOT/'.runtime/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean'
p=argparse.ArgumentParser();p.add_argument('--pilot',action='store_true');a=p.parse_args()
manifest=json.loads((HERE/'release-integrity-v1.json').read_text()); modules=manifest['formalModules']; out=HERE/'build-v1.json'; logs=HERE/'build-logs';logs.mkdir(exist_ok=True)
records=json.loads(out.read_text())['records'] if out.exists() else []
assert len(records)<=len(modules)
for r,m in zip(records,modules):
 assert r['module']==m['module'] and r['exit']==0
 assert hashlib.sha256((BUILD/(r['module']+'.lean')).read_bytes()).hexdigest()==m['sha256']
end=3 if a.pilot else len(modules)
for m in modules[len(records):end]:
 n=m['module']; path=BUILD/(n+'.lean'); assert hashlib.sha256(path.read_bytes()).hexdigest()==m['sha256']
 t=time.perf_counter();r=subprocess.run([str(LEAN),'-o',n+'.olean',n+'.lean'],cwd=BUILD,env={**os.environ,'LEAN_PATH':str(BUILD)},stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=60)
 (logs/(n+'.log')).write_text(r.stdout); rec={'module':n,'exit':r.returncode,'seconds':time.perf_counter()-t,'sourceSHA256':m['sha256'],'oleanSHA256':hashlib.sha256((BUILD/(n+'.olean')).read_bytes()).hexdigest() if (BUILD/(n+'.olean')).exists() else None}; records.append(rec)
 out.write_text(json.dumps({'status':'BUILD-PILOT' if len(records)<len(modules) else 'BUILD-COMPLETE','expectedModules':len(modules),'completedModules':sum(r['exit']==0 for r in records),'scientificOleansCopied':False,'records':records},indent=2)+'\n')
 print(json.dumps(rec),flush=True)
 assert r.returncode==0,r.stdout
print(json.dumps({'status':'PILOT-PASS' if a.pilot else 'REBUILD-PASS','completed':len(records),'seconds':sum(r['seconds'] for r in records)}))
