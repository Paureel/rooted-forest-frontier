#!/usr/bin/env python3
"""Metadata only: native installed Lean import source/binary identities; no scientific import."""
from pathlib import Path
import hashlib,json,os,subprocess,time
P=Path(__file__).resolve().parent.parent;ROOT=Path('/Users/paurel/Documents/ChatGPT/bootscience');TC=ROOT/'.runtime/elan/toolchains/leanprover--lean4---v4.35.0'
def h(p):
 d=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):d.update(b)
 return d.hexdigest()
s=P/'toy-src/StdDependencyIdentity.lean';b=P/'toy-build/StdDependencyIdentity.olean';lean=TC/'bin/lean';env=os.environ.copy();env['LEAN_PATH']=str(P/'toy-build')
(P/'stdlib-identity-source-freeze-v1.json').write_text(json.dumps({'source_sha256':h(s),'instrument_sha256':h(Path(__file__)),'frozen_before_execution':True,'purpose':'installed Std/Lean binary/source identity only; library not rebuilt or reviewed'},indent=2)+'\n')
st=time.perf_counter();r=subprocess.run([str(lean),'-o',str(b),s.name],cwd=s.parent,env=env,capture_output=True,text=True,timeout=55)
(P/'logs/stdlib-dependency-identity.log').write_text(r.stdout+r.stderr)
if r.returncode:raise SystemExit('Dependency metadata compilation failed')
mods=[json.loads(z[len('STDLIB_IMPORT_JSON '):])for z in r.stdout.splitlines()if z.startswith('STDLIB_IMPORT_JSON ')]
if len(mods)!=1:raise SystemExit('Nonunique standard-library module list')
rows=[];missing=[]
for name in mods[0]:
 rel=Path(*name.split('.'));source=TC/'src/lean'/rel.with_suffix('.lean');binary=TC/'lib/lean'/rel.with_suffix('.olean')
 row={'module':name,'source':None,'binaries':[]}
 if source.is_file():row['source']={'path':str(source),'bytes':source.stat().st_size,'sha256':h(source)}
 else:missing.append({'module':name,'kind':'source','path':str(source)})
 for p in [binary,Path(str(binary)+'.private'),Path(str(binary)+'.server')]:
  if p.is_file():row['binaries'].append({'path':str(p),'bytes':p.stat().st_size,'sha256':h(p)})
 if not binary.is_file():missing.append({'module':name,'kind':'binary','path':str(binary)})
 rows.append(row)
out={'phase':'PRE-CANDIDATE ONLY','native_lean_sha256':h(lean),'native_lean_version':subprocess.check_output([str(lean),'--version'],text=True).strip(),'imported_module_count':len(rows),'entries':rows,'missing':missing,'metadata_seconds':time.perf_counter()-st,'helper_olean_sha256':h(b),'library_rebuilt':False,'library_reviewed':False,'scientific_candidate_contact':False,'CoreGraph_imported':False,'replication_increment':0}
(P/'stdlib-dependency-identity-v1.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k not in ['entries','missing']},indent=2));print('Missing identities:',len(missing))
