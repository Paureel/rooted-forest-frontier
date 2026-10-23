#!/usr/bin/env python3
"""Measured source-only isolated build; each native compile has a bounded timeout."""
from pathlib import Path
import argparse,hashlib,json,os,subprocess,time
P=Path(__file__).resolve().parent;ROOT=Path('/Users/paurel/Documents/ChatGPT/bootscience');LEAN=ROOT/'.runtime/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean'
info=json.loads((P/'source-integrity-v1.json').read_text());order=info['positive_order']
ap=argparse.ArgumentParser();ap.add_argument('stage',choices=['pilot','remaining']);a=ap.parse_args();rows=[];st=time.perf_counter()
if a.stage=='remaining':
 old=json.loads((P/'build-pilot-v1.json').read_text())
 if not old['all_pass']:raise SystemExit('Pilot failed')
mods=order[:2]if a.stage=='pilot'else order[2:]
env=os.environ.copy();env['LEAN_PATH']=str(P/'build')
try:
 for n in mods:
  src=P/'src'/(n+'.lean');dest=P/'build'/(n+'.olean');t=time.perf_counter();cmd=[str(LEAN),'-o',str(dest),src.name]
  run=subprocess.run(cmd,cwd=src.parent,env=env,text=True,capture_output=True,timeout=55);secs=time.perf_counter()-t
  log=P/'logs'/('build-'+n+'.log');log.write_text(run.stdout+run.stderr)
  row={'module':n,'command':cmd,'seconds':secs,'exit_code':run.returncode,'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'log':str(log.relative_to(P))}
  if dest.is_file():row['olean_sha256']=hashlib.sha256(dest.read_bytes()).hexdigest()
  rows.append(row)
  (P/('build-'+a.stage+'-progress.json')).write_text(json.dumps(rows,indent=2)+'\n')
  if run.returncode:raise RuntimeError('Scientific build failed '+n)
 out={'stage':a.stage,'executions':rows,'execution_count':len(rows),'seconds':time.perf_counter()-st,'all_pass':all(r['exit_code']==0for r in rows),'copied_scientific_oleans':0,'native_lean_version':subprocess.check_output([str(LEAN),'--version'],text=True).strip(),'native_lean_sha256':hashlib.sha256(LEAN.read_bytes()).hexdigest()}
 (P/('build-'+a.stage+'-v1.json')).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k!='executions'},indent=2))
except Exception as ex:
 (P/('build-'+a.stage+'-FAILURE.json')).write_text(json.dumps({'failure':repr(ex),'completed':rows,'seconds':time.perf_counter()-st},indent=2)+'\n');raise
