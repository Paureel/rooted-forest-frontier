#!/usr/bin/env python3
"""Fresh original producer module names, using only fresh local pinned dependencies."""
from pathlib import Path
import argparse,hashlib,json,os,subprocess,time
P=Path(__file__).resolve().parent;A=P/'producer-origin';ROOT=Path('/Users/paurel/Documents/ChatGPT/bootscience');LEAN=ROOT/'.runtime/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean'
ap=argparse.ArgumentParser();ap.add_argument('module');a=ap.parse_args();s=A/'src'/(a.module+'.lean');b=A/'build'/(a.module+'.olean');env=os.environ.copy();env['LEAN_PATH']=str(A/'build')+':'+str(P/'build');st=time.perf_counter();r=subprocess.run([str(LEAN),'-o',str(b),s.name],cwd=s.parent,env=env,capture_output=True,text=True,timeout=55);log=P/'logs'/('producer-v2-'+a.module+'.log');log.write_text(r.stdout+r.stderr)
o={'module':a.module,'seconds':time.perf_counter()-st,'exit_code':r.returncode,'source_sha256':hashlib.sha256(s.read_bytes()).hexdigest(),'log':str(log.relative_to(P)),'all_pass':r.returncode==0,'copied_scientific_oleans':0,'LEAN_PATH':env['LEAN_PATH']}
if b.is_file():o['olean_sha256']=hashlib.sha256(b.read_bytes()).hexdigest()
(P/('producer-v2-'+a.module+'.json')).write_text(json.dumps(o,indent=2)+'\n');print(json.dumps(o,indent=2));print(r.stdout[:2500]if r.returncode else'');raise SystemExit(r.returncode)
