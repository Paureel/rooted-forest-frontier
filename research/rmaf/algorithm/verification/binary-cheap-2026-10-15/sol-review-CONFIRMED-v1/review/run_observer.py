#!/usr/bin/env python3
"""Compile a reviewer-only readout/audit helper; retain stdout and diagnostics."""
from pathlib import Path
import argparse,hashlib,json,os,subprocess,time
P=Path(__file__).resolve().parent;ROOT=Path('/Users/paurel/Documents/ChatGPT/bootscience');LEAN=ROOT/'.runtime/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean'
ap=argparse.ArgumentParser();ap.add_argument('module');ap.add_argument('--stage',default='observer');a=ap.parse_args();src=P/'src'/(a.module+'.lean');dst=P/'build'/(a.module+'.olean');env=os.environ.copy();env['LEAN_PATH']=str(P/'build');st=time.perf_counter();cmd=[str(LEAN),'-o',str(dst),src.name]
r=subprocess.run(cmd,cwd=src.parent,env=env,text=True,capture_output=True,timeout=55)
log=P/'logs'/(a.stage+'-'+a.module+'.log');log.write_text(r.stdout+r.stderr)
row={'module':a.module,'command':cmd,'seconds':time.perf_counter()-st,'exit_code':r.returncode,'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'log':str(log.relative_to(P)),'all_pass':r.returncode==0}
if dst.is_file():row['olean_sha256']=hashlib.sha256(dst.read_bytes()).hexdigest()
(P/(a.stage+'-'+a.module+'.json')).write_text(json.dumps(row,indent=2)+'\n');print(json.dumps(row,indent=2));print(r.stdout[:3500]if r.returncode else '')
raise SystemExit(r.returncode)
