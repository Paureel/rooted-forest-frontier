#!/usr/bin/env python3
"""One-shot 30s module pilot retaining stdout and every failure."""
from pathlib import Path
import datetime,json,os,shutil,subprocess,sys,time
D=Path(__file__).resolve().parent;R=D.parents[4];B=D/'build'
O=R/'results'/('algorithm-universal233-rule5-paid-selector-pilot-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'));O.mkdir()
rec=dict(status='RUNNING',runs=[],author_development=True)
for n in sys.argv[1:]:
 assert shutil.disk_usage(O).free>=3*1024**3,'DISK_FLOOR_3GIB'
 (B/(n+'.lean')).write_bytes((D/(n+'.lean')).read_bytes());start=time.monotonic()
 try:
  p=subprocess.run([str(R/'bootloops-lean'),'-o',str(B/(n+'.olean')),str(B/(n+'.lean'))],cwd=B,env=dict(os.environ,LEAN_PATH=str(B)),text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=30);code=p.returncode;out=p.stdout
 except subprocess.TimeoutExpired as e:code=124;out=str(e.stdout or '')+'\nPILOT_TIMEOUT_30S\n'
 (O/(n+'.log')).write_text(out);rec['runs'].append(dict(module=n,exit=code,seconds=time.monotonic()-start));(O/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n');print(n,code,out[-7000:],flush=True)
 if code:rec['status']='FAIL_RETAINED';(O/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n');print(O);sys.exit(code)
rec['status']='PASS_AUTHOR_PILOT';(O/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n');print(O)
