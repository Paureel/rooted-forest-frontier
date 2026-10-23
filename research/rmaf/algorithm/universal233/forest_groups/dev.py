#!/usr/bin/env python3
"""One-shot measured Lean development build, preserving every failed attempt."""
from pathlib import Path
import datetime,os,subprocess,sys,time
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[4]
OUT=HERE/'build'
for n in sys.argv[1:]:
 (OUT/(n+'.lean')).write_bytes((HERE/(n+'.lean')).read_bytes())
 stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
 start=time.monotonic()
 p=subprocess.run([str(ROOT/'bootloops-lean'),'-o',str(OUT/(n+'.olean')),str(OUT/(n+'.lean'))],cwd=OUT,env=dict(os.environ,LEAN_PATH=str(OUT)),text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=60)
 (HERE/(n+'-'+stamp+'.log')).write_text(p.stdout)
 print(n,p.returncode,round(time.monotonic()-start,4));print(p.stdout)
 if p.returncode:sys.exit(p.returncode)
