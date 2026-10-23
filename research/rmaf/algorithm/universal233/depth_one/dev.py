#!/usr/bin/env python3
"""One-shot development harness, not an independent certification route."""
from pathlib import Path
import datetime, os, subprocess, sys, time
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
BUILD = HERE/'build'
env = dict(os.environ,LEAN_PATH=str(BUILD))
history=HERE/'development-history'/datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
history.mkdir(parents=True,exist_ok=False)
for name in sys.argv[1:]:
    local = HERE/(name+'.lean')
    if local.exists(): (BUILD/(name+'.lean')).write_bytes(local.read_bytes())
    (history/(name+'.lean')).write_bytes((BUILD/(name+'.lean')).read_bytes())
    start=time.monotonic()
    p=subprocess.run([str(ROOT/'bootloops-lean'),'-o',str(BUILD/(name+'.olean')),str(BUILD/(name+'.lean'))],
      cwd=BUILD,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=60)
    (HERE/(name+'-dev.log')).write_text(p.stdout)
    (history/(name+'.log')).write_text(p.stdout)
    print(name,p.returncode,round(time.monotonic()-start,3),p.stdout[-800:] if p.returncode else '')
    if p.returncode: sys.exit(p.returncode)
