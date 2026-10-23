#!/usr/bin/env python3
"""One-shot timed pilot for fresh Std-only origin audit instrument."""
import json
import os
from pathlib import Path
import subprocess
import time

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[5]
TOY=HERE/'toy-src'
env={**os.environ,'LEAN_PATH':str(TOY)}
rows=[]
for label,cmd in [
    ('clean-compile',[str(ROOT/'bootloops-lean'),'-o','Clean.olean','Clean.lean']),
    ('origin-audit',[str(ROOT/'bootloops-lean'),'--run',str(HERE/'origin_audit_v2.lean'),
                     'Clean',str(HERE/'toy-clean-pilot-v2.json'),'Clean'])]:
    start=time.perf_counter()
    try:
        result=subprocess.run(cmd,cwd=TOY,env=env,text=True,capture_output=True,timeout=30)
        row={'label':label,'command':cmd,'returncode':result.returncode,
             'seconds':time.perf_counter()-start,'stdout':result.stdout,'stderr':result.stderr}
    except subprocess.TimeoutExpired as exc:
        row={'label':label,'command':cmd,'returncode':'TIMEOUT','seconds':time.perf_counter()-start,
             'stdout':str(exc.stdout),'stderr':str(exc.stderr)}
    rows.append(row)
    (HERE/'toy-pilot-v2.json').write_text(json.dumps(rows,indent=2)+'\n')
    print(json.dumps(row))
    if row['returncode']!=0:
        raise SystemExit(1)
