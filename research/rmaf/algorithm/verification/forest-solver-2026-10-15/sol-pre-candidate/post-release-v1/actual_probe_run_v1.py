#!/usr/bin/env python3
"""Timed bounded actual-call pilot/full driver; fixture mocks stay explicit."""
import json
import os
from pathlib import Path
import subprocess
import sys
import time
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[6]
BUILD=HERE/'isolated-build-v1'
mode=sys.argv[1]
out=HERE/('actual-probe-'+mode+'-v3.json')
check=HERE/('actual-check-'+mode+'-v2.json')
env={**os.environ,'LEAN_PATH':str(BUILD)}
commands=[
 [str(ROOT/'bootloops-lean'),'--run',str(HERE/'ActualProbe-v3.lean'),mode,str(out)],
 [str(ROOT/'bootloops-python'),str(HERE/'check_actual_probe_v2.py'),str(out),str(check)]]
result={'mode':mode,'commands':[]}
try:
    for cmd in commands:
        started=time.perf_counter()
        p=subprocess.run(cmd,cwd=BUILD,env=env,text=True,capture_output=True,timeout=30)
        result['commands'].append({'command':cmd,'returncode':p.returncode,'seconds':time.perf_counter()-started,
            'stdout':p.stdout,'stderr':p.stderr,'cwd':str(BUILD),'LEAN_PATH':str(BUILD)})
        assert p.returncode==0,'actual probe/graph adapter failure'
    assert json.loads(check.read_text())['passed']
    result['passed']=True
except Exception as exc:
    result['passed']=False;result['failure']=repr(exc);raise
finally:(HERE/('actual-probe-run-'+mode+'-v1.json')).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'passed':True,'mode':mode,'seconds':[r['seconds'] for r in result['commands']]}))
