#!/usr/bin/env python3
"""One-shot preproof execution; exact known answers are handwritten in GroupControls."""
from pathlib import Path
import datetime,hashlib,json,os,subprocess,time
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[4]
OUT=HERE/'build'
records=json.loads((HERE/'STACK-PINS.json').read_text())['entries']
for name in ['GroupControls','FalseGroupControls']:
 (OUT/(name+'.lean')).write_bytes((HERE/(name+'.lean')).read_bytes())
pins={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [HERE/'TARGET-v1.md',HERE/'CONTROLS-v1.md',HERE/'GroupControls.lean',HERE/'FalseGroupControls.lean',Path(__file__),HERE/'prepare.py']}
(HERE/'CONTROLS-PIN-v1.json').write_text(json.dumps(dict(created_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),pins=pins,expected_false=3),indent=2)+'\n')
result=dict(started_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),builds=[],status='RUNNING',all_three_main_milestones='OPEN')
env=dict(os.environ,LEAN_PATH=str(OUT))
for rec in records+[dict(module='GroupControls')]:
 n=rec['module']; start=time.monotonic()
 p=subprocess.run([str(ROOT/'bootloops-lean'),'-o',str(OUT/(n+'.olean')),str(OUT/(n+'.lean'))],cwd=OUT,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=60)
 (OUT/(n+'.log')).write_text(p.stdout)
 result['builds'].append(dict(module=n,returncode=p.returncode,seconds=time.monotonic()-start))
 assert p.returncode==0,(n,p.stdout)
p=subprocess.run([str(ROOT/'bootloops-lean'),str(OUT/'FalseGroupControls.lean')],cwd=OUT,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=60)
(OUT/'FalseGroupControls.log').write_text(p.stdout)
assert p.returncode!=0 and p.stdout.count('is false')==3,p.stdout
result.update(status='PASS_PREPROOF',positive='ALL_KERNEL_DECIDE_ACCEPTED',negative='THREE_OF_THREE_REJECTED',pin_sha256=hashlib.sha256((HERE/'CONTROLS-PIN-v1.json').read_bytes()).hexdigest())
(OUT/'preproof-controls-receipt.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
