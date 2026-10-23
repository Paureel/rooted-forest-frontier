#!/usr/bin/env python3
"""One-shot proof controls and completed-source receipt, author development."""
from pathlib import Path
import hashlib,json,datetime,subprocess,os,time,shutil
D=Path(__file__).resolve().parent;R=D.parents[4]
O=R/'results'/('algorithm-ordinary-dispatch-forest-min-completion-precontrols-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'));O.mkdir()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
M=R/'research/rmaf/algorithm/universal233/forest_solver/FOREST-SOLVER-MANIFEST-v3.json'
assert sha(M)=='89937a6f71bceb2dbeb64917b4b805e8f193fa485b00ec28acecdc95d047dcf5'
rows=json.loads(M.read_text())['immutable_files']
for e in rows:
 p=R/e['path'];assert sha(p)==e['sha256'],e['path']
C=R/'results/algorithm-universal233-forest-solver-20261015T114224630584Z'
rec=dict(status='RUNNING',input_pins={},runs=[],prior_immutable_files=len(rows),independence='AUTHOR DEVELOPMENT')
for p in [D/'TARGET-v1.md',D/'CONTROLS-PIN-v1.md',D/'MinPrecontrols.lean',D/'MinPreFalse.lean',Path(__file__),M,C/'certificate.json']:
 rec['input_pins'][str(p.relative_to(R))]=sha(p)
def save():(O/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n')
save()
for n in ['MinPrecontrols','MinPreFalse']:shutil.copyfile(D/(n+'.lean'),O/(n+'.lean'))
shutil.copyfile(C/'lean-toolchain',O/'lean-toolchain');env=dict(os.environ,LEAN_PATH=str(O)+':'+str(C))
for n,want in [('MinPrecontrols',0),('MinPreFalse',1)]:
 args=[str(R/'bootloops-lean')]
 if n=='MinPrecontrols':args+=['-o',str(O/(n+'.olean'))]
 args +=[str(O/(n+'.lean'))];start=time.monotonic()
 p=subprocess.run(args,cwd=O,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=30)
 (O/(n+'.log')).write_text(p.stdout);rec['runs'].append(dict(module=n,exit=p.returncode,seconds=time.monotonic()-start));save()
 assert p.returncode==want,(n,p.stdout)
 if want:assert p.stdout.count('is false')==4
rec['status']='PASS_PREPROOF_CONTROLS';save();print(rec['status'],rec['runs'],O)
