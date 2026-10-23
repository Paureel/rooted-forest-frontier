#!/usr/bin/env python3
"""Pinned preproof actual controls; universal author proofs do not yet exist."""
from pathlib import Path
import hashlib,json,os,subprocess,time,datetime
D=Path(__file__).resolve().parent;R=D.parents[4];B=D/'build'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
rec=dict(stage='BEFORE_NEW_UNIVERSAL_PROOFS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),files={n:sha(D/n) for n in ['TARGET-v1.md','CONTROLS-PIN-v1.json','ForestDefs.lean','ForestPrecontrols.lean','FalseForestControls.lean']},runs=[])
for n,s in [('TrueControl','import Std\nexample : 2+3=5 := by decide\n'),('FalseControl','import Std\nexample : 2+3=6 := by decide\n')]: (B/(n+'.lean')).write_text(s)
for n in ['ForestDefs','ForestPrecontrols','FalseForestControls']:(B/(n+'.lean')).write_bytes((D/(n+'.lean')).read_bytes())
for n,build,k in [('TrueControl',False,0),('FalseControl',False,1),('ForestDefs',True,0),('ForestPrecontrols',True,0),('FalseForestControls',False,2)]:
 t=time.monotonic();p=subprocess.run([str(R/'bootloops-lean')]+(['-o',str(B/(n+'.olean'))] if build else [])+[str(B/(n+'.lean'))],cwd=B,env=dict(os.environ,LEAN_PATH=str(B)),capture_output=True,text=True,timeout=60)
 log=p.stdout+p.stderr;(B/(n+'-preproof.log')).write_text(log);rec['runs'].append(dict(module=n,exit=p.returncode,false_count=log.count('is false'),seconds=time.monotonic()-t))
 (D/'PREPROOF-ATTEMPT.json').write_text(json.dumps(rec,indent=2)+'\n')
 assert (p.returncode==0 if k==0 else p.returncode!=0 and log.count('is false')==k),(n,log)
rec.update(status='PASS_PREPROOF',positive_actual_controls=6,false_actual_claims_rejected=2,independent_acceptance=False)
(D/'PREPROOF-RECEIPT-v1.json').write_text(json.dumps(rec,indent=2)+'\n')
print('PASS preproof: 6 actual controls; 2 false extensions rejected; true/false harness passed')
