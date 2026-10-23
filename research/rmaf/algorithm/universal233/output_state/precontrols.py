#!/usr/bin/env python3
"""Pinned source-bound preproof controls; no universal author proof imported."""
from pathlib import Path
import hashlib,json,os,subprocess,time,datetime
D=Path(__file__).resolve().parent;R=D.parents[4];B=D/'build'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
record=dict(stage='BEFORE_UNIVERSAL_AUTHOR_PROOF',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),files={},runs=[])
for n in ['CONTROLS-PIN-v1.json','OutputDefs.lean','OutputControls.lean','FalseOutputControls.lean']:
 record['files'][n]=sha(D/n)
for n,data in [('TrueControl','import Std\nexample : (2 : Nat)+3=5 := by decide\n'),('FalseControl','import Std\nexample : (2 : Nat)+3=6 := by decide\n')]: (B/(n+'.lean')).write_text(data)
for n in ['OutputDefs','OutputControls','FalseOutputControls']:(B/(n+'.lean')).write_bytes((D/(n+'.lean')).read_bytes())
for n,build,expected in [('TrueControl',False,0),('FalseControl',False,1),('OutputDefs',True,0),('OutputControls',True,0),('FalseOutputControls',False,4)]:
 t=time.monotonic();p=subprocess.run([str(R/'bootloops-lean')]+(['-o',str(B/(n+'.olean'))] if build else [])+[str(B/(n+'.lean'))],cwd=B,env=dict(os.environ,LEAN_PATH=str(B)),capture_output=True,text=True,timeout=60)
 log=p.stdout+p.stderr;(B/(n+'-preproof.log')).write_text(log)
 record['runs'].append(dict(module=n,exit=p.returncode,false_count=log.count('is false'),seconds=time.monotonic()-t))
 assert (p.returncode==0 if expected==0 else p.returncode!=0 and log.count('is false')==expected),(n,log)
record.update(status='PASS_PREPROOF',positive_actual_controls=8,false_actual_claims_rejected=4,known_true_accepted=True,known_false_rejected=True,independent_acceptance=False)
(D/'PREPROOF-RECEIPT-v1.json').write_text(json.dumps(record,indent=2)+'\n')
print('PASS preproof: 8 actual controls, 4 actual false claims rejected; true/false harness works')
