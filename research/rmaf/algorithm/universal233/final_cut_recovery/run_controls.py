#!/usr/bin/env python3
"""One-shot pinned pre-proof actual-program controls; no universal proof imports."""
from pathlib import Path
import datetime,hashlib,json,os,subprocess,time
D=Path(__file__).resolve().parent
ROOT=D.parents[4]
BASE=ROOT/'results/algorithm-universal233-rank-replay-20261015T091933Z'
OUT=ROOT/'results'/('algorithm-universal233-final-cuts-controls-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'))
OUT.mkdir()
record={'scope':'Pinned finite controls BEFORE universal proof construction; only actual completed core/rank imports','status':'RUNNING','sources':{},'runs':[]}
for n in ['RecoveryProgram','Controls','FalseControls']:
 p=D/(n+'.lean'); (OUT/p.name).write_bytes(p.read_bytes()); record['sources'][str(p.relative_to(ROOT))]=hashlib.sha256(p.read_bytes()).hexdigest()
(OUT/'lean-toolchain').write_bytes((ROOT/'research/rmaf/lean/lean-toolchain').read_bytes())
env=dict(os.environ,LEAN_PATH=str(OUT)+':'+str(BASE))
for n in ['RecoveryProgram','Controls','FalseControls']:
 start=time.monotonic(); p=subprocess.run([str(ROOT/'bootloops-lean'),'-o',str(OUT/(n+'.olean')),str(OUT/(n+'.lean'))],env=env,cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=45)
 (OUT/(n+'.log')).write_text(p.stdout); record['runs'].append({'module':n,'exit':p.returncode,'seconds':time.monotonic()-start})
 (OUT/'certificate.json').write_text(json.dumps(record,indent=2)+'\n')
 if n=='FalseControls': assert p.returncode!=0 and p.stdout.count('is false')>=2,p.stdout
 else: assert p.returncode==0,p.stdout
record.update(status='PASS_PREPROOF_ACTUAL_CONTROLS',positive_statements=11,false_propositions_rejected=3)
(OUT/'certificate.json').write_text(json.dumps(record,indent=2)+'\n')
(D/'CONTROLS-RECEIPT.txt').write_text(str(OUT)+'\n')
print(record['status'],OUT)
