"""One-shot exact-source compile receipts for the actual paid child consumer."""
from pathlib import Path
import hashlib,json,os,subprocess,time
D=Path(__file__).resolve().parent;R=D.parents[5];B=R/'results/algorithm-universal233-ordinary-child-binding-20261015T182851721674Z'
rec=[]
for n,want in [('PaidChildren',0),('ChildConsumerControls',0),('ChildConsumerFalseControls',1)]:
 p=D/(n+'.lean');h=hashlib.sha256(p.read_bytes()).hexdigest();(B/(n+'.lean')).write_bytes(p.read_bytes());start=time.monotonic()
 run=subprocess.run([str(R/'bootloops-lean')]+(['-o',str(B/(n+'.olean'))] if want==0 else [])+[str(B/(n+'.lean'))],cwd=B,env=dict(os.environ,LEAN_PATH=str(B)),stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=30)
 (D/(n+'-controls-v2.log')).write_text(run.stdout);rec.append(dict(module=n,source_sha256=h,exit=run.returncode,expected_exit=want,seconds=time.monotonic()-start));(D/'CHILD-COMPILE-CONTROLS-v2.json').write_text(json.dumps(rec,indent=2)+'\n')
 assert run.returncode==want,(n,run.stdout[-6000:])
 if want:assert run.stdout.count('error:')==2 and run.stdout.count('unsolved goals')==2
 assert hashlib.sha256(p.read_bytes()).hexdigest()==h
print('PASS_AUTHOR_PAID_CHILD_CONSUMER_CONTROLS;2falseclaimsrejected')
