#!/usr/bin/env python3
"""One-shot continuation wrapper for retained Lean sources; no dependency rebuild."""
from pathlib import Path
import datetime,gzip,hashlib,json,os,shutil,signal,subprocess,sys,threading,time
sys.dont_write_bytecode=True
D=Path(__file__).resolve().parent; A=D.parent; R=A.parents[5]
C=R/'results/algorithm-universal233-forest-check-root-20261015T211023Z'
F=R/'results/algorithm-universal233-fast-ordinary-recursion-replay-20261015T205325296780Z'
mods=['ELPrimitives','ELGeometry','ELPretest','ELPretestBounds','ELCherry','ELRule4Primitives','ELRule4Guards','ELRule4Raw','ELEarly','ELOuter']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
if len(sys.argv)>1 and sys.argv[1]=='prepare':
 O=R/os.environ['EARLY_RESUME_RECEIPT'] if 'EARLY_RESUME_RECEIPT' in os.environ else R/'results'/('algorithm-universal233-early-resume-20261016T083330Z-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'));O.mkdir()
 if 'EARLY_RESUME_RECEIPT' not in os.environ:(D/'ACTIVE-v1.json').write_text(json.dumps({'receipt':str(O.relative_to(R))},indent=2)+'\n')
 (O/'lean-toolchain').write_bytes((C/'lean-toolchain').read_bytes())
 # Add only completed licensed dependency modules absent from the readonly checker closure.
 copied=[];seen=set()
 def dep(n):
  if n in seen or (C/(n+'.olean')).exists():return
  seen.add(n);p=F/(n+'.lean');q=F/(n+'.olean');assert p.exists() and q.exists(),n
  for line in p.read_text().splitlines():
   if line.startswith('import '):
    for v in line[7:].split():dep(v)
  for x in [p,q]:
   y=O/x.name;y.write_bytes(x.read_bytes());y.chmod(0o444);copied.append({'original':str(x.relative_to(R)),'snapshot':str(y.relative_to(R)),'sha256':sha(x),'mode':oct(x.stat().st_mode&0o777),'inode':x.stat().st_ino,'device':x.stat().st_dev})
 dep('EarlyControls')
 (O/'DEPENDENCY-SNAPSHOTS-v1.json').write_text(json.dumps(copied,indent=2)+'\n')
 for n in mods:(O/(n+'.lean')).write_bytes((A/(n+'.lean')).read_bytes())
 for n in ['ERInterface','ERControls','ERFalseControls']:(O/(n+'.lean')).write_bytes((D/(n+'.lean')).read_bytes())
 print(O);sys.exit()
O=R/os.environ['EARLY_RESUME_RECEIPT'] if 'EARLY_RESUME_RECEIPT' in os.environ else R/json.loads((D/'ACTIVE-v1.json').read_text())['receipt']
def run(n,want=0):
 assert n in mods or n.startswith('ER'),'REFUSE_DEPENDENCY_REBUILD|'+n
 assert shutil.disk_usage(O).free>=3*1024**3
 pth=O/(n+'.lean');s=pth.read_bytes();stamp=str(time.time_ns());(O/(n+'-'+stamp+'.source.lean')).write_bytes(s);start=time.monotonic();reasons=[]
 p=subprocess.Popen([str(R/'bootloops-lean'),'-M3072','-o',str(O/(n+'.olean')),str(pth)],cwd=O,env=dict(os.environ,LEAN_PATH=str(O)+':'+str(C)),stdout=subprocess.PIPE,stderr=subprocess.STDOUT,start_new_session=True)
 stop=threading.Event()
 def watch():
  while not stop.wait(.1):
   if time.monotonic()-start>60 or shutil.disk_usage(O).free<3*1024**3:
    reasons.append('TIME_60S_OR_DISK_FLOOR_3GIB')
    try:os.killpg(p.pid,signal.SIGTERM)
    except ProcessLookupError:pass
    return
 th=threading.Thread(target=watch,daemon=True);th.start()
 try:out,_=p.communicate(timeout=65)
 finally:stop.set();th.join()
 assert len(out)<=16*1024**2,'OUTPUT_CAP'
 log=O/(n+'-'+stamp+'.log.gz');gzip.open(log,'wb').write(out)
 rr={'module':n,'source_sha256':hashlib.sha256(s).hexdigest(),'exit':p.returncode,'want':want,'seconds':time.monotonic()-start,'stop_reasons':reasons,'log':str(log.relative_to(R)),'log_sha256':sha(log)}
 (O/(n+'-'+stamp+'.run.json')).write_text(json.dumps(rr,indent=2)+'\n')
 assert p.returncode==want and not reasons,(n,p.returncode,out.decode(errors='replace')[-5000:])
 return out.decode(errors='replace')
if __name__=='__main__':
 for n in sys.argv[1:]:print(n,run(n)[-1500:],flush=True)
 print(O)
