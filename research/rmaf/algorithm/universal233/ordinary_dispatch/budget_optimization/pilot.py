#!/usr/bin/env python3
"""One-shot task-specific capped compiler; never rebuilds licensed dependency modules."""
from pathlib import Path
import datetime,gzip,hashlib,json,os,shutil,signal,subprocess,sys,threading,time
D=Path(__file__).resolve().parent; R=D.parents[5]
C=R/'results/algorithm-universal233-fast-ordinary-recursion-replay-20261015T205325296780Z'
B=D/'build'; B.mkdir(exist_ok=True)
(B/'lean-toolchain').write_bytes((C/'lean-toolchain').read_bytes())
O=R/'results'/('algorithm-universal233-budget-optimization-pilot-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'));O.mkdir()
rec={'status':'RUNNING_AUTHOR','runs':[],'dependency_rebuilds':0,'independent_acceptance':False}
for n in sys.argv[1:]:
 assert not (C/(n+'.lean')).exists(),'REFUSE_DEPENDENCY_REBUILD'
 assert shutil.disk_usage(O).free>=3*1024**3,'DISK_FLOOR_3GIB'
 s=(D/(n+'.lean')).read_bytes();(B/(n+'.lean')).write_bytes(s);(O/(n+'.lean')).write_bytes(s)
 start=time.monotonic();p=subprocess.Popen([str(R/'bootloops-lean'),'-o',str(B/(n+'.olean')),str(B/(n+'.lean'))],cwd=B,env=dict(os.environ,LEAN_PATH=str(B)+':'+str(C)),stdout=subprocess.PIPE,stderr=subprocess.STDOUT,start_new_session=True)
 stop=threading.Event();reasons=[]
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
 gzip.open(O/(n+'.log.gz'),'wb').write(out)
 rec['runs'].append({'module':n,'source_sha256':hashlib.sha256(s).hexdigest(),'exit':p.returncode,'seconds':time.monotonic()-start,'stop_reasons':reasons})
 rec['status']='PASS_AUTHOR_PILOT' if p.returncode==0 and not reasons else 'FAIL_RETAINED'
 (O/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n')
 print(n,p.returncode,out.decode(errors='replace')[-10000:],flush=True)
 if p.returncode or reasons:print(O);sys.exit(p.returncode or 125)
print(O)
