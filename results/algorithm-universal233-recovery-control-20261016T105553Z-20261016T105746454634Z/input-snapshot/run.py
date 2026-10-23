#!/usr/bin/env python3
"""One-shot continuation wrapper for retained Lean sources; no dependency rebuild."""
from pathlib import Path
import datetime,gzip,hashlib,json,os,shutil,signal,subprocess,sys,threading,time
sys.dont_write_bytecode=True
D=Path(__file__).resolve().parent;A=D;R=D.parents[5]
C=R/'results/algorithm-universal233-forest-check-root-20261015T211023Z'
F=R/'results/algorithm-universal233-fast-ordinary-recursion-replay-20261015T205325296780Z'
E=R/'results/algorithm-universal233-early-resume-20261016T083330Z-20261016T083634190186Z'
B=R/'results/algorithm-universal233-budget-optimization-replay-20261015T213529360638Z'
W=R/'results/algorithm-universal233-optimizer-local-20261016T085144Z-20261016T085502958188Z'
S=R/'results/algorithm-universal233-recovery-source-20261016T092054Z-20261016T092457019053Z'
V=R/'results/algorithm-universal233-recovery-scalar-20261016T095748Z-20261016T100125837782Z'
I=R/'results/algorithm-universal233-recovery-initial-20261016T103025Z-20261016T103331813592Z'
mods=[]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
if len(sys.argv)>1 and sys.argv[1]=='prepare':
 O=R/os.environ['RECOVERY_CONTROL_RECEIPT'] if 'RECOVERY_CONTROL_RECEIPT' in os.environ else R/'results'/('algorithm-universal233-recovery-control-20261016T105553Z-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'));O.mkdir()
 if 'RECOVERY_CONTROL_RECEIPT' not in os.environ:(D/'ACTIVE-v1.json').write_text(json.dumps({'receipt':str(O.relative_to(R))},indent=2)+'\n')
 (O/'lean-toolchain').write_bytes((B/'lean-toolchain').read_bytes())
 print(O);sys.exit()
O=R/os.environ['RECOVERY_CONTROL_RECEIPT'] if 'RECOVERY_CONTROL_RECEIPT' in os.environ else R/json.loads((D/'ACTIVE-v1.json').read_text())['receipt']
def run(n,want=0):
 assert n in mods or n.startswith('RC'),'REFUSE_DEPENDENCY_REBUILD|'+n
 assert shutil.disk_usage(O).free>=3*1024**3
 pth=O/(n+'.lean');original=D/(n+'.lean');
 if original.exists():pth.write_bytes(original.read_bytes())
 s=pth.read_bytes();stamp=str(time.time_ns());(O/(n+'-'+stamp+'.source.lean')).write_bytes(s);start=time.monotonic();reasons=[]
 p=subprocess.Popen([str(R/'bootloops-lean'),'-M3072','-o',str(O/(n+'.olean')),str(pth)],cwd=O,env=dict(os.environ,LEAN_PATH=':'.join(map(str,[O,I,V,S,W,E,B,C]))),stdout=subprocess.PIPE,stderr=subprocess.STDOUT,start_new_session=True)
 stop=threading.Event()
 def watch():
  while not stop.wait(.1):
   if time.monotonic()-start>30 or shutil.disk_usage(O).free<3*1024**3:
    reasons.append('TIME_30S_OR_DISK_FLOOR_3GIB')
    try:os.killpg(p.pid,signal.SIGTERM)
    except ProcessLookupError:pass
    return
 th=threading.Thread(target=watch,daemon=True);th.start()
 try:out,_=p.communicate(timeout=35)
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
