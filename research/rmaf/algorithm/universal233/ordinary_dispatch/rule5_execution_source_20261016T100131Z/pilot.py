#!/usr/bin/env python3
"""One-problem extension of earlier capped Rule5 pilots; immutable imports only."""
from pathlib import Path
import datetime,gzip,hashlib,json,os,shutil,signal,subprocess,sys,threading,time
D=Path(__file__).resolve().parent;R=D.parents[5];B=D/'build';B.mkdir(exist_ok=True);PATHS=[R/p for p in json.loads((D/'DEPENDENCIES-v1.json').read_text())['import_paths']];P=PATHS[2];deps=json.loads((D/'DEPENDENCIES-v1.json').read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for e in deps['entries'].values():
 for kind in ['source','olean']:assert sha(R/e[kind])==e[kind+'_sha256'],e[kind]
 assert sha(R/e['loaded_olean'])==e['loaded_sha256'],e['loaded_olean']
assert shutil.disk_usage(D).free>=3*1024**3
(B/'lean-toolchain').write_bytes((P/'lean-toolchain').read_bytes())
O=R/'results'/('algorithm-universal233-rule5-execution-20261016T100131Z-pilot-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'));O.mkdir();(D/'LAST-RUN.txt').write_text(str(O)+'\n');rec=dict(status='RUNNING_AUTHOR',runs=[])
for n in sys.argv[1:]:
 assert n not in deps['entries'],'REFUSE_DEPENDENCY_REBUILD'
 s=D/(n+'.lean');(B/s.name).write_bytes(s.read_bytes());(O/s.name).write_bytes(s.read_bytes());start=time.monotonic();reason=[];count=[0];out=[]
 cmd=[str(R/'bootloops-lean'),'-M3072','-o',str(B/(n+'.olean')),str(B/s.name)]
 p=subprocess.Popen(cmd,cwd=B,env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[B]+PATHS))),stdout=subprocess.PIPE,stderr=subprocess.STDOUT,start_new_session=True);stop=threading.Event()
 def kill(why):
  if not reason:reason.append(why)
  try:os.killpg(p.pid,signal.SIGTERM)
  except ProcessLookupError:pass
 def read():
  with gzip.open(O/(n+'.log.gz'),'wb') as f:
   while True:
    b=p.stdout.readline(16*1024**2+1)
    if not b:break
    count[0]+=len(b)
    if len(b)>16*1024**2:kill('LINE_CAP');break
    if count[0]>64*1024**2:kill('OUTPUT_CAP');break
    f.write(b);out.append(b)
 def watch():
  while not stop.wait(.1):
   if shutil.disk_usage(O).free<3*1024**3:kill('LIVE_DISK_FLOOR');return
   if sum(q.stat().st_size for q in O.iterdir() if q.is_file())>128*1024**2:kill('DIRECTORY_CAP');return
 reader=threading.Thread(target=read,daemon=True);watcher=threading.Thread(target=watch,daemon=True);reader.start();watcher.start()
 try:code=p.wait(timeout=30)
 except subprocess.TimeoutExpired:kill('TIMEOUT_30S');p.wait(timeout=5);code=124
 finally:stop.set();watcher.join();reader.join(timeout=5)
 if reason:code=125
 text=b''.join(out).decode(errors='replace')
 rec['runs'].append(dict(module=n,exit=code,seconds=time.monotonic()-start,stop=reason,raw_bytes=count[0],source_sha256=sha(s),olean_sha256=sha(B/(n+'.olean')) if code==0 else None));rec['status']='PASS_AUTHOR_PILOT' if code==0 else 'FAIL_RETAINED';(O/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n')
 print(n,code,round(rec['runs'][-1]['seconds'],3),text[-7000:],flush=True)
 if code:print(O);sys.exit(code)
print(O)
