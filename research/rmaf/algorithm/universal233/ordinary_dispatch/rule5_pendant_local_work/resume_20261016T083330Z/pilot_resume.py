#!/usr/bin/env python3
"""Problem-specific extension of ../pilot.py; never rebuild dependencies.
Adds explicit Lean memory and output caps; not a new reusable toolkit engine.
"""
from pathlib import Path
import datetime,gzip,hashlib,json,os,shutil,signal,subprocess,sys,threading,time
D=Path(__file__).resolve().parent; P=D.parent; R=P.parents[5]; B=D/'build'; B.mkdir(exist_ok=True)
C=R/'results/algorithm-universal233-fast-ordinary-recursion-replay-20261015T205325296780Z'; old=P/'build'
T=R/'research/rmaf/monitoring/resume-20261016T083330Z/rule5-TARGET-v1.json'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(T)=='ecf42b0b64cfe61e6288812a2c94b7dc40e6e5132a408e34122278b639f81db4'
m=json.loads(T.read_text())
for e in m['own_checkpoint_sha256']:assert sha(R/e['path'])==e['sha256'],e['path']
pre=json.loads((D/'IMPORT-CLOSURE-PRECHECK-v1.json').read_text());assert not pre['conflicts']
fmanifest=json.loads((R/m['allowed_packages']['functional']['manifest']).read_text());frozen={e['path']:e['sha256'] for e in fmanifest['immutable_files']}
for n,h in pre['source_hashes'].items():
 for p in [C/(n+'.lean'),C/(n+'.olean')]:
  assert sha(p)==frozen[str(p.relative_to(R))],str(p)
assert shutil.disk_usage(D).free>=3*1024**3
(B/'lean-toolchain').write_bytes((old/'lean-toolchain').read_bytes())
O=R/'results'/('algorithm-universal233-rule5-resume-20261016T083330Z-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'));O.mkdir()
rec=dict(status='RUNNING',runs=[],lineage='Same author/Lean and frozen sources; no independent verification claim',limits=dict(seconds_per_process=30,lean_memory_mib=3072,free_disk_bytes=3*1024**3,raw_bytes=64*1024**2,logical_bytes=128*1024**2));(D/'LAST-RUN.txt').write_text(str(O)+'\n')
for n in sys.argv[1:]:
 assert n not in pre['source_hashes'] and not (old/(n+'.lean')).exists(),'REFUSE_DEPENDENCY_REBUILD'
 p=D/(n+'.lean');assert p.exists();(B/p.name).write_bytes(p.read_bytes());(O/p.name).write_bytes(p.read_bytes());start=time.monotonic()
 log=O/(n+'.log.gz'); captured=[];count=[0];stop=threading.Event();reason=[]
 command=[str(R/'bootloops-lean'),'-M3072','-o',str(B/(n+'.olean')),str(B/p.name)]
 proc=subprocess.Popen(command,cwd=B,env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[B,old,C]))),stdout=subprocess.PIPE,stderr=subprocess.STDOUT,start_new_session=True)
 def kill(why):
  if not reason:reason.append(why)
  try:os.killpg(proc.pid,signal.SIGTERM)
  except ProcessLookupError:pass
 def collect():
  with gzip.open(log,'wb') as f:
   while True:
    part=proc.stdout.read(65536)
    if not part:break
    count[0]+=len(part)
    if count[0]>64*1024**2:kill('RAW_OUTPUT_CAP');break
    f.write(part);captured.append(part)
 def watch():
  while not stop.wait(.1):
   if shutil.disk_usage(O).free<3*1024**3:kill('LIVE_DISK_FLOOR');return
   if sum(p.stat().st_size for p in O.rglob('*') if p.is_file())>128*1024**2:kill('LOGICAL_DIRECTORY_CAP');return
 reader=threading.Thread(target=collect,daemon=True);watcher=threading.Thread(target=watch,daemon=True);reader.start();watcher.start()
 try:code=proc.wait(timeout=30)
 except subprocess.TimeoutExpired:kill('TIMEOUT_30S');code=124;proc.wait(timeout=5)
 finally:stop.set();watcher.join();reader.join(timeout=5)
 if reason:code=125
 out=b''.join(captured).decode(errors='replace')
 rec['runs'].append(dict(module=n,exit=code,seconds=time.monotonic()-start,source_sha256=sha(p),raw_output_bytes=count[0],cap_reason=reason,command=command,olean_sha256=sha(B/(n+'.olean')) if code==0 else None))
 rec['status']='FAIL_RETAINED' if code else 'PASS_AUTHOR_PILOT';(O/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n')
 print(n,code,round(rec['runs'][-1]['seconds'],3),out[-6000:],flush=True)
 if code:print(O);sys.exit(code)
print(O)
