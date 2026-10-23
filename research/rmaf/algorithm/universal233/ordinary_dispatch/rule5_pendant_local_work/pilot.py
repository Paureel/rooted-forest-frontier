#!/usr/bin/env python3
"""New-module-only capped pilot; linked dependencies are never written."""
from pathlib import Path
import datetime,json,os,shutil,subprocess,sys,time,threading,gzip,signal
D=Path(__file__).resolve().parent;R=D.parents[5];B=D/'build';deps=json.loads((D/'DEPENDENCIES.json').read_text());names={e['module'] for e in deps}
O=R/'results'/('algorithm-universal233-rule5-pendant-local-work-pilot-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'));O.mkdir();rec=dict(status='RUNNING',runs=[])
for n in sys.argv[1:]:
 assert n not in names,'REFUSE_REBUILD_LINKED_DEPENDENCY';assert shutil.disk_usage(O).free>=3*1024**3,'DISK_FLOOR_3GIB'
 for e in deps:
  assert os.path.samefile(B/(e['module']+'.lean'),R/e['source']);assert os.path.samefile(B/(e['module']+'.olean'),R/e['olean'])
 (B/(n+'.lean')).write_bytes((D/(n+'.lean')).read_bytes());(O/(n+'.lean')).write_bytes((D/(n+'.lean')).read_bytes());start=time.monotonic()
 try:
  p=subprocess.Popen([str(R/'bootloops-lean'),'-o',str(B/(n+'.olean')),str(B/(n+'.lean'))],cwd=B,env=dict(os.environ,LEAN_PATH=str(B)),text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,start_new_session=True)
  stop=threading.Event();low=[False]
  def watch():
   while not stop.wait(0.1):
    if shutil.disk_usage(O).free<3*1024**3:
     low[0]=True
     try:os.killpg(p.pid,signal.SIGTERM)
     except ProcessLookupError:pass
     return
  monitor=threading.Thread(target=watch,daemon=True);monitor.start()
  try:out,_=p.communicate(timeout=30)
  finally:stop.set();monitor.join()
  code=p.returncode
  if low[0]:code=125;out+='\nLIVE_DISK_FLOOR_3GIB_STOP\n'
 except subprocess.TimeoutExpired as e:
  try:os.killpg(p.pid,signal.SIGTERM)
  except ProcessLookupError:pass
  out,_=p.communicate(timeout=5);code=124;out+='\nPILOT_TIMEOUT_30S\n'
 if n=='PendantWorkControls' and '("PASS_LITERAL_PENDANT_WORK_CONTROLS", true)' not in out:
  code=1;out+='\nRUNTIME_TRUTH_CONTROLS_FAILED\n'
 gzip.open(O/(n+'.log.gz'),'wt').write(out);rec['runs'].append(dict(module=n,exit=code,seconds=time.monotonic()-start));(O/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n');print(n,code,out[-7000:],flush=True)
 if code:rec['status']='FAIL_RETAINED';(O/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n');print(O);sys.exit(code)
rec['status']='PASS_AUTHOR_PILOT';(O/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n');print(O)
