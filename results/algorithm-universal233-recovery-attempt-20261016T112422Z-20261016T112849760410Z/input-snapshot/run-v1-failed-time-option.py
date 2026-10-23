#!/usr/bin/env python3
"""Owned continuation runner: bounded streaming output, measured RSS, no dependency rebuild.
macOS time -l supplies final exact high-water RSS; ps samples process-group RSS
(sum is conservative for shared pages) and terminates on breach or missing sample.
"""
from pathlib import Path
import datetime,gzip,hashlib,json,os,re,selectors,shutil,signal,subprocess,sys,time
sys.dont_write_bytecode=True
D=Path(__file__).resolve().parent; R=D.parents[5]
C=R/'results/algorithm-universal233-forest-check-root-20261015T211023Z'
E=R/'results/algorithm-universal233-early-resume-20261016T083330Z-20261016T083634190186Z'
B=R/'results/algorithm-universal233-budget-optimization-replay-20261015T213529360638Z'
W=R/'results/algorithm-universal233-optimizer-local-20261016T085144Z-20261016T085502958188Z'
S=R/'results/algorithm-universal233-recovery-source-20261016T092054Z-20261016T092457019053Z'
V=R/'results/algorithm-universal233-recovery-scalar-20261016T095748Z-20261016T100125837782Z'
I=R/'results/algorithm-universal233-recovery-initial-20261016T103025Z-20261016T103331813592Z'
J=R/'results/algorithm-universal233-recovery-control-20261016T105553Z-20261016T105746454634Z'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
CAP={'rss_bytes':3072*1024**2,'raw_bytes':16*1024**2,'line_bytes':8*1024**2,'gzip_bytes':256*1024**2,'disk_bytes':3*1024**3}
if len(sys.argv)>1 and sys.argv[1]=='prepare':
 O=R/'results'/('algorithm-universal233-recovery-attempt-20261016T112422Z-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'));O.mkdir()
 (D/'ACTIVE-v1.json').write_text(json.dumps({'receipt':str(O.relative_to(R))},indent=2)+'\n');(O/'lean-toolchain').write_bytes((B/'lean-toolchain').read_bytes());print(O);sys.exit()
O=R/json.loads((D/'ACTIVE-v1.json').read_text())['receipt']
def supervise(command,tag,seconds=30,env=None,cwd=None):
 assert seconds<=59
 assert shutil.disk_usage(O).free>=CAP['disk_bytes'],'DISK_FLOOR_BEFORE'
 assert sum(p.stat().st_size for p in O.rglob('*.gz'))<CAP['gzip_bytes'],'COMPRESSED_CAP_BEFORE'
 stamp=str(time.time_ns());timelog=O/(tag+'-'+stamp+'.time.txt');start=time.monotonic();reasons=[];samples=[];chunks=[];size=0;line=0;peak=0
 p=subprocess.Popen(['/usr/bin/time','-l','-o',str(timelog),*command],cwd=cwd or O,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,start_new_session=True)
 sel=selectors.DefaultSelector();sel.register(p.stdout,selectors.EVENT_READ)
 def stop(reason):
  if reason not in reasons:reasons.append(reason)
  try:os.killpg(p.pid,signal.SIGKILL)
  except ProcessLookupError:pass
 while sel.get_map() or p.poll() is None:
  now=time.monotonic()
  if now-start>seconds:stop('TIME_CAP')
  if shutil.disk_usage(O).free<CAP['disk_bytes']:stop('DISK_FLOOR')
  if sum(q.stat().st_size for q in O.rglob('*.gz'))>CAP['gzip_bytes']:stop('COMPRESSED_CAP')
  if p.poll() is None:
   try:
    ps=subprocess.run(['/bin/ps','-axo','pid=,pgid=,rss='],capture_output=True,timeout=1,check=True).stdout
    rss=sum(int(z[2])*1024 for x in ps.splitlines() if len(z:=x.split())==3 and int(z[1])==p.pid)
    peak=max(peak,rss);samples.append([round(now-start,4),rss])
    if rss>CAP['rss_bytes']:stop('RSS_CAP')
   except Exception as e:stop('RSS_MEASUREMENT_FAILED:'+type(e).__name__)
  for key,_ in sel.select(.025):
   chunk=os.read(key.fd,65536)
   if not chunk:sel.unregister(key.fileobj);continue
   size+=len(chunk)
   for segment in chunk.splitlines(keepends=True):
    line+=len(segment)
    if line>CAP['line_bytes']:stop('LINE_CAP')
    if segment.endswith(b'\n'):line=0
   if size>CAP['raw_bytes']:stop('RAW_CAP')
   if size<=CAP['raw_bytes']:chunks.append(chunk)
 p.wait();sel.close()
 # Child tree peak reported by Darwin time; missing/unparseable is fail-closed.
 timing=timelog.read_text() if timelog.exists() else ''
 m=re.search(r'^\s*(\d+)\s+maximum resident set size',timing,re.M)
 final_peak=int(m[1]) if m else None
 if final_peak is None:reasons.append('FINAL_RSS_MEASUREMENT_MISSING')
 else:
  peak=max(peak,final_peak)
  if peak>CAP['rss_bytes']:reasons.append('RSS_CAP_FINAL')
 out=b''.join(chunks);log=O/(tag+'-'+stamp+'.log.gz');log.write_bytes(gzip.compress(out,mtime=0))
 if sum(q.stat().st_size for q in O.rglob('*.gz'))>CAP['gzip_bytes']:reasons.append('COMPRESSED_CAP_FINAL')
 rr={'tag':tag,'command':command,'exit':p.returncode,'seconds':time.monotonic()-start,'stop_reasons':reasons,'raw_bytes':size,'peak_rss_bytes':peak,'final_time_rss_bytes':final_peak,'rss_samples':samples,'log':str(log.relative_to(R)),'log_sha256':sha(log),'time_log':str(timelog.relative_to(R)),'time_log_sha256':sha(timelog),'caps':CAP,'limit_seconds':seconds}
 path=O/(tag+'-'+stamp+'.run.json');path.write_text(json.dumps(rr,indent=2)+'\n')
 return rr,out,path

def run(n,want=0,audit=False):
 assert n.startswith('RA'),'REFUSE_DEPENDENCY_REBUILD|'+n
 original=D/(n+'.lean');pth=O/(n+'.lean')
 if original.exists():pth.write_bytes(original.read_bytes())
 source=pth.read_bytes();(O/(n+'-'+str(time.time_ns())+'.source.lean')).write_bytes(source)
 rr,out,path=supervise([str(R/'bootloops-lean'),'-M3072','-o',str(O/(n+'.olean')),str(pth)],n,59 if audit else 30,env=dict(os.environ,LEAN_PATH=':'.join(map(str,[O,J,I,V,S,W,E,B,C]))))
 rr.update(module=n,source_sha256=hashlib.sha256(source).hexdigest(),want=want);path.write_text(json.dumps(rr,indent=2)+'\n')
 assert rr['exit']==want and not rr['stop_reasons'],(n,rr['exit'],rr['stop_reasons'],out.decode(errors='replace')[-6500:])
 return out.decode(errors='replace')
if __name__=='__main__':
 for n in sys.argv[1:]:print(n,run(n)[-1500:],flush=True)
 print(O)
