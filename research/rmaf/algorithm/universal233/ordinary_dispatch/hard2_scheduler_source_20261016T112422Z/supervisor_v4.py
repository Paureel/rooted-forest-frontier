from pathlib import Path
import hashlib,json,os,re,resource,selectors,shutil,signal,subprocess,sys,time
import ctypes
import psutil
RSS_CAP=3072*(1<<20);RSS_MARGIN=256*(1<<20);RAW_CAP=8*(1<<20);LINE_CAP=8*(1<<20);FLOOR=3*(1<<30)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def limit():
 resource.setrlimit(resource.RLIMIT_FSIZE,(64*(1<<20),64*(1<<20)))
 resource.setrlimit(resource.RLIMIT_CORE,(0,0))
_proc=ctypes.CDLL('/usr/lib/libproc.dylib',use_errno=True)
_child=_proc.proc_listchildpids;_child.argtypes=[ctypes.c_int,ctypes.c_void_p,ctypes.c_int];_child.restype=ctypes.c_int
def own_tree_rss(pid):
 queue=[pid];seen=set();rss=0
 while queue:
  p=queue.pop()
  if p in seen:continue
  seen.add(p)
  try:rss+=psutil.Process(p).memory_info().rss
  except (psutil.NoSuchProcess,psutil.ZombieProcess):continue
  a=(ctypes.c_int*1024)();n=_child(p,a,ctypes.sizeof(a))
  assert 0<=n<len(a),('OWN_CHILD_QUERY_FAILED',p,n,ctypes.get_errno())
  queue.extend(a[:n])
 return rss
def run(cmd,cwd,env,out,label,seconds=30,want=0,plant=None):
 assert 0<seconds<=59 and sys.platform=='darwin'
 out=Path(out);out.mkdir(exist_ok=True);cwd=Path(cwd);log=out/(label+'.log');receipt=out/(label+'.receipt.json')
 assert not receipt.exists();rss_limit=RSS_CAP-RSS_MARGIN;raw_limit=RAW_CAP;line_limit=LINE_CAP
 if plant=='rss':rss_limit=32*(1<<20)
 if plant=='raw':raw_limit=1<<20
 if plant=='line':line_limit=1<<19
 start=time.monotonic();chunks=[];size=0;line=0;peak=0;stop=None;samples=0;usage=None;exited=False;killed=False
 proc=subprocess.Popen(list(cmd),cwd=cwd,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,start_new_session=True,preexec_fn=limit)
 sel=selectors.DefaultSelector();sel.register(proc.stdout,selectors.EVENT_READ)
 while sel.get_map() or not exited:
  now=time.monotonic()
  if not exited:
   try:peak=max(peak,own_tree_rss(proc.pid));samples+=1
   except (psutil.NoSuchProcess,psutil.ZombieProcess):pass
   except BaseException as error:stop='MONITOR_QUERY_FAILURE|'+repr(error)
  if stop is not None:pass
  elif peak>rss_limit:stop='PEAK_RSS_MARGIN_STOP'
  elif now-start>seconds:stop='WALL_CAP_STOP'
  elif plant=='disk' or shutil.disk_usage(cwd).free<FLOOR:stop='LIVE_DISK_FLOOR_STOP'
  elif size>raw_limit:stop='RAW_CAP_STOP'
  elif line>line_limit:stop='LINE_CAP_STOP'
  if stop and not killed:
   try:os.killpg(proc.pid,signal.SIGKILL)
   except ProcessLookupError:pass
   killed=True
  for key,_ in sel.select(.025):
   b=os.read(key.fd,1<<15)
   if not b:sel.unregister(key.fileobj);continue
   chunks.append(b);size+=len(b);pieces=b.split(b'\n')
   line=line+len(b) if len(pieces)==1 else len(pieces[-1])
   if any(len(x)>line_limit for x in pieces):stop='LINE_CAP_STOP'
  if not exited:
   pid,status,ru=os.wait4(proc.pid,os.WNOHANG)
   if pid:
    proc.returncode=os.waitstatus_to_exitcode(status);usage=ru;exited=True
 sel.close();proc.stdout.close();data=b''.join(chunks);log.write_bytes(data)
 assert usage is not None
 exact=int(usage.ru_maxrss)
 if exact>RSS_CAP:stop='EXACT_PEAK_RSS_CAP_VIOLATION'
 if size>raw_limit and stop is None:stop='RAW_CAP_STOP'
 if any(len(x)>line_limit for x in data.split(b'\n')) and stop is None:stop='LINE_CAP_STOP'
 elapsed=time.monotonic()-start
 if elapsed>seconds and stop is None:stop='WALL_CAP_STOP'
 row=dict(status='PASS' if stop is None and proc.returncode==want else 'FAILED_RETAINED',cmd=cmd,cwd=str(cwd),source_sha256=sha(cmd[-1]) if Path(cmd[-1]).is_file() else None,exit=proc.returncode,expected_exit=want,seconds=elapsed,cap_seconds=seconds,sampled_group_peak_RSS_bytes=peak,wait4_exact_peak_RSS_bytes=exact,RSS_samples=samples,hard_RSS_cap_bytes=RSS_CAP,margin_stop_bytes=rss_limit,stdout_bytes=size,raw_cap_bytes=raw_limit,line_cap_bytes=line_limit,disk_floor_bytes=FLOOR,resource_stop=stop,plant=plant,log=str(log),log_sha256=sha(log),measurement='own-child-tree direct libproc/psutil RSS monitoring plus exact Darwin wait4 ru_maxrss; no global process enumeration or time sysctl',supervisor_sha256=sha(__file__))
 receipt.write_text(json.dumps(row,indent=2)+'\n')
 if plant:
  expected={'rss':'PEAK_RSS_MARGIN_STOP','raw':'RAW_CAP_STOP','line':'LINE_CAP_STOP','disk':'LIVE_DISK_FLOOR_STOP','time':'WALL_CAP_STOP'}[plant]
  assert stop==expected,(label,row)
 else:assert row['status']=='PASS',(label,row,data[-2000:].decode(errors='replace'))
 return row,data.decode(errors='replace')
