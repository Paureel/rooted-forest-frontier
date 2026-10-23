from pathlib import Path
import datetime,hashlib,json,os,resource,selectors,shutil,signal,subprocess,sys,time
D=Path(__file__).resolve().parent;R=D.parents[5];B=R/'results/algorithm-universal233-ordinary-recursion-20261015T191007632025Z';FLOOR=3*(1<<30)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def limit():resource.setrlimit(resource.RLIMIT_FSIZE,(8*(1<<20),8*(1<<20)))
stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ');O=B/('live-compile-'+stamp);O.mkdir();rec=dict(instrument_sha256=sha(Path(__file__)),controls=[],runs=[])
def save():(O/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
def run(n,p,want=0,resource_plant=False):
 assert shutil.disk_usage(R).free>=FLOOR,'FREE_SPACE_MARGIN_STOP_BEFORE_LAUNCH';start=time.monotonic()
 proc=subprocess.Popen([str(R/'bootloops-lean'),'-o',str(p.with_suffix('.olean')),str(p)],cwd=B,env=dict(os.environ,LEAN_PATH=str(B)),stdout=subprocess.PIPE,stderr=subprocess.STDOUT,preexec_fn=limit,start_new_session=True)
 sel=selectors.DefaultSelector();sel.register(proc.stdout,selectors.EVENT_READ);chunks=[];size=0;stop=None
 while sel.get_map():
  free=FLOOR-1 if resource_plant else shutil.disk_usage(R).free
  if free<FLOOR:stop='FREE_SPACE_MARGIN_STOP'
  elif time.monotonic()-start>30:stop='COMMAND_30S_CAP'
  elif size>8*(1<<20):stop='STDOUT_8MIB_CAP'
  if stop:
   os.killpg(proc.pid,signal.SIGINT);break
  for key,_ in sel.select(.1):
   data=os.read(key.fd,1<<15)
   if data:chunks.append(data);size+=len(data)
   else:sel.unregister(key.fileobj)
 try:tail=proc.communicate(timeout=2)[0]
 except subprocess.TimeoutExpired:os.killpg(proc.pid,signal.SIGKILL);tail=proc.communicate()[0]
 if tail:chunks.append(tail)
 sel.close();output=b''.join(chunks).decode(errors='replace');log=O/(n+'.log');log.write_text(output)
 row=dict(module=n,source_sha256=sha(p),exit=proc.returncode,expected_exit=want,seconds=time.monotonic()-start,resource_stop=stop,log_sha256=sha(log));rec['runs'].append(row);save()
 if resource_plant:assert stop=='FREE_SPACE_MARGIN_STOP';return output
 assert stop is None,stop
 assert proc.returncode==want,(n,output[-6000:]);return output
save()
try:
 for n,s,w in [('GuardPositive','import Std\ntheorem guard_positive : (1:Nat)+1=2 := by decide\n',0),('GuardFalse','import Std\nexample : (1:Nat)+1=3 := by decide\n',1)]:
  p=O/(n+'.lean');p.write_text(s);out=run(n,p,w);rec['controls'].append(dict(module=n,expected_exit=w,passed=True));save()
 p=O/'GuardResourcePlant.lean';p.write_text('import Std\ntheorem guard_resource : True := True.intro\n');run('GuardResourcePlant',p,resource_plant=True);rec['controls'].append(dict(module='GuardResourcePlant',passed=True,scope='Synthetic below-floor reading stops own process before real development.'));save()
 n=sys.argv[1];p=D/(n+'.lean');q=B/p.name
 assert not q.exists() or q.stat().st_nlink==1,'REFUSE_LINKED_DEPENDENCY_WRITE'
 if q.exists():(O/(n+'-prior.lean.txt')).write_bytes(q.read_bytes())
 q.write_bytes(p.read_bytes());run(n,q);rec['status']='PASS_AUTHOR_LIVE_GUARDED_COMPILE';save();print(rec['status'],n,flush=True)
except BaseException as e:rec.update(status='FAILED_NOT_ACCEPTED',error=repr(e));save();raise
