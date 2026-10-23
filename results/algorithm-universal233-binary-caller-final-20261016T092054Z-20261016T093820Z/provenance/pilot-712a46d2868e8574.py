#!/usr/bin/env python3
"""One-root bounded compiler that refuses every linked dependency target."""
from pathlib import Path
import datetime,gzip,hashlib,json,os,selectors,shutil,subprocess,sys,time
D=Path(__file__).resolve().parent;R=next(p for p in D.parents if (p/'bootloops-lean').exists());spec=json.loads((D/'ROOT-v1.json').read_text());O=R/spec['root'];DEPS={e['module'] for e in spec['dependencies']};sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def run(n,build=False,want=0):
 if n in DEPS:raise RuntimeError('REFUSE_LINKED_DEPENDENCY_COMPILATION|'+n)
 for suffix in ['.lean','.olean']:
  p=O/(n+suffix)
  if p.exists() and p.stat().st_nlink>1:raise RuntimeError('REFUSE_LINK_MUTATION|'+str(p))
 if shutil.disk_usage(D).free<3*1024**3:raise RuntimeError('DISK_FLOOR_3_GIB')
 stamp=str(time.time_ns());source=O/(n+'.lean');(O/(n+'-'+stamp+'.source')).write_bytes(source.read_bytes());start=time.monotonic();p=subprocess.Popen([str(R/'bootloops-lean'),'-M','3072']+(['-o',str(O/(n+'.olean'))] if build else [])+[str(source)],cwd=O,env=dict(os.environ,LEAN_PATH=str(O)),stdout=subprocess.PIPE,stderr=subprocess.STDOUT);sel=selectors.DefaultSelector();sel.register(p.stdout,selectors.EVENT_READ);out=bytearray();fail=None
 while sel.get_map():
  if time.monotonic()-start>30:fail='TIMEOUT';p.kill()
  if shutil.disk_usage(D).free<3*1024**3:fail='LIVE_DISK_FLOOR_3_GIB';p.kill()
  for key,_ in sel.select(.2):
   b=os.read(key.fileobj.fileno(),65536)
   if not b:sel.unregister(key.fileobj);continue
   if len(out)+len(b)>8*1024**2:fail='OUTPUT_CAP';p.kill()
   else:out.extend(b)
  if fail and p.poll() is not None:break
 p.wait();sel.close();txt=out.decode(errors='replace');log=O/(n+'-'+stamp+'.log.gz')
 with gzip.open(log,'wt') as f:f.write(txt)
 rec={'module':n,'exit':p.returncode,'seconds':time.monotonic()-start,'failure':fail,'source_sha256':sha(source),'log_sha256':sha(log),'output_bytes':len(out),'expected_exit':want}
 (O/(n+'-'+stamp+'.run.json')).write_text(json.dumps(rec,indent=2)+'\n');print(n,p.returncode,round(rec['seconds'],3),flush=True)
 if p.returncode!=want or fail:print(txt[-6500:]);raise AssertionError(rec)
 return txt
if __name__=='__main__':
 for n in sys.argv[1:]:
  if n in DEPS:raise RuntimeError('LINKED_DEPENDENCY')
  dest=O/(n+'.lean')
  if dest.exists() and dest.stat().st_nlink>1:raise RuntimeError('LINKED_SOURCE')
  dest.write_bytes((D/(n+'.lean')).read_bytes());run(n,True)
