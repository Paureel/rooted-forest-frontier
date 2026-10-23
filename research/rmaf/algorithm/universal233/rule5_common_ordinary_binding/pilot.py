#!/usr/bin/env python3
"""One-shot bounded author compiler; retains exact source per attempt."""
from pathlib import Path
import gzip,os,selectors,shutil,subprocess,sys,time
sys.dont_write_bytecode=True
D=Path(__file__).resolve().parent;R=D.parents[4];O=D/'build'
def run(root,n,build=False,want=0):
 if shutil.disk_usage(D).free<3*1024**3:raise RuntimeError('DISK_FLOOR_3_GIB')
 stamp=str(time.time_ns());src=root/(n+'.lean');(root/(n+'-'+stamp+'.source')).write_bytes(src.read_bytes());start=time.monotonic()
 p=subprocess.Popen([str(R/'bootloops-lean')]+(['-o',str(root/(n+'.olean'))] if build else [])+[str(src)],cwd=root,env=dict(os.environ,LEAN_PATH=str(root)),stdout=subprocess.PIPE,stderr=subprocess.STDOUT);sel=selectors.DefaultSelector();sel.register(p.stdout,selectors.EVENT_READ);data=bytearray();fail=None
 while sel.get_map():
  if time.monotonic()-start>30:fail='TIMEOUT';p.kill()
  for key,_ in sel.select(.2):
   b=os.read(key.fileobj.fileno(),65536)
   if not b:sel.unregister(key.fileobj);continue
   if len(data)+len(b)>8*1024**2:fail='OUTPUT_CAP';p.kill()
   else:data.extend(b)
  if fail and p.poll() is not None:break
 p.wait();sel.close();txt=data.decode(errors='replace')
 with gzip.open(root/(n+'-'+stamp+'.log.gz'),'wt') as f:f.write(txt)
 print(n,p.returncode,round(time.monotonic()-start,3),flush=True)
 if p.returncode!=want or fail:print(txt[-6000:]);raise AssertionError((n,p.returncode,fail))
 return txt
if __name__=='__main__':
 assert (D/'PRODUCER-PREFLIGHT-v1.json').exists()
 for n in sys.argv[1:]:
  (O/(n+'.lean')).write_bytes((D/(n+'.lean')).read_bytes());run(O,n,True)
