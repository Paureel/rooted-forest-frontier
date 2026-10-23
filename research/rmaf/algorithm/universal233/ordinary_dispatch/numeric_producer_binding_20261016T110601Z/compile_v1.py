# One-shot guarded Lean adapter, preserving every attempt and frozen dependency.
from pathlib import Path
import json,os,subprocess,sys,time,hashlib,shutil,datetime,signal
D=Path(__file__).resolve().parent;R=D.parents[5];P=json.loads((D/'DEPENDENCY-PINS-v1.json').read_text());B=R/P['pool']
assert shutil.disk_usage(D).free>=3*(1<<30)
n=sys.argv[1];expected=int(sys.argv[2]) if len(sys.argv)>2 else 0
O=D/'attempts'/datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ');O.mkdir(parents=True)
p=D/(n+'.lean');b=p.read_bytes();(O/p.name).write_bytes(b)
env=dict(os.environ,LEAN_PATH=str(D)+os.pathsep+str(R/P['prior_own_pool'])+os.pathsep+str(B),BOOTLOOPS_RUN_TITLE='numeric invariants '+n)
t=time.monotonic();proc=subprocess.Popen([str(R/'bootloops-lean'),'--memory=3072','-o',str(D/(n+'.olean')),str(p)],cwd=D,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,start_new_session=True)
try:out,_=proc.communicate(timeout=30)
except subprocess.TimeoutExpired:
 os.killpg(proc.pid,signal.SIGTERM);out,_=proc.communicate();(O/'log.txt').write_bytes(out);raise
(O/'log.txt').write_bytes(out)
rec=dict(module=n,source_sha256=hashlib.sha256(b).hexdigest(),exit=proc.returncode,expected=expected,seconds=time.monotonic()-t,log_bytes=len(out),memory_mib=3072,timeout_seconds=30,command='bootloops-lean --memory=3072 -o OWN.olean OWN.lean',accepted=proc.returncode==expected and b'sorry' not in out,olean_sha256=hashlib.sha256((D/(n+'.olean')).read_bytes()).hexdigest() if proc.returncode==0 and expected==0 else None)
assert p.read_bytes()==b
(O/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec));print(out.decode()[:7000]);assert rec['accepted']
