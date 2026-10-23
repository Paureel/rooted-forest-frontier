#!/usr/bin/env python3
"""One-shot bounded author build wrapper using completed DEVELOPMENT audit.
Toolkit index has no rooted-tree Lean transport; reuse the completed audit and
add only path isolation, 30-second caps, and retained attempt logs here.
"""
from pathlib import Path
import datetime,hashlib,importlib.util,json,os,subprocess,sys,time
sys.dont_write_bytecode=True
D=Path(__file__).resolve().parent;R=D.parents[4];O=D/'build';O.mkdir(exist_ok=True)
S=R/'results/algorithm-universal233-rule5-final-classification-replay-20261015T145040Z'
spec=importlib.util.spec_from_file_location('prior_audit',D.parent/'rule5_final_classification/audit.py');audit=importlib.util.module_from_spec(spec);spec.loader.exec_module(audit)
(O/'lean-toolchain').write_bytes((S/'lean-toolchain').read_bytes())
def run(out,n,build=False):
 start=time.monotonic();p=subprocess.run([str(R/'bootloops-lean')]+(['-o',str(out/(n+'.olean'))] if build else [])+[str(out/(n+'.lean'))],cwd=out,env=dict(os.environ,LEAN_PATH=str(out)),text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=30)
 (out/(n+'-'+str(time.time_ns())+'.log')).write_text(p.stdout)
 print(n,p.returncode,round(time.monotonic()-start,3),flush=True)
 return p
audit.run_lean=run
if sys.argv[1:] == ['controls']:
 C=R/'results'/('algorithm-universal233-rule5-source-orientation-producer-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'));C.mkdir();(C/'lean-toolchain').write_bytes((S/'lean-toolchain').read_bytes())
 controls=audit.detector_controls(C)
 for n,text,want in [('StdTrue','import Std\nexample : (3:Nat)+4=7 := by decide\n',0),('StdFalse','import Std\nexample : (3:Nat)+4=8 := by decide\n',1)]:
  (C/(n+'.lean')).write_text(text);p=run(C,n);assert p.returncode==want
  if want:assert p.stdout.count('is false')==1
 rec={'status':'PASS_AUTHOR_PRODUCER_PREFLIGHT','controls':controls,'independent_credit':0,'instrument_sha256':hashlib.sha256((D.parent/'rule5_final_classification/audit.py').read_bytes()).hexdigest(),'wrapper_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'immutable_files':[{'path':str(p.relative_to(R)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in sorted(C.iterdir()) if p.is_file()]}
 (C/'manifest.json').write_text(json.dumps(rec,indent=2)+'\n')
 for p in C.iterdir():p.chmod(0o444)
 (D/'PRODUCER-PREFLIGHT-v1.json').write_text(json.dumps({'manifest':str((C/'manifest.json').relative_to(R)),'sha256':hashlib.sha256((C/'manifest.json').read_bytes()).hexdigest()},indent=2)+'\n')
 print(rec['status']);sys.exit()
assert (D/'PRODUCER-PREFLIGHT-v1.json').exists()
for p in S.glob('*'):
 if p.suffix in ['.lean','.olean'] and not (O/p.name).exists():(O/p.name).write_bytes(p.read_bytes())
for n in sys.argv[1:]:
 (O/(n+'.lean')).write_bytes((D/(n+'.lean')).read_bytes());p=run(O,n,True)
 if p.returncode:print(p.stdout);sys.exit(p.returncode)
