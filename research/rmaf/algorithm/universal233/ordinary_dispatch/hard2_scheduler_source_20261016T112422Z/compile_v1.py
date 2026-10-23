from pathlib import Path
import datetime,hashlib,importlib.util,json,os,re,shutil,sys
sys.dont_write_bytecode=True
D=Path(__file__).resolve().parent;R=D.parents[5];B=R/json.loads((D/'BUILD-v1.json').read_text())['directory']
s=importlib.util.spec_from_file_location('own_supervised_compiler',D/'supervisor_v4.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
assert json.loads((B/'supervisor-controls-v4/controls.json').read_text())['status'].startswith('PASS_MEASURED_SUPERVISOR')
assert not (D/'RESOURCE-STOP-v1.json').exists(),'PERMANENT_RESOURCE_STOP_REQUIRES_NEW_ROOT_LICENSE'
O=B/('compile-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'));O.mkdir();rec=dict(status='CHECKING',supervisor_sha256=m.sha(D/'supervisor_v4.py'),controls=[],runs=[])
def save():(O/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
def run(n,p,want):
 cmd=[str(R/'bootloops-lean'),'--memory=2688','-o',str(p.with_suffix('.olean')),str(p)]
 try:row,output=m.run(cmd,B,dict(os.environ,LEAN_PATH=str(B)),O,n,seconds=30,want=want)
 except BaseException:
  f=O/(n+'.receipt.json')
  if f.exists() and json.loads(f.read_text())['resource_stop']:
   (D/'RESOURCE-STOP-v1.json').write_text(json.dumps(dict(status='PERMANENT_AFFECTED_STAGE_RESOURCE_STOP',receipt=str(f.relative_to(R)),sha256=m.sha(f)),indent=2)+'\n')
  raise
 row.update(module=n,source_sha256=m.sha(p),olean_sha256=m.sha(p.with_suffix('.olean')) if p.with_suffix('.olean').exists() else None);rec['runs'].append(row);save()
 assert 'declaration uses `sorry`' not in output and 'sorryAx' not in output
 if want==1:
  errors=re.findall(r': error(?:\([^)]*\))?: ([^\n]*)',output)
  assert errors and all(e=='unsolved goals' or e.startswith('Tactic `decide` proved that the proposition') for e in errors),errors
 return row
save()
try:
 for n,source,w in [('GuardPositive','import Std\ntheorem guard_positive : (1:Nat)+1=2 := by decide\n',0),('GuardFalse','import Std\nexample : (1:Nat)+1=3 := by decide\n',1)]:
  p=O/(n+'.lean');p.write_text(source);run(n,p,w);rec['controls'].append(dict(module=n,passed=True));save()
 n=sys.argv[1];p=D/(n+'.lean');q=B/p.name;assert not q.exists() or q.stat().st_nlink==1 and q.stat().st_mode&0o200
 if q.exists():(O/(n+'-prior.lean.txt')).write_bytes(q.read_bytes())
 q.write_bytes(p.read_bytes());r=run(n,q,int(sys.argv[2]) if len(sys.argv)>2 else 0)
 rec['status']='PASS_AUTHOR_MEASURED_SOURCE_COMPILE';save();print(rec['status'],n,'PEAK_RSS_BYTES',max(r['sampled_group_peak_RSS_bytes'],r['wait4_exact_peak_RSS_bytes']))
except BaseException as e:rec.update(status='FAILED_RETAINED',error=repr(e));save();raise
