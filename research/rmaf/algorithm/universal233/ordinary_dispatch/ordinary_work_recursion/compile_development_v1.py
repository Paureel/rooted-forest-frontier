# One-shot guarded DP proof compiler; immutable capped engine reused.
from pathlib import Path
import ast,datetime,hashlib,json,os,re,resource,selectors,shutil,signal,subprocess,sys,time
D=Path(__file__).resolve().parent;R=D.parents[5];FLOOR=3*(1<<30)
S=D.parent/'ordinary_recursion/compile_development_v5.py';B=R/json.loads((D/'LATEST-BUILD-v1.json').read_text())['directory']
assert json.loads((B/'SEED-RECEIPT.json').read_text())['status']=='PASS_EXACT_READONLY_SOURCE_SEED'
for n in ast.parse(S.read_text()).body:
 if isinstance(n,ast.FunctionDef) and n.name in {'sha','limit','run'}:exec(compile(ast.Module(body=[n],type_ignores=[]),str(S),'exec'))
O=B/('live-compile-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'));O.mkdir();rec=dict(instrument_sha256=sha(Path(__file__)),reused_compiler=str(S.relative_to(R)),reused_compiler_sha256=sha(S),controls=[],runs=[])
def save():(O/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
save()
try:
 for n,s,w in [('GuardPositive','import Std\nexample : (1:Nat)+1=2 := by decide\n',0),('GuardFalse','import Std\nexample : (1:Nat)+1=3 := by decide\n',1)]:
  p=O/(n+'.lean');p.write_text(s);run(n,p,w);rec['controls'].append(dict(module=n,passed=True));save()
 p=O/'GuardResource.lean';p.write_text('import Std\nexample : True := True.intro\n');run('GuardResource',p,resource_plant=True);rec['controls'].append(dict(module='GuardResource',passed=True));save()
 n=sys.argv[1];p=D/(n+'.lean');q=B/p.name;assert not q.exists() or q.stat().st_nlink==1,'REFUSE_FROZEN_LINK'
 if q.exists():(O/(n+'-prior.lean.txt')).write_bytes(q.read_bytes())
 q.write_bytes(p.read_bytes());run(n,q,int(sys.argv[2]) if len(sys.argv)>2 else 0);rec['status']='PASS_AUTHOR_LIVE_GUARDED_COMPILE';save();print(rec['status'],n,flush=True)
except BaseException as e:rec.update(status='FAILED_NOT_ACCEPTED',error=repr(e));save();raise
