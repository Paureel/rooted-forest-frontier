# One-shot adapter of the already measured guarded compiler. Toolkit consulted:
# no toolkit package supplies Lean source-meter proofs; reuse its campaign driver.
from pathlib import Path
import ast,datetime,hashlib,json,os,re,resource,selectors,shutil,signal,subprocess,sys,time
D=Path(__file__).resolve().parent;R=D.parents[5];B=R/json.loads((D/'BUILD-v1.json').read_text())['directory'];FLOOR=3*(1<<30)
S=D.parent/'ordinary_recursion/compile_development_v5.py'
class Caps(ast.NodeTransformer):
 def visit_Call(self,n):
  self.generic_visit(n)
  if isinstance(n.func,ast.Attribute) and isinstance(n.func.value,ast.Name) and n.func.value.id=='subprocess' and n.func.attr=='Popen':n.args[0].elts.insert(1,ast.Constant(value='--memory=3072'))
  return n
for n in ast.parse(S.read_text()).body:
 if isinstance(n,ast.FunctionDef) and n.name in {'sha','limit','run'}:
  n=Caps().visit(n);s=ast.unparse(n).replace('8 * (1 << 20)','120000').replace('STDOUT_8MIB_CAP','STDOUT_120KB_CAP');exec(s,globals())
O=B/('compile-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'));O.mkdir();rec={'instrument_sha256':sha(Path(__file__)),'reused_compiler_sha256':sha(S),'runs':[]}
def save():(O/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
save()
try:
 for n,s,w in [('GuardPositive','import Std\ntheorem guard_positive : (2:Nat)+3=5 := by decide\n',0),('GuardFalse','import Std\nexample : (2:Nat)+3=4 := by decide\n',1)]:
  p=O/(n+'.lean');p.write_text(s);run(n,p,w)
 n=sys.argv[1];p=D/(n+'.lean');q=B/p.name;assert not q.exists() or (q.stat().st_nlink==1 and q.stat().st_mode&0o200)
 if q.exists():(O/(n+'-prior.lean.txt')).write_bytes(q.read_bytes())
 q.write_bytes(p.read_bytes());out=run(n,q,int(sys.argv[2]) if len(sys.argv)>2 else 0);assert 'sorryAx' not in out and 'declaration uses `sorry`' not in out
 rec['status']='PASS_AUTHOR_GUARDED_SOURCE_COMPILE';save();print(rec['status'],n)
except BaseException as e:rec.update(status='FAILED_NOT_ACCEPTED',error=repr(e));save();raise
