# One-shot exact prior capped compiler, destination changed and Lean memory capped.
from pathlib import Path
import ast,datetime,hashlib,json,os,re,resource,selectors,shutil,signal,subprocess,sys,time
D=Path(__file__).resolve().parent;R=D.parents[6];FLOOR=3*(1<<30)
S=D.parent.parent/'ordinary_recursion/compile_development_v5.py'
B=R/json.loads((D/'RESUME-BUILD-v1.json').read_text())['directory']
assert json.loads((B/'RESUME-SEED-RECEIPT.json').read_text())['status']=='PASS_EXACT_CHECKPOINT_CONTINUATION_SEED'
class MemoryCap(ast.NodeTransformer):
 def visit_Call(self,n):
  self.generic_visit(n)
  if isinstance(n.func,ast.Attribute) and isinstance(n.func.value,ast.Name) and n.func.value.id=='subprocess' and n.func.attr=='Popen':
   assert isinstance(n.args[0],ast.List)
   n.args[0].elts.insert(1,ast.Constant(value='--memory=3072'))
  return n
for n in ast.parse(S.read_text()).body:
 if isinstance(n,ast.FunctionDef) and n.name in {'sha','limit','run'}:
  n=MemoryCap().visit(n);exec(compile(ast.fix_missing_locations(ast.Module(body=[n],type_ignores=[])),str(S),'exec'))
O=B/('resume-compile-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'));O.mkdir()
rec=dict(instrument_sha256=sha(Path(__file__)),reused_compiler=str(S.relative_to(R)),reused_compiler_sha256=sha(S),memory_megabytes=3072,controls=[],runs=[])
def save():(O/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
save()
try:
 prior=R/'results/algorithm-universal233-ordinary-work-recursion-20261015T215305067588Z/live-compile-20261015T220123767831Z'
 for n,w in [('GuardPositive',0),('GuardFalse',1)]:
  p=O/(n+'.lean');shutil.copyfile(prior/p.name,p);run(n,p,w)
  rec['controls'].append(dict(module=n,source_origin=str((prior/p.name).relative_to(R)),source_sha256=sha(p),passed=True,same_lineage=True));save()
 p=O/'GuardResource.lean';shutil.copyfile(prior/p.name,p);run('GuardResource',p,resource_plant=True)
 rec['controls'].append(dict(module='GuardResource',passed=True,same_lineage=True));save()
 name=sys.argv[1];p=D/(name+'.lean');q=B/p.name
 assert not q.exists() or (q.stat().st_nlink==1 and q.stat().st_mode&0o200),'REFUSE_FROZEN_SOURCE_WRITE'
 if q.exists():(O/(name+'-prior.lean.txt')).write_bytes(q.read_bytes())
 q.write_bytes(p.read_bytes());output=run(name,q,int(sys.argv[2]) if len(sys.argv)>2 else 0)
 assert 'declaration uses `sorry`' not in output and 'sorryAx' not in output,'UNFINISHED_PROOF_NOT_ACCEPTED'
 rec['status']='PASS_AUTHOR_RESUME_GUARDED_COMPILE';save();print(rec['status'],name,flush=True)
except BaseException as e:
 rec.update(status='FAILED_NOT_ACCEPTED',error=repr(e));save();raise
