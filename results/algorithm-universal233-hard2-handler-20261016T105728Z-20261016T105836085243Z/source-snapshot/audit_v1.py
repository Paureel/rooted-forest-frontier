# Author source integration audit. Reuses controlled exact compressed producer engine.
from pathlib import Path
import ast,datetime,gzip,hashlib,importlib.util,json,os,re,resource,selectors,shlex,shutil,signal,subprocess,time
D=Path(__file__).resolve().parent;R=D.parents[5];B=R/json.loads((D/'BUILD-v1.json').read_text())['directory']
O=B/'author-audit-v1';assert not O.exists();O.mkdir()
V=D.parent/'resume_20261015T1810Z/compressed_pool_resume_v3.py'
def load(n,p):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
A=load('integration_producer',R/'research/rmaf/algorithm/universal233/rule5_common_split/audit_graph.py')
G=load('integration_compatibility',D.parent/'producer_compatibility/compatibility.py')
class MemoryCap(ast.NodeTransformer):
 def visit_Call(self,n):
  self.generic_visit(n)
  if isinstance(n.func,ast.Attribute) and isinstance(n.func.value,ast.Name) and n.func.value.id=='subprocess' and n.func.attr=='Popen':n.args[0].left.left.elts.append(ast.Constant(value='--memory=3072'))
  return n
for n in ast.parse(V.read_text()).body:
 if isinstance(n,ast.FunctionDef) and n.name in {'sha','string_sha','pin','margin','cap','run','source','header_source','parse_header','extract','read_rows','fingerprint'}:
  n=MemoryCap().visit(n);exec(compile(ast.fix_missing_locations(ast.Module(body=[n],type_ignores=[])),str(V),'exec'),globals())
compressed_source=source
full={'Hard2GroupingSource','GoodPairSource','Hard2GroupingBound','GoodPairLocalBound','GoodPairWeightedBound','GoodPairSelectedBound','OrdinaryPrepareSource','OrdinaryPrepareBound'}
def source(imports,modules,out):
 s=compressed_source(imports,modules,out)
 if not set(modules)<=full:return s
 a='let body := match ci with | .thmInfo _ => none | _ => ci.value? true';assert s.count(a)==1;s=s.replace(a,'let body := ci.value? true')
 a='match ci with | .thmInfo _ => "OMITTED_THEOREM_PROOF_TEXT" | _ => "FULL_NONPROOF_BODY"';assert s.count(a)==1;return s.replace(a,'"FULL_ALL_BODY"')
# The exact full ConstantInfo bridge is reused from the completed author stage.
P=D.parent/'ordinary_full_source_work_20261016T085803Z/audit_v3.py'
for n in ast.parse(P.read_text()).body:
 if isinstance(n,ast.FunctionDef) and n.name in {'metadata_compare','metadata_profile'}:exec(compile(ast.Module(body=[n],type_ignores=[]),str(P),'exec'),globals())
rec=dict(status='CHECKING',all_main_milestones='OPEN',full_runtime_claim=False,independent_acceptance=False,runs=[],inputs={},controls={},sources=[],reused_producers=[],new_producers=[],version_compatibility=[])
def save():(O/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n')
def closure(starts,resolve):
 order=[];seen=set()
 def visit(n):
  if n in seen:return
  p,o=resolve(n);assert p.exists() and o.exists(),n
  for dep in re.findall(r'^import ([A-Za-z0-9_\'.]+)\s*$',p.read_text(),re.M):
   if dep.split('.')[0] not in {'Std','Lean','Init'}:visit(dep)
  seen.add(n);order.append(n)
 for n in starts:visit(n)
 return order
save()
try:
 assert sha(V)=='626e3f21ba70fb417ad1085995a88b4af217a1b6f210191fa58ca442aad0098a'
 T=R/'research/rmaf/monitoring/main-next-20261016T105728Z/MAIN-HANDLER-TARGET-v1.json';assert sha(T)=='7a2f2210eea48dd5179088da4ceab59736556291980025b6eac9d1b41355b1af';t=json.loads(T.read_text())
 for p in [Path(__file__),D.parent/'ordinary_full_source_integration_20261016T092805Z/audit_v2.py',V,P,Path(A.__file__),Path(G.__file__),T,B/'SEED.json',D/'compile_v1.py',D/'CONTROLS-PIN-v1.md']:rec['inputs'][str(p.relative_to(R))]=sha(p)
 for k in ['hard_paid']:
  e=t['allowed_packages'][k];assert sha(R/e['manifest'])==e['sha256']
 oldM=json.loads((R/t['allowed_packages']['hard_paid']['manifest']).read_text());oldC=R/oldM['canonical_certificate'];assert sha(oldC)==oldM['certificate_sha256'];old=json.loads(oldC.read_text())
 rec['controls']['completed_engine_controls_inherited']=dict(certificate=str(oldC.relative_to(R)),sha256=sha(oldC),controls=old['controls'],independent=False)
 records={e['module']:e for e in old['reused_producers']+old['new_producers']};oldSources={e['module']:e for e in old['sources']}
 receipts=[]
 for p in B.glob('compile-*/receipt.json'):
  c=json.loads(p.read_text())
  if c.get('status')=='PASS_AUTHOR_GUARDED_SOURCE_COMPILE':receipts.append((p,c))
 for n in sorted(full|{'HandlerSourceControls'}):
  assert sha(D/(n+'.lean'))==sha(B/(n+'.lean'))
  assert any(r['module']==n and r['exit']==0 and r['source_sha256']==sha(D/(n+'.lean')) for p,c in receipts for r in c['runs']),('NO_COMPILE_RECEIPT',n)
 neg=[(p,c) for p,c in receipts if any(r['module']=='HandlerSourceFalseControls' and r['exit']==1 and r['source_sha256']==sha(D/'HandlerSourceFalseControls.lean') for r in c['runs'])];assert neg
 p,c=neg[-1];log=(p.parent/'HandlerSourceFalseControls.log').read_text();errs=re.findall(r': error(?:\([^)]*\))?: ([^\n]*)',log)
 assert len(errs)==3 and 'sorry' not in log and all(e=='unsolved goals' or e.startswith('Tactic `decide` proved that the proposition') for e in errs)
 rec['controls']['three_targeted_corruptions']=dict(receipt=str(p.relative_to(R)),sha256=sha(p),errors=errs)
 resolve=lambda n:(B/(n+'.lean'),B/(n+'.olean'))
 order=closure(['HandlerSourceControls'],resolve)
 for n in order:
  p,o=resolve(n);rec['sources'].append(dict(module=n,source_sha256=sha(p),olean_sha256=sha(o)))
 (O/'lean-toolchain').write_bytes((B/'lean-toolchain').read_bytes())
 (O/'Header.lean').write_text(header_source(order));counts,expected=parse_header(run(O,'Header',B),order,B)
 def check(n,rows,cnts=counts,exp=expected):
  A.parse_producer(dict(producer=n,count=cnts[n]),rows)
  assert [(r['index'],r['actual_name'],r['kind']) for r in rows]==exp[n],('HEADER_MISMATCH',n)
  for r in rows:
   if r['kind'] in {'definition','opaque'}:assert r['has_body'] and r['body']!='<none>'
 baseRows={};merged=[];fresh=[]
 for n in order:
  if n in records and n in oldSources and sha(B/(n+'.lean'))==oldSources[n]['source_sha256'] and sha(B/(n+'.olean'))==oldSources[n]['olean_sha256']:
   e=records[n];p=R/e['path'];assert sha(p)==e['sha256'];rows=read_rows(p);check(n,rows)
   baseRows[n]=fingerprint(rows);merged+=baseRows[n];rec['reused_producers'].append(e)
  else:fresh.append(n)
 print('CLOSURE',len(order),'FRESH',len(fresh),flush=True);save()
 assert json.loads((B/'SEED.json').read_text())['object_identity_differences']==[], 'UNEXPECTED_IMPORT_OBJECT_SUBSTITUTION'
 total=0
 for i,n in enumerate(fresh):
  idx,folder=extract(O,order,[n],B,'Source'+str(i));assert not idx['rejects'];e=idx['producer_counts'][0];p=folder/e['file'];rows=read_rows(p);check(n,rows)
  total+=p.stat().st_size;assert total<=256*(1<<20)
  if n in full:assert all(r['body_text_scope']=='FULL_ALL_BODY' for r in rows)
  merged+=fingerprint(rows);rec['new_producers'].append(dict(module=n,path=str(p.relative_to(R)),sha256=sha(p),stored_occurrences=len(rows),compressed_bytes=p.stat().st_size,full_proof_bodies=n in full));save();print('SOURCE_EXTRACTED',i+1,'OF',len(fresh),flush=True)
 assert len(merged)==sum(counts.values());compat=G.inspect(merged);assert not compat['rejects'];(O/'COMPATIBILITY.json').write_text(json.dumps(compat,indent=2)+'\n')
 axioms=sorted({a for r in merged for a in r['axiom_references']});assert set(axioms)<=A.ALLOWED
 for e in rec['sources']:assert sha(B/(e['module']+'.lean'))==e['source_sha256'] and sha(B/(e['module']+'.olean'))==e['olean_sha256']
 for p,h in rec['inputs'].items():assert sha(R/p)==h
 rec.update(status='PASS_AUTHOR_GOOD_PAIR_FULL_SOURCE_BOUND_AND_ORDINARY_PREPARATION_STAGE',actual_imported_modules=len(order),fresh_producer_modules=len(fresh),full_proof_body_modules=len(full),stored_declarations=len(merged),axiom_union=axioms,compressed_bytes=total,scope='Complete literal GoodPairDP.runPair source value/Nat callback split/local polynomial and actual selected-edge sharp weighted forest-debit bound; fixed-base uniform hard-paid caseMass cap and closed hard-paid uniform corollary. Complete ordinary properBlock/slot/prepare source/value/polynomial. Remaining ordinary scheduler/reconstruction, disjoint endpoint, BothBad and full hard2 composition OPEN.')
 save();print(rec['status'],len(order),len(fresh),len(merged),flush=True)
except BaseException as e:rec.update(status='FAILED_NOT_ACCEPTED',error=repr(e));save();raise
