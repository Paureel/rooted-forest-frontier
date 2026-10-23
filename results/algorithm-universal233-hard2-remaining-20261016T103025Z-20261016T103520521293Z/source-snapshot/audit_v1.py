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
full={'Hard2GeneratorSource','Hard2OutputGenerationSource','Hard2GenerationBound','Hard2SelectedGenerationBound','Hard2FullOutputBound','Hard2OutputWeightedBound','HardPaidSourceBound'}
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
 T=R/'research/rmaf/monitoring/next-20261016T103025Z/MAIN-HARD2-REMAINING-TARGET-v1.json';assert sha(T)=='1d7630704bd30255e2c3b8f09fdac57e1790d43760ae211230d5a4f874866e29';t=json.loads(T.read_text())
 for p in [Path(__file__),D.parent/'ordinary_full_source_integration_20261016T092805Z/audit_v2.py',V,P,Path(A.__file__),Path(G.__file__),T,B/'SEED.json',D/'compile_v1.py',D/'CONTROLS-PIN-v1.md']:rec['inputs'][str(p.relative_to(R))]=sha(p)
 for k in ['hard2_front','actual_recovery_source','optimizer_fees']:
  e=t['allowed_packages'][k];assert sha(R/e['manifest'])==e['sha256']
 oldM=json.loads((R/t['allowed_packages']['hard2_front']['manifest']).read_text());oldC=R/oldM['canonical_certificate'];assert sha(oldC)==oldM['certificate_sha256'];old=json.loads(oldC.read_text())
 rec['controls']['completed_engine_controls_inherited']=dict(certificate=str(oldC.relative_to(R)),sha256=sha(oldC),controls=old['controls'],independent=False)
 records={e['module']:e for e in old['reused_producers']+old['new_producers']};oldSources={e['module']:e for e in old['sources']}
 receipts=[]
 for p in B.glob('compile-*/receipt.json'):
  c=json.loads(p.read_text())
  if c.get('status')=='PASS_AUTHOR_GUARDED_SOURCE_COMPILE':receipts.append((p,c))
 for n in sorted(full|{'HardPaidSourceControls'}):
  assert sha(D/(n+'.lean'))==sha(B/(n+'.lean'))
  assert any(r['module']==n and r['exit']==0 and r['source_sha256']==sha(D/(n+'.lean')) for p,c in receipts for r in c['runs']),('NO_COMPILE_RECEIPT',n)
 neg=[(p,c) for p,c in receipts if any(r['module']=='HardPaidSourceFalseControls' and r['exit']==1 and r['source_sha256']==sha(D/'HardPaidSourceFalseControls.lean') for r in c['runs'])];assert neg
 p,c=neg[-1];log=(p.parent/'HardPaidSourceFalseControls.log').read_text();errs=re.findall(r': error(?:\([^)]*\))?: ([^\n]*)',log)
 assert len(errs)==3 and 'sorry' not in log and all(e=='unsolved goals' or e.startswith('Tactic `decide` proved that the proposition') for e in errs)
 rec['controls']['three_targeted_corruptions']=dict(receipt=str(p.relative_to(R)),sha256=sha(p),errors=errs)
 resolve=lambda n:(B/(n+'.lean'),B/(n+'.olean'))
 order=closure(['HardPaidSourceControls'],resolve)
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
 seed=json.loads((B/'SEED.json').read_text());ctx=[R/p for p in seed['recovery_original_contexts']];dep={e['module']:e for e in seed['recovery_closure']}
 def original(n):
  e=dep[n];p=R/e['source'];o=R/e['olean'];assert sha(p)==e['source_sha256'] and sha(o)==e['olean_sha256'];return p,o
 altOrder=closure(['RWInitial'],original);pathroot=os.pathsep.join(map(str,ctx))
 (O/'AlternativeHeader.lean').write_text(header_source(altOrder));ah=run(O,'AlternativeHeader',pathroot)
 paths=dict(re.findall(r'^PATH\|([^|]+)\|(.+)$',ah,re.M));assert set(altOrder)<=set(paths)
 for n,p in paths.items():
  q=Path(p).resolve();assert q==original(n)[1].resolve() if n in altOrder else q.is_relative_to(R/'.runtime/elan/toolchains'),'FOREIGN_ORIGINAL_CONTEXT_PATH'
 ac=dict((n,int(c)) for n,c in re.findall(r'^COUNT\|([^|]+)\|(\d+)$',ah,re.M));assert set(ac)==set(altOrder)
 ae={n:[] for n in altOrder}
 for n,i,x,k in re.findall(r'^NAME\|([^|]+)\|(\d+)\|([^|]+)\|([^\n]+)$',ah,re.M):ae[n].append((int(i),x,k))
 assert all(len(ae[n])==ac[n] for n in altOrder)
 planted={'Test':dict(name='Test',kind='inductive',full_constant_info='numParams=1')};metadata_compare(planted,planted)
 try:metadata_compare(planted,{'Test':dict(name='Test',kind='inductive',full_constant_info='numParams=2')})
 except AssertionError:rec['controls']['full_metadata_corruption']='CAUGHT'
 else:raise AssertionError('METADATA_CORRUPTION_ACCEPTED')
 different=seed['object_identity_differences']
 for i,e in enumerate(different):
  n=e['module'];p,o=original(n);assert sha(p)==sha(B/p.name) and sha(o)==e['original_olean_sha256']
  idx,folder=extract(O,altOrder,[n],pathroot,'Version'+str(i));assert not idx['rejects'];rowfile=folder/idx['producer_counts'][0]['file'];rows=read_rows(rowfile);check(n,rows,ac,ae)
  chosen=baseRows[n];comparison=G.inspect(chosen+fingerprint(rows))
  assert all(r['decision']=='NONPROOF_METADATA_UNCHECKED' for r in comparison['rejects']),('NONPROOF_VERSION_DIFFERENCE',n,comparison['rejects'])
  bridge=None
  if comparison['rejects']:
   cm,cp=metadata_profile(B,n,'Chosen'+str(i));am,ap=metadata_profile(pathroot,n,'Alternative'+str(i));names={r['name'] for r in comparison['rejects']};assert set(cm)==names and set(am)==names;metadata_compare(cm,am)
   bridge=dict(decision='EXACT_FULL_CONSTANTINFO_METADATA_EQUAL',chosen=str(cp.relative_to(R)),chosen_sha256=sha(cp),alternative=str(ap.relative_to(R)),alternative_sha256=sha(ap),declarations=len(names))
  assert {r['actual_name'] for r in chosen}=={r['actual_name'] for r in rows}
  rec['version_compatibility'].append(dict(module=n,source_sha256=sha(p),chosen_olean_sha256=sha(B/(n+'.olean')),alternative_olean_sha256=sha(o),record=str(rowfile.relative_to(R)),record_sha256=sha(rowfile),decision='EXACT_TYPE_AND_NONPROOF_BODY_COMPATIBLE',metadata_bridge=bridge,theorem_proofs='Proof variation allowed; actual full proof references and axiom closure retained.'))
  save();print('OBJECT_COMPATIBLE',i+1,'OF',len(different),flush=True)
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
 rec.update(status='PASS_AUTHOR_COMPLETE_HARD_PAID_SOURCE_UNIT_BOUND_REMAINING_HANDLERS_OPEN',actual_imported_modules=len(order),fresh_producer_modules=len(fresh),full_proof_body_modules=len(full),stored_declarations=len(merged),axiom_union=axioms,compressed_bytes=total,scope='Complete literal Hard2PaidLocal.actualOutputs/runHardPaid source/value/Nat callback split and polynomial times2.33^q local source bill with sharp per-output weighted forest debit. Exact recovery generator reused, color/init/copy/output fees explicit. GoodPairDP.runPair, DisjointParents.query, BothBadLocal/Grouped and complete hard2 source counter remain OPEN.')
 save();print(rec['status'],len(order),len(fresh),len(merged),flush=True)
except BaseException as e:rec.update(status='FAILED_NOT_ACCEPTED',error=repr(e));save();raise
