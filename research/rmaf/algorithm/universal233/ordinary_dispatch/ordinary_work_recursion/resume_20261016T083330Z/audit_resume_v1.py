# One-shot author continuation audit. Exact completed extractor/compatibility
# engines reused; new small producers retain FULL theorem and nonproof bodies.
from pathlib import Path
import ast,datetime,gzip,hashlib,importlib.util,json,os,re,resource,selectors,shlex,shutil,signal,subprocess,time
D=Path(__file__).resolve().parent;R=D.parents[6]
B=R/json.loads((D/'RESUME-BUILD-v1.json').read_text())['directory']
V=D.parent.parent/'resume_20261015T1810Z/compressed_pool_resume_v3.py'
O=B/'author-source-audit-v1';assert not O.exists();O.mkdir()
def load(n,p):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
A=load('global_resume_producer_gate',R/'research/rmaf/algorithm/universal233/rule5_common_split/audit_graph.py')
G=load('global_resume_value_gate',D.parent.parent/'producer_compatibility/compatibility.py')
class MemoryCap(ast.NodeTransformer):
 def visit_Call(self,n):
  self.generic_visit(n)
  if isinstance(n.func,ast.Attribute) and isinstance(n.func.value,ast.Name) and n.func.value.id=='subprocess' and n.func.attr=='Popen':
   assert isinstance(n.args[0],ast.BinOp)
   n.args[0].left.left.elts.append(ast.Constant(value='--memory=3072'))
  return n
wanted={'sha','string_sha','pin','margin','cap','run','source','header_source','parse_header','extract','read_rows','fingerprint'}
parts=[n for n in ast.parse(V.read_text()).body if isinstance(n,ast.FunctionDef) and n.name in wanted]
assert {n.name for n in parts}==wanted
for n in parts:
 n=MemoryCap().visit(n);exec(compile(ast.fix_missing_locations(ast.Module(body=[n],type_ignores=[])),str(V),'exec'),globals())
compressed_source=source
def source(imports,modules,out):
 s=compressed_source(imports,modules,out)
 a='let body := match ci with | .thmInfo _ => none | _ => ci.value? true'
 assert s.count(a)==1;s=s.replace(a,'let body := ci.value? true')
 a='match ci with | .thmInfo _ => "OMITTED_THEOREM_PROOF_TEXT" | _ => "FULL_NONPROOF_BODY"'
 assert s.count(a)==1;return s.replace(a,'"FULL_ALL_BODY"')
rec=dict(status='CHECKING_AUTHOR_SOURCE_CONTINUATION',independent_acceptance=False,
 all_main_milestones='OPEN',runtime_claim=False,runs=[],controls={},inputs={},sources=[],
 reused_producers=[],new_producers=[],targets=[])
def save():(O/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n')
save()
try:
 M=D.parent.parent/'allgood_local_work/ALLGOOD-WORK-MANIFEST-v1.json'
 assert sha(M)=='3521617a9057a12def4b39222456a2acf3a68b69338f751ecb2e51a40bdab9a9'
 assert sha(V)=='626e3f21ba70fb417ad1085995a88b4af217a1b6f210191fa58ca442aad0098a'
 manifest=json.loads(M.read_text());oldpath=R/manifest['canonical_audit']/'certificate.json'
 assert sha(oldpath)==manifest['certificate_sha256'];old=json.loads(oldpath.read_text())
 assert old['status']=='PASS_AUTHOR_ACTUAL_ALLGOOD_DP_SOURCE_WORK_PRODUCER'
 for p in [Path(__file__),V,Path(A.__file__),Path(G.__file__),M,oldpath,B/'RESUME-SEED-RECEIPT.json',D/'compile_resume_v1.py',D/'RESUME-SKELETON-v1.md']:
  rec['inputs'][str(p.relative_to(R))]=sha(p)
 for p in [V,Path(A.__file__),Path(G.__file__)]:assert old['inputs'][str(p.relative_to(R))]==sha(p)
 seed=json.loads((B/'RESUME-SEED-RECEIPT.json').read_text());assert seed['status']=='PASS_EXACT_CHECKPOINT_CONTINUATION_SEED'
 own0=[e['module'] for e in seed['own_completed']]
 own=['OrdinaryStepTrace','OrdinaryStepBounds','OrdinaryCallNodes','OrdinaryCallBound','OrdinaryCallControls']
 receipts=[]
 for p in B.glob('resume-compile-*/receipt.json'):
  c=json.loads(p.read_text())
  if c.get('status')=='PASS_AUTHOR_RESUME_GUARDED_COMPILE':receipts.append((p,c))
 for n in own:
  assert sha(D/(n+'.lean'))==sha(B/(n+'.lean'))
  assert any(r['module']==n and r['exit']==0 and r['source_sha256']==sha(D/(n+'.lean')) for p,c in receipts for r in c['runs'])
 negative=[(p,c) for p,c in receipts if any(r['module']=='OrdinaryCallFalseControls' and r['exit']==1 and r['expected_exit']==1 and r['source_sha256']==sha(D/'OrdinaryCallFalseControls.lean') for r in c['runs'])]
 assert negative
 p,c=negative[-1];text=(p.parent/'OrdinaryCallFalseControls.log').read_text();errors=re.findall(r': error(?:\([^)]*\))?: ([^\n]*)',text)
 assert len(errors)==2 and 'sorry' not in text and all(e=='unsolved goals' or e.startswith('Tactic `decide` proved that the proposition') for e in errors)
 rec['controls']['targeted_false_counts']=dict(receipt=str(p.relative_to(R)),sha256=sha(p),mathematical_failures=errors)
 rec['controls']['exact_extractor_controls_inherited']=dict(receipt=str(oldpath.relative_to(R)),sha256=sha(oldpath),controls=old['controls'],same_lineage=True)
 order=[];seen=set()
 def visit(n):
  if n in seen:return
  p=B/(n+'.lean');assert p.exists(),n
  for dep in re.findall(r'^import ([A-Za-z0-9_\'.]+)\s*$',p.read_text(),re.M):
   if dep.split('.')[0] not in {'Std','Lean','Init'}:visit(dep)
  seen.add(n);order.append(n)
 for n in own:visit(n)
 records={e['module']:e for e in old['reused_producers']+old['new_producers']}
 seedrecords={e['module']:e for e in seed['sources']+seed['own_completed']}
 pins={};fresh=[]
 for n in order:
  p=B/(n+'.lean');o=B/(n+'.olean');pins[str(p.relative_to(R))]=sha(p);pins[str(o.relative_to(R))]=sha(o)
  if n not in own:
   e=seedrecords[n];assert sha(p)==e['source_sha256'] and sha(o)==e['olean_sha256']
  if n in own0+own:fresh.append(n)
  else:assert n in records,n
  rec['sources'].append(dict(module=n,source_sha256=sha(p),olean_sha256=sha(o),mode='FRESH_FULL_BODY_EXTRACTION' if n in fresh else 'EXACT_COMPLETED_PRODUCER_RECORD_REUSE'))
 (O/'BUILD-PINS.json').write_text(json.dumps(pins,indent=2)+'\n');save()
 (O/'lean-toolchain').write_bytes((B/'lean-toolchain').read_bytes())
 (O/'FreshHeader.lean').write_text(header_source(order));header=run(O,'FreshHeader',B);counts,expected=parse_header(header,order,B)
 for name,bad in [('foreign_path',header.replace(str(B/'RMAF.olean'),'/tmp/foreign/RMAF.olean',1)),('missing_path',re.sub(r'^PATH\|RMAF\|.*\n','',header,flags=re.M))]:
  try:parse_header(bad,order,B)
  except AssertionError:rec['controls'][name]='CAUGHT'
  else:raise AssertionError('HEADER_CORRUPTION_ACCEPTED')
 def check(n,rows):
  A.parse_producer(dict(producer=n,count=counts[n]),rows)
  assert [(r['index'],r['actual_name'],r['kind']) for r in rows]==expected[n]
  for r in rows:
   if r['kind'] in {'definition','opaque'}:assert r['has_body'] and r['body'] and r.get('body_text_scope','FULL_NONPROOF_BODY')!='OMITTED_THEOREM_PROOF_TEXT'
 merged=[]
 for n in order:
  if n in fresh:continue
  e=records[n];p=R/e['path'];assert sha(p)==e['sha256'];rows=read_rows(p);check(n,rows)
  merged+=fingerprint(rows);rec['reused_producers'].append(e)
 print('ACTUAL_CLOSURE',len(order),'FRESH_FULL_BODY',len(fresh),flush=True);save()
 total=0
 names=['forestWork_cast','forestWork_split','ordinaryStepTrace_value','ordinaryStepTrace_bounds','ordinaryStepTrace_lex','ordinaryStepTrace_paid_mass','ordinaryStepTrace_common_or_paid','ordinaryCallNodes','ordinaryCallNodes_eq','ordinaryCallNodes_bound','ordinaryCallNodes_bound_aux','common_zero_literal','failed_duplicate_occurrences']
 for i in range(0,len(fresh),4):
  idx,folder=extract(O,order,fresh[i:i+4],B,'Resume'+str(i//4));assert not idx['rejects']
  for e in idx['producer_counts']:
   n=e['producer'];p=folder/e['file'];total+=p.stat().st_size;assert total<=256*(1<<20)
   rows=read_rows(p);check(n,rows)
   assert all(r.get('body_text_scope')=='FULL_ALL_BODY' for r in rows)
   for r in rows:
    if r['actual_name'].split('.')[-1] in names:
     assert r['has_body'] and r['body']!='<none>'
     rec['targets'].append(dict(name=r['actual_name'],producer=n,type_sha256=string_sha(r['type']),body_sha256=string_sha(r['body']),body_bytes=len(r['body']),axioms=r['axiom_references'],record=str(p.relative_to(R)),record_sha256=sha(p)))
   merged+=fingerprint(rows)
   rec['new_producers'].append(dict(module=n,path=str(p.relative_to(R)),sha256=sha(p),stored_occurrences=len(rows),compressed_bytes=p.stat().st_size))
  save();print('FULL_BODY_EXTRACTED',min(i+4,len(fresh)),'OF',len(fresh),'BYTES',total,flush=True)
 assert len(merged)==sum(counts.values())
 compatibility=G.inspect(merged);assert not compatibility['rejects']
 (O/'COMPATIBILITY.json').write_text(json.dumps(compatibility,indent=2)+'\n')
 axioms=sorted({a for r in merged for a in r['axiom_references']});assert set(axioms)<=A.ALLOWED
 assert {r['name'].split('.')[-1] for r in rec['targets']}==set(names)
 for p,h in pins.items():assert sha(R/p)==h
 for p,h in rec['inputs'].items():assert sha(R/p)==h
 rec.update(status='PASS_AUTHOR_SOURCE_BOUND_ORDINARY_CALL_RECURRENCE',actual_imported_modules=len(order),fresh_full_body_modules=len(fresh),stored_occurrences=len(merged),compressed_bytes=total,axiom_union=axioms,
  body_qualification='New and resumed small producers: full exact Expr repr for theorem/definition/opaque bodies. Older completed producer records preserve their original qualified theorem-text omission, with actual proof reference and axiom closure.',
  scope='Exact FastOrdinary.solve one-step value/ordered-query binding and universal invocation count <=1024*(n+1)*(233/100)^q. Includes same-q common contractions, all failed and duplicate ordinary query occurrences. Full local ordinary/Rule5 source sheet, fresh-label bit growth, bounded primitive provider, native/IR cost correspondence and full-runtime/base acceptance remain OPEN.')
 save();print(rec['status'],len(order),len(fresh),len(merged),flush=True)
except BaseException as e:
 rec.update(status='FAILED_NOT_ACCEPTED',error=repr(e));save();raise
