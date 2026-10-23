# One-shot actual hard2 root audit. Reuses exact bounded compressed extractor.
from pathlib import Path
import ast,datetime,gzip,hashlib,importlib.util,json,os,re,resource,selectors,shlex,shutil,signal,subprocess,time
D=Path(__file__).resolve().parent;R=D.parents[5];B=R/json.loads((D/'LATEST-BUILD-v1.json').read_text())['directory'];P=R/'results/algorithm-universal233-fast-source-pool-20261015T194053203759Z';PA=R/'results/algorithm-universal233-fast-source-audit-20261015T195353361662Z';V=D.parent/'resume_20261015T1810Z/compressed_pool_resume_v3.py';O=R/'results'/('algorithm-universal233-hard2-dispatch-audit-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'));O.mkdir()
def load(n,p):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
A=load('hard2_split_audit',R/'research/rmaf/algorithm/universal233/rule5_common_split/audit_graph.py');G=load('hard2_value_gate',D.parent/'producer_compatibility/compatibility.py');wanted={'sha','string_sha','pin','margin','cap','run','source','header_source','parse_header','extract','read_rows','fingerprint'};parts=[n for n in ast.parse(V.read_text()).body if isinstance(n,ast.FunctionDef) and n.name in wanted];assert {n.name for n in parts}==wanted;exec(compile(ast.Module(body=parts,type_ignores=[]),str(V),'exec'),globals())
rec=dict(status='FRESH_HARD2_AUDIT_CONTROLS',all_main_milestones='OPEN',independent_acceptance=False,full_faster_solver=False,runtime_claim=False,runs=[],inputs={},controls={},sources=[],reused_producers=[],new_producers=[])
def save():(O/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n')
for p in [Path(__file__),V,Path(A.__file__),Path(G.__file__),D/'TARGET-v1.md',D/'CONTROLS-PIN-v1.md',D/'compile_development_v1.py',D/'build_root_v1.py',D/'extend_final_handlers_v1.py',B/'certificate-v1.json',B/'extension-v1/certificate.json']:rec['inputs'][str(p.relative_to(R))]=sha(p)
(O/'lean-toolchain').write_bytes((B/'lean-toolchain').read_bytes());save()
try:
 m=D.parent/'fast_source_pool/release_v1/FAST-SOURCE-POOL-MANIFEST-v1.json';assert sha(m)=='efa132be64d489544e2aeeffaa0d08494cb9986d28104024f200f1080e2fbb60';poolpins={e['path']:e['sha256'] for e in json.loads(m.read_text())['immutable_files']};rec['inputs'][str(m.relative_to(R))]=sha(m);old=json.loads((PA/'certificate.json').read_text());assert old['status']=='PASS_AUTHOR_FAST_CONSUMER_ONE_ROOT_SOURCE_PRODUCER_AUDIT' and old['inputs'][str(V.relative_to(R))]==sha(V);rec['exact_generator_control_origin']=old['exact_generator_control_origin'];rec['controls']['exact_generator']=old['controls']['exact_generator']
 own=['PairAdapters','Hard2Program','PaidCaseExact','Hard2Exact','PairControls','Hard2Controls'];receipts=[]
 for p in B.glob('live-compile-*/receipt.json'):
  c=json.loads(p.read_text())
  if c.get('status')=='PASS_AUTHOR_LIVE_GUARDED_COMPILE':receipts.append((p,c))
 for n in own:
  assert sha(D/(n+'.lean'))==sha(B/(n+'.lean'));assert any(any(r['module']==n and r['exit']==0 and r['expected_exit']==0 and r['source_sha256']==sha(B/(n+'.lean')) for r in c['runs']) for p,c in receipts),('NO_POSITIVE_SOURCE_RECEIPT',n)
 false=[(p,c) for p,c in receipts if any(r['module']=='Hard2FalseControls' and r['exit']==1 and r['expected_exit']==1 and r['source_sha256']==sha(D/'Hard2FalseControls.lean') for r in c['runs'])];assert false;fp,fc=sorted(false)[-1];log=(fp.parent/'Hard2FalseControls.log').read_text();errs=re.findall(r': error(?:\([^)]*\))?: ([^\n]*)',log);assert len(errs)==4 and 'sorry' not in log and all(e=='unsolved goals' or e.startswith('Tactic `decide` proved that the proposition') for e in errs),('FALSE_DIAGNOSTIC_GATE',errs);rec['controls']['actual_false_claims']=dict(path=str(fp.relative_to(R)),sha256=sha(fp),errors=errs)
 def nonproof(rr):
  for r in rr:
   if r['kind'] in {'definition','opaque'}:assert r['has_body'] and r['body'] and r.get('body_text_scope','FULL_NONPROOF_BODY')=='FULL_NONPROOF_BODY',('MISSING_NONPROOF_BODY',r['actual_name'])
 rr=[dict(kind='opaque',actual_name='Hard2OpaquePlant',has_body=True,body='Nat.zero',body_text_scope='FULL_NONPROOF_BODY')];nonproof(rr)
 for k,v in [('has_body',False),('body',''),('body_text_scope','OMITTED_THEOREM_PROOF_TEXT')]:
  try:nonproof([dict(rr[0],**{k:v})])
  except AssertionError:rec['controls']['opaque_'+k]='CAUGHT'
  else:raise AssertionError('OPAQUE_CORRUPTION_ACCEPTED')
 def adapt(data,changes):
  result=[]
  for line in data.splitlines(keepends=True):
   m=re.fullmatch(r'import ([A-Za-z0-9_\'.]+)\s*',line)
   result.append('import '+changes[m[1]]+'\n' if m and m[1] in changes else line)
  return ''.join(result)
 planted='import PlantBase\n\nnamespace Plant\ndef value : Nat := 0\nend Plant\n';expected_plant='import PlantAlias\n\nnamespace Plant\ndef value : Nat := 0\nend Plant\n'
 assert adapt(planted,{'PlantBase':'PlantAlias'})==expected_plant
 try:assert adapt(planted.replace(':= 0',':= 1'),{'PlantBase':'PlantAlias'})==expected_plant
 except AssertionError:rec['controls']['nonimport_body_corruption']='CAUGHT'
 else:raise AssertionError('BODY_CHANGE_ACCEPTED')
 rec['controls']['exact_import_adaptation_blank_line']='PASS';save()
 order=[];seen=set()
 def visit(n):
  if n in seen:return
  p=B/(n+'.lean');assert p.exists()
  for dep in re.findall(r'^import ([A-Za-z0-9_\'.]+)\s*$',p.read_text(),re.M):
   if dep.split('.')[0] not in {'Std','Lean','Init'}:visit(dep)
  seen.add(n);order.append(n)
 for n in own:visit(n)
 entries={e['module']:e for e in json.loads((B/'extension-v1/certificate.json').read_text())['source_entries']};pins={};fresh=[];records={e['module']:e for e in old['reused_producers']+old['new_producers']}
 # Every adapted source is exact pinned producer text with ONLY named import rewrites.
 for n in order:
  p=B/(n+'.lean');o=B/(n+'.olean');pins[str(p.relative_to(R))]=sha(p);pins[str(o.relative_to(R))]=sha(o)
  if n in entries:
   e=entries[n];assert sha(p)==e['sha256']
   if e.get('origins'):
    for origin in e['origins']:
     op=R/origin['source'];assert sha(op)==origin['source_sha256'];data=op.read_text()
     data=adapt(data,origin.get('import_adaptations',{}))
     assert hashlib.sha256(data.encode()).hexdigest()==sha(p),('ADAPTATION_BEYOND_IMPORTS',n,origin['source'])
  elif n not in own and n not in {'Hard2ConsumersV2'}:raise AssertionError(('UNACCOUNTED_SOURCE',n))
  reused=n in records and (P/(n+'.olean')).exists() and sha(o)==sha(P/(n+'.olean')) and sha(p)==sha(P/(n+'.lean'))
  if reused:assert sha(p)==poolpins[str((P/p.name).relative_to(R))] and sha(o)==poolpins[str((P/o.name).relative_to(R))]
  else:fresh.append(n)
  rec['sources'].append(dict(module=n,source_sha256=sha(p),olean_sha256=sha(o),mode='EXACT_FROZEN_POOL_BINARY_RECORD_REUSE' if reused else 'FRESH_ACTUAL_PRODUCER_EXTRACTION'))
 (O/'BUILD-PINS.json').write_text(json.dumps(pins,indent=2)+'\n');save();(O/'FreshHeader.lean').write_text(header_source(order));log=run(O,'FreshHeader',B);counts,expected=parse_header(log,order,B)
 def check(n,c,rr):
  A.parse_producer(c,rr);assert [(r['index'],r['actual_name'],r['kind']) for r in rr]==expected[n],('ACTUAL_HEADER_MISMATCH',n);nonproof(rr)
 rows=[]
 for n in order:
  if n in fresh:continue
  e=records[n];p=R/e['path'];assert sha(p)==e['sha256'];rr=read_rows(p);check(n,dict(producer=n,count=counts[n]),rr);rows+=fingerprint(rr);rec['reused_producers'].append(dict(module=n,path=e['path'],sha256=e['sha256'],stored_occurrences=len(rr)));del rr
 e=rec['reused_producers'][0];rr=read_rows(R/e['path']);c=dict(producer=e['module'],count=counts[e['module']]);A.parse_producer(c,rr)
 for label,bad in [('missing',rr[:-1]),('duplicate',rr+[rr[0]])]:
  try:A.parse_producer(c,bad)
  except AssertionError:rec['controls']['fresh_merge_'+label]='CAUGHT'
  else:raise AssertionError('ROW_CORRUPTION_ACCEPTED')
 try:assert sha(B/(order[0]+'.lean'))=='corrupted'
 except AssertionError:rec['controls']['fresh_source_pin']='CAUGHT'
 else:raise AssertionError('SOURCE_PIN_CORRUPTION_ACCEPTED')
 save();print('ACTUAL_HARD2_PRODUCERS',len(order),'REUSED',len(rec['reused_producers']),'FRESH',len(fresh),flush=True);newrows=[];total=0
 for start in range(0,len(fresh),10):
  idx,folder=extract(O,order,fresh[start:start+10],B,'Actual'+str(start//10));assert not idx['rejects']
  for c in idx['producer_counts']:
   p=folder/c['file'];total+=p.stat().st_size;assert total<768*(1<<20);rr=read_rows(p);check(c['producer'],c,rr);fr=fingerprint(rr);rows+=fr;newrows+=fr;rec['new_producers'].append(dict(module=c['producer'],path=str(p.relative_to(R)),sha256=sha(p),stored_occurrences=len(rr)));del rr
  save();print('FRESH_ACTUAL',len(rec['new_producers']),len(fresh),flush=True)
 compat=G.inspect(rows);(O/'COMPATIBILITY.json').write_text(json.dumps(compat,indent=2)+'\n');assert not compat['rejects'];ax=sorted({a for r in rows for a in r['axiom_references']});assert set(ax)<=A.ALLOWED
 interfaces=['OrdinaryDispatch.Hard2Dispatcher.run','OrdinaryDispatch.Hard2Dispatcher.paidCase_complete','OrdinaryDispatch.Hard2Dispatcher.run_exact']
 for n in interfaces:assert any(r['actual_name']==n for r in newrows)
 for p,h in pins.items():assert sha(R/p)==h,'ACTUAL_BUILD_CHANGED'
 for p,h in rec['inputs'].items():assert sha(R/p)==h,'INPUT_CHANGED'
 rec.update(status='PASS_AUTHOR_LITERAL_HARD2_DISPATCH_SOURCE_PRODUCER',imported_modules=len(order),new_own_builds=len(own),new_own_stored_occurrences=sum(e['stored_occurrences'] for e in rec['new_producers'] if e['module'] in own),freshly_extracted_modules=len(fresh),fresh_stored_occurrences=len(newrows),selected_stored_occurrences=len(rows),axiom_union=ax,interfaces=interfaces,scope='Actual literal hard2 dispatcher and all closed consumers in one root; exact current-budget QueryExact under printed proper/actualbothhard2/noRule4/rejected0/1/BelowIH context. Every imported stored producer checked, full actual proof reference walk, NPbody present/full. Author same-lineage evidence, no independent/full ordinary solver/fullsource-bit-payload/base/novelty acceptance.');save();print(rec['status'],len(order),len(rows),flush=True)
except BaseException as e:rec.update(status='FAILED_NOT_ACCEPTED',error=repr(e));save();raise
finally:(D/'LATEST-AUDIT-v1.json').write_text(json.dumps(dict(directory=str(O.relative_to(R)),certificate_sha256=sha(O/'certificate.json')),indent=2)+'\n')
