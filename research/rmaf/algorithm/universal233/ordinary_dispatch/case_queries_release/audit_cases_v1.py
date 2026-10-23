# One-shot source-bound consumer audit; exact completed bounded extractor reused.
from pathlib import Path
import ast,datetime,gzip,hashlib,importlib.util,json,os,re,resource,selectors,shlex,shutil,signal,subprocess,sys,time
D=Path(__file__).resolve().parent;R=D.parents[5];which=sys.argv[1];W=D.parent/which;B=R/json.loads((W/'LATEST-BUILD-v1.json').read_text())['directory'];P=R/'results/algorithm-universal233-fast-source-pool-20261015T194053203759Z';PA=R/'results/algorithm-universal233-fast-source-audit-20261015T195353361662Z';V=D.parent/'resume_20261015T1810Z/compressed_pool_resume_v3.py';O=R/'results'/('algorithm-universal233-'+which.replace('_','-')+'-audit-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'));O.mkdir()
def load(n,p):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
A=load('case_split_audit',R/'research/rmaf/algorithm/universal233/rule5_common_split/audit_graph.py');G=load('case_values_gate',D.parent/'producer_compatibility/compatibility.py')
names={'sha','string_sha','pin','margin','cap','run','source','header_source','parse_header','extract','read_rows','fingerprint'};parts=[n for n in ast.parse(V.read_text()).body if isinstance(n,ast.FunctionDef) and n.name in names];assert {n.name for n in parts}==names
exec(compile(ast.Module(body=parts,type_ignores=[]),str(V),'exec'),globals())
rec=dict(status='FRESH_CASE_CONTROLS',all_main_milestones='OPEN',independent_acceptance=False,runtime_claim=False,runs=[],inputs={},controls={},sources=[],reused_producers=[],new_producers=[])
def save():(O/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n')
config={'disjoint_parent_query':(['DisjointQuery','MemberComplete','AllGoodParents','DisjointExact','DisjointCounts','Hard2Combine','DisjointControls'],'DisjointFalseControls',3,['OrdinaryDispatch.DisjointParents.query','OrdinaryDispatch.DisjointParents.run_complete','OrdinaryDispatch.DisjointParents.run_minimum','OrdinaryDispatch.DisjointParents.query_mass']), 'pair_allgood_query':(['TwoGroupDP','TwoGroupComplete','ActualPair','PairExecution','PairExact','PairControls'],'PairFalseControls',4,['OrdinaryDispatch.GoodPairDP.runPair','OrdinaryDispatch.GoodPairDP.runPair_complete','OrdinaryDispatch.GoodPairDP.runPair_minimum','OrdinaryDispatch.GoodPairDP.runPair_mass'])};own,false,falsecount,interfaces=config[which]
for p in [Path(__file__),V,Path(A.__file__),Path(G.__file__),W/'TARGET-v1.md',W/'CONTROLS-PIN-v1.md',W/'compile_v1.py',PA/'certificate.json']:rec['inputs'][str(p.relative_to(R))]=sha(p)
save();(O/'lean-toolchain').write_bytes((B/'lean-toolchain').read_bytes())
try:
 M=D.parent/'fast_source_pool/release_v1/FAST-SOURCE-POOL-MANIFEST-v1.json';assert sha(M)=='efa132be64d489544e2aeeffaa0d08494cb9986d28104024f200f1080e2fbb60';pool=json.loads(M.read_text());poolpins={e['path']:e['sha256'] for e in pool['immutable_files']};rec['inputs'][str(M.relative_to(R))]=sha(M)
 pold=json.loads((PA/'certificate.json').read_text());assert pold['status']=='PASS_AUTHOR_FAST_CONSUMER_ONE_ROOT_SOURCE_PRODUCER_AUDIT';assert pold['inputs'][str(V.relative_to(R))]==sha(V);rec['exact_generator_control_origin']=pold['exact_generator_control_origin'];rec['controls']['exact_generator']=pold['controls']['exact_generator']
 receipts=[]
 for p in B.glob('live-compile-*/receipt.json'):
  c=json.loads(p.read_text())
  if c.get('status')=='PASS_AUTHOR_LIVE_GUARDED_COMPILE':receipts.append((p,c))
 for n in own:
  assert sha(W/(n+'.lean'))==sha(B/(n+'.lean'))
  assert any(any(r['module']==n and r['exit']==0 and r['expected_exit']==0 and r['source_sha256']==sha(B/(n+'.lean')) for r in c['runs']) for p,c in receipts),('NO_POSITIVE_RECEIPT',n)
 fs=[(p,c) for p,c in receipts if any(r['module']==false and r['exit']==1 and r['expected_exit']==1 and r['source_sha256']==sha(W/(false+'.lean')) for r in c['runs'])];assert fs,'MISSING_FALSE_CONTROLS';fp,fc=sorted(fs)[-1];log=(fp.parent/(false+'.log')).read_text();errs=re.findall(r': error(?:\([^)]*\))?: ([^\n]*)',log);assert len(errs)==falsecount and 'sorry' not in log and all(e=='unsolved goals' or e.startswith('Tactic `decide` proved that the proposition') for e in errs),('FALSE_DIAGNOSTIC_GATE',errs);rec['controls']['actual_false_claims']=dict(path=str(fp.relative_to(R)),sha256=sha(fp),errors=errs)
 # Fresh field-level guard: proof-text omission never licenses opaque-value loss.
 def nonproof(rr):
  for z in rr:
   if z['kind'] in {'definition','opaque'}:assert z['has_body'] and z['body'] and z.get('body_text_scope','FULL_NONPROOF_BODY')=='FULL_NONPROOF_BODY',('MISSING_NONPROOF_BODY',z['actual_name'])
 sample=[dict(kind='opaque',actual_name='CaseOpaquePlant',has_body=True,body='Nat.zero',body_text_scope='FULL_NONPROOF_BODY')];nonproof(sample)
 for k,v in [('has_body',False),('body',''),('body_text_scope','OMITTED_THEOREM_PROOF_TEXT')]:
  try:nonproof([dict(sample[0],**{k:v})])
  except AssertionError:rec['controls']['opaque_'+k]='CAUGHT'
  else:raise AssertionError('OPAQUE_CORRUPTION_ACCEPTED')
 order=[];seen=set()
 def visit(n):
  if n in seen:return
  p=B/(n+'.lean');assert p.exists()
  for dep in re.findall(r'^import ([A-Za-z0-9_\'.]+)\s*$',p.read_text(),re.M):
   if dep.split('.')[0] not in {'Std','Lean','Init'}:visit(dep)
  seen.add(n);order.append(n)
 for n in own:visit(n)
 pins={};extra={}
 if which=='disjoint_parent_query':
  m=D.parent/'both_bad_local_binding/FINAL-MANIFEST-v1.json';assert sha(m)=='90a3ca2d369ed9f30822a1eb72bad4aea957e9013458ff3a43cb856b2eb964c4';rec['inputs'][str(m.relative_to(R))]=sha(m);cm=json.loads(m.read_text());cp={e['path']:e['sha256'] for e in cm['immutable_files']};C=R/cm['canonical_root'] if 'canonical_root' in cm else R/'results/algorithm-universal233-both-bad-local-root-20261015T195334Z'
  for n in ['CallbackLocality','OrdinaryLocal']:
   for ext in ['.lean','.olean']:assert sha(B/(n+ext))==cp[str((C/(n+ext)).relative_to(R))]
   extra[n]=True
 for n in order:
  p=B/(n+'.lean');o=B/(n+'.olean');pins[str(p.relative_to(R))]=sha(p);pins[str(o.relative_to(R))]=sha(o)
  if n not in own and n not in extra:
   assert sha(p)==poolpins[str((P/p.name).relative_to(R))] and sha(o)==poolpins[str((P/o.name).relative_to(R))],('FROZEN_POOL_DEPENDENCY_CHANGED',n)
  rec['sources'].append(dict(module=n,source_sha256=sha(p),olean_sha256=sha(o),mode='NEW_SOURCE_BUILD' if n in own else 'UNCHANGED_FROZEN_DEPENDENCY'))
 (O/'BUILD-PINS.json').write_text(json.dumps(pins,indent=2)+'\n');save();(O/'FreshHeader.lean').write_text(header_source(order));log=run(O,'FreshHeader',B);counts,expected=parse_header(log,order,B)
 def check(n,c,rr):
  A.parse_producer(c,rr);assert [(r['index'],r['actual_name'],r['kind']) for r in rr]==expected[n];nonproof(rr)
 records={e['module']:e for e in pold['reused_producers']+pold['new_producers']};rows=[];fresh=[]
 for n in order:
  if n in own or n in extra:fresh.append(n);continue
  e=records[n];p=R/e['path'];assert sha(p)==e['sha256'];rr=read_rows(p);check(n,dict(producer=n,count=counts[n]),rr);rows+=fingerprint(rr);rec['reused_producers'].append(dict(module=n,path=e['path'],sha256=e['sha256'],stored_occurrences=len(rr)));del rr
 e=rec['reused_producers'][0];rr=read_rows(R/e['path']);c=dict(producer=e['module'],count=counts[e['module']]);A.parse_producer(c,rr)
 for label,bad in [('missing',rr[:-1]),('duplicate',rr+[rr[0]])]:
  try:A.parse_producer(c,bad)
  except AssertionError:rec['controls']['fresh_merge_'+label]='CAUGHT'
  else:raise AssertionError('ROW_CORRUPTION_ACCEPTED')
 try:assert sha(B/(order[0]+'.lean'))=='corrupted'
 except AssertionError:rec['controls']['fresh_source_pin']='CAUGHT'
 else:raise AssertionError('SOURCE_PIN_CORRUPTION_ACCEPTED')
 save();idx,folder=extract(O,order,fresh,B,'CaseNew');assert not idx['rejects'];newrows=[]
 for c in idx['producer_counts']:
  p=folder/c['file'];rr=read_rows(p);check(c['producer'],c,rr);fr=fingerprint(rr);rows+=fr;newrows+=fr;rec['new_producers'].append(dict(module=c['producer'],path=str(p.relative_to(R)),sha256=sha(p),stored_occurrences=len(rr)));del rr
 compat=G.inspect(rows);(O/'COMPATIBILITY.json').write_text(json.dumps(compat,indent=2)+'\n');assert not compat['rejects'];ax=sorted({a for r in rows for a in r['axiom_references']});assert set(ax)<=A.ALLOWED
 for n in interfaces:assert any(r['actual_name']==n for r in newrows)
 for p,h in pins.items():assert sha(R/p)==h
 for p,h in rec['inputs'].items():assert sha(R/p)==h
 rec.update(status='PASS_AUTHOR_ACTUAL_CASE_QUERY_SOURCE_PRODUCER',case=which,new_builds=len(own),copied_frozen_sources=len(order)-len(own),freshly_extracted_modules=len(fresh),imported_modules=len(order),new_stored_occurrences=sum(r['stored_occurrences'] for r in rec['new_producers'] if r['module'] in own),all_fresh_stored_occurrences=len(newrows),selected_stored_occurrences=len(rows),axiom_union=ax,interfaces=interfaces,scope='Actual named import closure. Dependencies source/binary exact immutable pins; records reused only for identical binaries. New own and new linked BothBadLocal producers freshly extracted. Theorem proof text may be omitted, actual full references walked, every nonproof body present/nonempty/full. Author development lineage, no independent verification or full algorithm/runtime claim.');save();print(rec['status'],which,len(order),rec['new_stored_occurrences'],len(rows),flush=True)
except BaseException as e:rec.update(status='FAILED_NOT_ACCEPTED',error=repr(e));save();raise
finally:(W/'LATEST-AUDIT-v1.json').write_text(json.dumps(dict(directory=str(O.relative_to(R)),certificate_sha256=sha(O/'certificate.json')),indent=2)+'\n')
