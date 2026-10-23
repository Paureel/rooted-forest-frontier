# One-shot actual work consumer audit. Frozen header, compressed body extractor,
# producer gate and value-compatibility gate are reused without modification.
from pathlib import Path
import ast,datetime,gzip,hashlib,importlib.util,json,os,re,resource,selectors,shlex,shutil,signal,subprocess,time
D=Path(__file__).resolve().parent;R=D.parents[5]
B=R/json.loads((D/'LATEST-BUILD-v1.json').read_text())['directory']
M=D.parent/'hard2_query_size/HARD2-SIZE-MANIFEST-v1.json'
V=D.parent/'resume_20261015T1810Z/compressed_pool_resume_v3.py'
O=R/'results'/('algorithm-universal233-ordinary-work-audit-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'));O.mkdir()
def load(n,p):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
A=load('work_producer_gate',R/'research/rmaf/algorithm/universal233/rule5_common_split/audit_graph.py')
G=load('work_value_gate',D.parent/'producer_compatibility/compatibility.py')
wanted={'sha','string_sha','pin','margin','cap','run','source','header_source','parse_header','extract','read_rows','fingerprint'}
parts=[n for n in ast.parse(V.read_text()).body if isinstance(n,ast.FunctionDef) and n.name in wanted];assert {n.name for n in parts}==wanted
exec(compile(ast.Module(body=parts,type_ignores=[]),str(V),'exec'),globals())
rec=dict(status='FRESH_WORK_CONSUMER_CONTROLS',all_main_milestones='OPEN',independent_acceptance=False,runtime_claim=False,runs=[],inputs={},controls={},sources=[],reused_producers=[],new_producers=[])
def save():(O/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n')
for p in [Path(__file__),V,Path(A.__file__),Path(G.__file__),M,D/'TARGET-v1.md',D/'CONTROLS-PIN-v1.md',D/'compile_development_v1.py',D/'build_components_v1.py',D/'extend_rule5_v1.py',B/'certificate-v1.json',B/'rule5-extension-v1/certificate.json']:
 rec['inputs'][str(p.relative_to(R))]=sha(p)
(O/'lean-toolchain').write_bytes((B/'lean-toolchain').read_bytes());save()
try:
 assert sha(V)=='626e3f21ba70fb417ad1085995a88b4af217a1b6f210191fa58ca442aad0098a'
 assert sha(M)=='dbb5959912e70269374cb980a4e0501674bbf65829fb69e1a03b1ec87edf3e3b'
 mm=json.loads(M.read_text());P=R/mm['canonical_build'];PA=R/mm['canonical_audit'];pins0={e['path']:e['sha256'] for e in mm['immutable_files']}
 assert sha(PA/'certificate.json')==pins0[str((PA/'certificate.json').relative_to(R))]
 old=json.loads((PA/'certificate.json').read_text());assert old['status']=='PASS_AUTHOR_ACTUAL_HARD2_QUERY_SIZE_SOURCE_PRODUCER'
 rec['controls']['exact_generator_inherited']=old['controls']['exact_generator_inherited'];rec['exact_generator_control_origin']=old['exact_generator_control_origin']
 def nonproof(rows):
  for r in rows:
   if r['kind'] in {'definition','opaque'}:assert r['has_body'] and r['body'] and r.get('body_text_scope','FULL_NONPROOF_BODY')=='FULL_NONPROOF_BODY',('MISSING_NONPROOF_BODY',r['actual_name'])
 planted=dict(producer='WorkOpaquePlant',kind='opaque',actual_name='WorkOpaquePlant.value',has_body=True,type='Nat',body='Nat.zero',body_text_scope='FULL_NONPROOF_BODY')
 nonproof([planted])
 for k,v in [('has_body',False),('body',''),('body_text_scope','OMITTED_THEOREM_PROOF_TEXT')]:
  try:nonproof([dict(planted,**{k:v})])
  except AssertionError:rec['controls']['opaque_'+k]='CAUGHT'
  else:raise AssertionError('OPAQUE_CORRUPTION_ACCEPTED')
 assert not G.inspect(fingerprint([planted,dict(planted,producer='WorkOpaqueTwin')]))['rejects']
 assert G.inspect(fingerprint([planted,dict(planted,producer='WorkOpaqueBad',body='Nat.succ Nat.zero')]))['rejects'];rec['controls']['nonproof_actual_body_comparison']='PLANT_PASS_CORRUPTION_CAUGHT'
 base=json.loads((B/'certificate-v1.json').read_text());extension=json.loads((B/'rule5-extension-v1/certificate.json').read_text())
 assert base['status']=='PASS_AUTHOR_WORK_COMPONENT_BUILD_PENDING_ACTUAL_CONSUMERS_AUDIT' and extension['status']=='PASS_AUTHOR_WORK_RULE5_EXTENSION_PENDING_ACTUAL_CONSUMER_AUDIT'
 for c in [base,extension]:
  for p,h in c['inputs'].items():assert sha(R/p)==h,('BUILD_INPUT_CHANGED',p)
 entries={e['module']:e for e in extension['source_entries']};receipts=[]
 for p in B.glob('live-compile-*/receipt.json'):
  c=json.loads(p.read_text())
  if c.get('status')=='PASS_AUTHOR_LIVE_GUARDED_COMPILE':receipts.append((p,c))
 own=['QueryProperBase','PairQueryProper','ModeQueryProper','Hard2QueryProper','Hard2Frontier','Hard2StepTrace','Hard2SourceBill','WorkControls']
 for n in own:
  assert sha(D/(n+'.lean'))==sha(B/(n+'.lean'))
  assert any(any(r['module']==n and r['exit']==0 and r['expected_exit']==0 and r['source_sha256']==sha(B/(n+'.lean')) for r in c['runs']) for p,c in receipts),('NO_SOURCE_RECEIPT',n)
 false=[(p,c) for p,c in receipts if any(r['module']=='WorkFalseControls' and r['exit']==1 and r['expected_exit']==1 and r['source_sha256']==sha(D/'WorkFalseControls.lean') for r in c['runs'])];assert false
 fp,fc=sorted(false)[-1];log=(fp.parent/'WorkFalseControls.log').read_text();errs=re.findall(r': error(?:\([^)]*\))?: ([^\n]*)',log)
 assert len(errs)==4 and 'sorry' not in log and all(e=='unsolved goals' or e.startswith('Tactic `decide` proved that the proposition') for e in errs),('FALSE_DIAGNOSTIC_GATE',errs)
 rec['controls']['actual_false_claims']=dict(path=str(fp.relative_to(R)),sha256=sha(fp),errors=errs)
 order=[];seen=set()
 def visit(n):
  if n in seen:return
  p=B/(n+'.lean');assert p.exists()
  for dep in re.findall(r'^import ([A-Za-z0-9_\'.]+)\s*$',p.read_text(),re.M):
   if dep.split('.')[0] not in {'Std','Lean','Init'}:visit(dep)
  seen.add(n);order.append(n)
 for n in own:visit(n)
 records={e['module']:e for e in old['reused_producers']+old['new_producers']};fresh=[];pins={}
 for n in order:
  p=B/(n+'.lean');o=B/(n+'.olean');pins[str(p.relative_to(R))]=sha(p);pins[str(o.relative_to(R))]=sha(o)
  reuse=n in records and (P/p.name).exists() and (P/o.name).exists() and sha(p)==sha(P/p.name) and sha(o)==sha(P/o.name)
  if reuse:assert sha(p)==pins0[str((P/p.name).relative_to(R))] and sha(o)==pins0[str((P/o.name).relative_to(R))]
  else:
   fresh.append(n)
   if n in own:assert sha(p)==sha(D/p.name)
   else:
    e=entries.get(n)
    if e:
     assert sha(p)==e['sha256']
     for origin in e['origins']:
      op=R/origin['source'];assert sha(op)==origin['source_sha256'];lines=[]
      for line in op.read_text().splitlines(keepends=True):
       m=re.fullmatch(r'import ([A-Za-z0-9_\'.]+)\s*',line)
       if m and m[1] in origin['import_adaptations']:line='import '+origin['import_adaptations'][m[1]]+'\n'
       lines.append(line)
      assert string_sha(''.join(lines))==sha(p),('ADAPTATION_MISMATCH',n,origin)
    assert any(r['module']==n and r['exit']==0 and r['expected_exit']==0 and r['source_sha256']==sha(p) for c in [base,extension] for r in c['runs']),('NO_UNION_SOURCE_RECEIPT',n)
  rec['sources'].append(dict(module=n,source_sha256=sha(p),olean_sha256=sha(o),mode='EXACT_SEALED_BINARY_RECORD_REUSE' if reuse else 'FRESH_ACTUAL_PRODUCER_EXTRACTION',source_origins=entries.get(n,{}).get('origins',[])))
 (O/'BUILD-PINS.json').write_text(json.dumps(pins,indent=2)+'\n');save();print('ACTUAL_CLOSURE',len(order),'FRESH',len(fresh),flush=True)
 (O/'FreshHeader.lean').write_text(header_source(order));hlog=run(O,'FreshHeader',B);counts,expected=parse_header(hlog,order,B)
 for label,bad in [('foreign_path',hlog.replace(str(B/'RMAF.olean'),'/tmp/foreign/RMAF.olean',1)),('missing_path',re.sub(r'^PATH\|RMAF\|.*\n','',hlog,flags=re.M))]:
  try:parse_header(bad,order,B)
  except AssertionError:rec['controls'][label]='CAUGHT'
  else:raise AssertionError('PATH_CORRUPTION_ACCEPTED')
 def check(n,rr):
  A.parse_producer(dict(producer=n,count=counts[n]),rr);assert [(r['index'],r['actual_name'],r['kind']) for r in rr]==expected[n],('HEADER_MISMATCH',n);nonproof(rr)
 rows=[]
 for n in order:
  if n in fresh:continue
  e=records[n];p=R/e['path'];assert sha(p)==e['sha256'];rr=read_rows(p);check(n,rr);rows+=fingerprint(rr);rec['reused_producers'].append(e);del rr
 pp=B/(order[0]+'.lean');expected_pin=sha(pp)
 try:assert string_sha(pp.read_text()+'\n')==expected_pin
 except AssertionError:rec['controls']['source_pin_corruption']='CAUGHT'
 else:raise AssertionError('SOURCE_CORRUPTION_ACCEPTED')
 n=rec['reused_producers'][0]['module'];rr=read_rows(R/rec['reused_producers'][0]['path'])
 for label,bad in [('missing_row',rr[:-1]),('duplicate_row',rr+[rr[0]])]:
  try:check(n,bad)
  except AssertionError:rec['controls'][label]='CAUGHT'
  else:raise AssertionError('INVENTORY_CORRUPTION_ACCEPTED')
 save();total=0
 for i in range(0,len(fresh),6):
  margin();shard=fresh[i:i+6];idx,folder=extract(O,order,shard,B,'Work'+str(i//6));assert not idx['rejects']
  for entry in idx['producer_counts']:
   n=entry['producer'];p=folder/entry['file'];total+=p.stat().st_size;assert total<=768*(1<<20),'TOTAL_COMPRESSED_OUTPUT_CAP'
   rr=read_rows(p);check(n,rr);rows+=fingerprint(rr);rec['new_producers'].append(dict(module=n,path=str(p.relative_to(R)),sha256=sha(p),stored_occurrences=len(rr),compressed_bytes=p.stat().st_size));del rr
  save();print('WORK_EXTRACTED',min(i+6,len(fresh)),'OF',len(fresh),'BYTES',total,flush=True)
 assert len(rows)==sum(counts.values());merged=G.inspect(rows);(O/'COMPATIBILITY.json').write_text(json.dumps(merged,indent=2)+'\n');assert not merged['rejects'],merged['rejects']
 axioms=sorted({a for r in rows for a in r['axiom_references']});assert axioms==['Classical.choice','Quot.sound','propext']
 for p,h in pins.items():assert sha(R/p)==h,'BUILD_CHANGED'
 for p,h in rec['inputs'].items():assert sha(R/p)==h,'INPUT_CHANGED'
 rec.update(status='PASS_AUTHOR_ACTUAL_HARD2_WORK_CONSUMER_SOURCE_PRODUCER',actual_imported_modules=len(order),new_own_builds=len(own),fresh_actual_producers=len(fresh),new_stored_occurrences=sum(e['stored_occurrences'] for e in rec['new_producers']),selected_stored_occurrences=len(rows),axiom_union=axioms,compressed_bytes=total,
  interfaces=['OrdinaryDispatch.WorkIntegration.hard2Trace_value','OrdinaryDispatch.WorkIntegration.hard2Trace_mass','OrdinaryDispatch.WorkIntegration.hard2Trace_query_bounds','OrdinaryDispatch.WorkIntegration.hard2Trace_query_potential','OrdinaryDispatch.WorkIntegration.combined_source_bill_bound','OrdinaryDispatch.WorkIntegration.disjoint_source_bill_bound','OrdinaryDispatch.WorkIntegration.hard2_ordinary_work_bound'],
  full_source_bit_payload_recurrence='OPEN',source_bill_runtime_correspondence='OPEN',scope='Actual full hard2 dispatcher value and ordinary query occurrence trace, mass gamma(233/100), strict proper smaller calls and both target sizes. Non-Rule5 actual full-forest declared source sheets bounded using only smaller actual-query bills, with forest overhead coefficient once. Concrete nonrecursive dispatcher/local Rule5/scalar bit work remain OPEN. Full nonproof bodies retained, actual theorem proof references traversed; exact finite selected source/binary union only; same-author lineage, no independent acceptance.')
 save();print(rec['status'],len(order),len(rows),len(fresh),flush=True)
except BaseException as e:rec.update(status='FAILED_NOT_ACCEPTED',error=repr(e));save();raise
finally:(D/'LATEST-AUDIT-v1.json').write_text(json.dumps(dict(directory=str(O.relative_to(R)),certificate_sha256=sha(O/'certificate.json')),indent=2)+'\n')
