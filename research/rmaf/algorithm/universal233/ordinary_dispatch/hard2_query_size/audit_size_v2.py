# One-shot source-bound audit wrapper; adapted only consumer roots, names and scope from the immutable trace audit.
# One-shot theorem consumer audit; unchanged frozen compressed extractor/gates.
from pathlib import Path
import ast, datetime, gzip, hashlib, importlib.util, json, os, re, resource, selectors, shlex, shutil, signal, subprocess, time
D=Path(__file__).resolve().parent; R=D.parents[5]
B=R/json.loads((D/'LATEST-BUILD-v1.json').read_text())['directory']
P=R/'results/algorithm-universal233-hard2-trace-20261015T205110998851Z'
PA=R/'results/algorithm-universal233-hard2-trace-audit-20261015T205812219432Z'
M=D.parent/'hard2_trace_bound/HARD2-TRACE-MANIFEST-v1.json'
V=D.parent/'resume_20261015T1810Z/compressed_pool_resume_v3.py'
O=R/'results'/('algorithm-universal233-hard2-query-size-audit-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')); O.mkdir()
def load(n,p):
 s=importlib.util.spec_from_file_location(n,p); m=importlib.util.module_from_spec(s); s.loader.exec_module(m); return m
A=load('trace_source_gate',R/'research/rmaf/algorithm/universal233/rule5_common_split/audit_graph.py')
G=load('trace_np_gate',D.parent/'producer_compatibility/compatibility.py')
wanted={'sha','string_sha','pin','margin','cap','run','source','header_source','parse_header','extract','read_rows','fingerprint'}
parts=[n for n in ast.parse(V.read_text()).body if isinstance(n,ast.FunctionDef) and n.name in wanted]
assert {n.name for n in parts}==wanted
exec(compile(ast.Module(body=parts,type_ignores=[]),str(V),'exec'),globals())
rec=dict(status='TRACE_FRESH_CONTROLS',all_main_milestones='OPEN',independent_acceptance=False,runtime_claim=False,runs=[],inputs={},controls={},sources=[],reused_producers=[],new_producers=[])
def save(): (O/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n')
for p in [Path(__file__),V,Path(A.__file__),Path(G.__file__),M,D/'TARGET-v1.md',D/'CONTROLS-PIN-v1.md',D/'compile_development_v1.py']:
 rec['inputs'][str(p.relative_to(R))]=sha(p)
(O/'lean-toolchain').write_bytes((B/'lean-toolchain').read_bytes());save()
try:
 assert sha(M)=='e29854e71351309f3ef06fd7ba8636765ae08cf68708bb3242c8f55e8c1c68dc'
 pins0={e['path']:e['sha256'] for e in json.loads(M.read_text())['immutable_files']}
 assert sha(PA/'certificate.json')==pins0[str((PA/'certificate.json').relative_to(R))]
 old=json.loads((PA/'certificate.json').read_text())
 assert old['status']=='PASS_AUTHOR_ACTUAL_HARD2_TRACE_BOUND_SOURCE_PRODUCER'
 rec['controls']['exact_generator_inherited']=old['controls']['exact_generator_inherited']
 rec['exact_generator_control_origin']=old['exact_generator_control_origin']
 def nonproof(rows):
  for r in rows:
   if r['kind'] in {'definition','opaque'}:
    assert r['has_body'] and r['body'] and r.get('body_text_scope','FULL_NONPROOF_BODY')=='FULL_NONPROOF_BODY',('MISSING_NONPROOF_BODY',r['actual_name'])
 planted=dict(kind='opaque',actual_name='TraceOpaqueControl',has_body=True,body='Nat.zero',body_text_scope='FULL_NONPROOF_BODY')
 nonproof([planted])
 for k,v in [('has_body',False),('body',''),('body_text_scope','OMITTED_THEOREM_PROOF_TEXT')]:
  try:nonproof([dict(planted,**{k:v})])
  except AssertionError:rec['controls']['opaque_'+k]='CAUGHT'
  else:raise AssertionError('OPAQUE_CORRUPTION_ACCEPTED')
 own=['TargetBounds','GroupedTargets','PaidTargets','SizeControls']; receipts=[]
 for p in B.glob('live-compile-*/receipt.json'):
  c=json.loads(p.read_text())
  if c.get('status')=='PASS_AUTHOR_LIVE_GUARDED_COMPILE':receipts.append((p,c))
 for n in own:
  assert sha(D/(n+'.lean'))==sha(B/(n+'.lean'))
  assert any(any(r['module']==n and r['exit']==0 and r['expected_exit']==0 and r['source_sha256']==sha(B/(n+'.lean')) for r in c['runs']) for p,c in receipts),('NO_SOURCE_RECEIPT',n)
 false=[(p,c) for p,c in receipts if any(r['module']=='SizeFalseControls' and r['exit']==1 and r['expected_exit']==1 and r['source_sha256']==sha(D/'SizeFalseControls.lean') for r in c['runs'])]
 assert false
 fp,fc=sorted(false)[-1]; log=(fp.parent/'SizeFalseControls.log').read_text(); errs=re.findall(r': error(?:\([^)]*\))?: ([^\n]*)',log)
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
 records={e['module']:e for e in old['reused_producers']+old['new_producers']}; fresh=[];pins={}
 for n in order:
  p=B/(n+'.lean');o=B/(n+'.olean');pins[str(p.relative_to(R))]=sha(p);pins[str(o.relative_to(R))]=sha(o)
  if n in own:
   fresh.append(n);assert sha(p)==sha(D/p.name)
  else:
   assert n in records and sha(p)==sha(P/p.name) and sha(o)==sha(P/o.name)
   assert sha(p)==pins0[str((P/p.name).relative_to(R))] and sha(o)==pins0[str((P/o.name).relative_to(R))]
  rec['sources'].append(dict(module=n,source_sha256=sha(p),olean_sha256=sha(o),mode='FRESH_ACTUAL_PRODUCER_EXTRACTION' if n in own else 'EXACT_SEALED_BINARY_RECORD_REUSE'))
 (O/'BUILD-PINS.json').write_text(json.dumps(pins,indent=2)+'\n');save()
 (O/'FreshHeader.lean').write_text(header_source(order)); hlog=run(O,'FreshHeader',B);counts,expected=parse_header(hlog,order,B)
 def check(n,rr):
  A.parse_producer(dict(producer=n,count=counts[n]),rr);assert [(r['index'],r['actual_name'],r['kind']) for r in rr]==expected[n],('HEADER_MISMATCH',n);nonproof(rr)
 rows=[]
 for n in order:
  if n in fresh:continue
  e=records[n];p=R/e['path'];assert sha(p)==e['sha256'];rr=read_rows(p);check(n,rr);rows+=fingerprint(rr);rec['reused_producers'].append(e);del rr
 # Fresh exact source pin and inventory corruptions, before new extraction.
 first=order[0];pp=B/(first+'.lean');expected_pin=sha(pp);assert expected_pin==pins[str(pp.relative_to(R))]
 try:assert string_sha(pp.read_text()+'\n')==expected_pin
 except AssertionError:rec['controls']['source_pin_corruption']='CAUGHT'
 else:raise AssertionError('SOURCE_CORRUPTION_ACCEPTED')
 assert rows
 n=rec['reused_producers'][0]['module'];rr=read_rows(R/rec['reused_producers'][0]['path'])
 for key,badrows in [('missing_row',rr[:-1]),('duplicate_row',rr+[rr[0]])]:
  try:check(n,badrows)
  except AssertionError:rec['controls'][key]='CAUGHT'
  else:raise AssertionError('INVENTORY_CORRUPTION_ACCEPTED')
 save()
 idx,folder=extract(O,order,fresh,B,'ActualTrace');assert not idx['rejects']
 for entry in idx['producer_counts']:
  n=entry['producer'];p=folder/entry['file'];rr=read_rows(p);check(n,rr);rows+=fingerprint(rr)
  rec['new_producers'].append(dict(module=n,path=str(p.relative_to(R)),sha256=sha(p),stored_occurrences=len(rr)))
 assert len(rows)==sum(counts.values())
 merged=G.inspect(rows);(O/'COMPATIBILITY.json').write_text(json.dumps(merged,indent=2)+'\n');assert not merged['rejects'],merged['rejects']
 axioms=sorted({a for r in rows for a in r['axiom_references']});assert axioms==['Classical.choice','Quot.sound','propext']
 for p,h in pins.items():assert sha(R/p)==h,'BUILD_CHANGED'
 for p,h in rec['inputs'].items():assert sha(R/p)==h,'INPUT_CHANGED'
 rec.update(status='PASS_AUTHOR_ACTUAL_HARD2_QUERY_SIZE_SOURCE_PRODUCER',actual_imported_modules=len(order),new_own_builds=len(own),new_own_stored_occurrences=sum(e['stored_occurrences'] for e in rec['new_producers']),selected_stored_occurrences=len(rows),axiom_union=axioms,
  interfaces=['OrdinaryDispatch.Hard2Size.paidCase_target_bound','OrdinaryDispatch.Hard2Size.combined_target_bound','OrdinaryDispatch.Hard2Size.disjoint_target_bound','OrdinaryDispatch.Hard2Size.combined_query_potential','OrdinaryDispatch.Hard2Size.disjoint_query_potential'],
  admitted_rule5_trace='OPEN_SEPARATE_CONSUMER',full_source_bit_payload_recurrence='OPEN',source_bill_runtime_correspondence='OPEN',scope='Actual non-Rule5 forest query target label support and leaf count bound, all current paid/grouped/DP/disjoint/unit calls, and selected strict-budget potential n+2q. No supplied desired callback-list or correctness IH. Source-level producer evidence only; primitive scalar/payload/full-runtime correspondence remains OPEN.')
 save();print(rec['status'],len(order),len(rows),rec['new_own_stored_occurrences'],flush=True)
except BaseException as e:
 rec.update(status='FAILED_NOT_ACCEPTED',error=repr(e));save();raise
finally:
 (D/'LATEST-AUDIT-v1.json').write_text(json.dumps(dict(directory=str(O.relative_to(R)),certificate_sha256=sha(O/'certificate.json')),indent=2)+'\n')
