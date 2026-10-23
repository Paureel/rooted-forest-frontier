"""Author thin actual-root audit; exact frozen dependencies, new producers only.
Omitted theorem proof TEXT never excuses missing nonproof opaque bodies.
"""
from pathlib import Path
import ast,datetime,gzip,hashlib,importlib.util,json,os,re,resource,selectors,shlex,shutil,signal,subprocess,time
D=Path(__file__).resolve().parent;R=D.parents[5];B=R/'results/algorithm-universal233-ordinary-recursion-20261015T191007632025Z';U=D.parent/'resume_20261015T1810Z'
O=R/'results'/('algorithm-universal233-ordinary-scaffold-audit-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'));O.mkdir();V=U/'compressed_pool_resume_v3.py'
def load(n,p):
 spec=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
A=load('scaffold_split_audit',R/'research/rmaf/algorithm/universal233/rule5_common_split/audit_graph.py');G=load('scaffold_value_gate',D.parent/'producer_compatibility/compatibility.py')
wanted={'sha','string_sha','pin','margin','cap','run','source','header_source','parse_header','extract','read_rows','fingerprint'}
parts=[n for n in ast.parse(V.read_text()).body if isinstance(n,ast.FunctionDef) and n.name in wanted];assert {n.name for n in parts}==wanted
exec(compile(ast.fix_missing_locations(ast.Module(body=parts,type_ignores=[])),str(V),'exec'),globals())
rec=dict(status='RUNNING_AUTHOR_THIN_SCAFFOLD_AUDIT',all_main_milestones='OPEN',full_faster_solver=False,runtime_claim=False,independent_acceptance=False,runs=[],inputs={},controls={},dependencies=[],sources=[])
def save():(O/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n')
for p in [Path(__file__),V,Path(A.__file__),Path(G.__file__),D/'TARGET-v1.md',D/'CONTROLS-PIN-v1.md',D/'CONTROL-ERRATUM-v1.md',B/'certificate.json']:rec['inputs'][str(p.relative_to(R))]=sha(p)
save();(O/'lean-toolchain').write_bytes((B/'lean-toolchain').read_bytes())
try:
 # Exact generator controls are immutable and were executed before scientific application.
 q=R/'results/algorithm-universal233-ordinary-source-pool-compressed-20261015T182814513546Z/certificate.json';x=json.loads(q.read_text());assert x['status']=='PASS_AUTHOR_COMPRESSED_POOL_AUDIT' and x['inputs'][str(V.relative_to(R))]==sha(V)
 for n in ['actual_proof_body_reference_walk','opaque_bad_LR','opaque_bad_RL','clean_opaque','false_proof','production_pin_corruption']:assert n in x['controls']
 rec['exact_generator_control_origin']=dict(path=str(q.relative_to(R)),sha256=sha(q));rec['controls']['exact_generator']=x['controls'];save()
 own=['OrdinaryScaffold','ScaffoldFacts','ScaffoldExact','ScaffoldControlPilot','ScaffoldControls'];receipts=[]
 for p in B.glob('live-compile-*/receipt.json'):
  z=json.loads(p.read_text())
  if z.get('status')=='PASS_AUTHOR_LIVE_GUARDED_COMPILE':receipts.append((p,z))
 for n in own:
  assert sha(D/(n+'.lean'))==sha(B/(n+'.lean'))
  candidates=[(p,z) for p,z in receipts if any(t['module']==n and t['exit']==0 and t['expected_exit']==0 and t['source_sha256']==sha(D/(n+'.lean')) for t in z['runs'])]
  if n=='OrdinaryScaffold':
   c=json.loads((B/'compile-v2.json').read_text());assert c['exit']==0 and c['source_sha256']==sha(D/(n+'.lean'))
  else:assert candidates,('NO_ACTUAL_POSITIVE_SOURCE_RECEIPT',n)
 false=[(p,z) for p,z in receipts if any(t['module']=='ScaffoldFalseControls' and t['exit']==1 and t['expected_exit']==1 and t['source_sha256']==sha(D/'ScaffoldFalseControls.lean') for t in z['runs'])]
 assert false;fp,frec=sorted(false)[-1];log=(fp.parent/'ScaffoldFalseControls.log').read_text();errors=re.findall(r': error(?:\([^)]*\))?: ([^\n]*)',log)
 assert len(errors)==3 and all(e=='unsolved goals' or e.startswith('Tactic `decide` proved that the proposition') for e in errors) and 'sorry' not in log,('FALSE_CONTROLS_DIAGNOSTIC_GATE',errors)
 rec['controls']['actual_program_false_claims']=dict(path=str(fp.relative_to(R)),sha256=sha(fp),errors=errors);save()
 # Freeze exact actual import closure, not every file staged in the directory.
 order=[];seen=set()
 def visit(n):
  if n in seen:return
  p=B/(n+'.lean');assert p.exists()
  for dep in re.findall(r'^import ([A-Za-z0-9_\'.]+)\s*$',p.read_text(),re.M):
   if dep.split('.')[0] not in {'Std','Lean','Init'}:visit(dep)
  seen.add(n);order.append(n)
 for n in own:visit(n)
 stage=json.loads((B/'certificate.json').read_text());entries={e['module']:e for e in stage['source_entries']};pins={}
 for n in order:
  p=B/(n+'.lean');o=B/(n+'.olean');pins[str(p.relative_to(R))]=sha(p);pins[str(o.relative_to(R))]=sha(o)
  if n not in own:
   e=entries[n];assert sha(p)==e['sha256'] and sha(o)==e['olean_sha256'];assert p.stat().st_mode&0o222==0 and o.stat().st_mode&0o222==0
  rec['sources'].append(dict(module=n,source_sha256=sha(p),olean_sha256=sha(o),mode='NEW_SOURCE_BUILD' if n in own else 'PINNED_IMMUTABLE_DEPENDENCY'))
 (O/'BUILD-PINS.json').write_text(json.dumps(pins,indent=2)+'\n');save()
 # Header checks every actual stored row and every resolved binary path.
 (O/'FreshHeader.lean').write_text(header_source(order));out=run(O,'FreshHeader',B);counts,expected=parse_header(out,order,B)
 old_roots={
 'results/algorithm-universal233-ordinary-common-reduction-20261015T185752074314Z':R/'results/algorithm-universal233-ordinary-common-reduction-compressed-20261015T190441071133Z/records-LocalIHAll',
 'results/algorithm-universal233-ordinary-child-binding-20261015T182851721674Z':R/'results/algorithm-universal233-ordinary-child-consumer-compressed-20261015T185512557908Z/records-LocalIHAll'}
 indices={str(k):{c['producer']:c for c in json.loads((v/'index.json').read_text())['producer_counts']} for k,v in old_roots.items()};rows=[]
 def check(n,c,rr):
  A.parse_producer(c,rr)
  assert [(z['index'],z['actual_name'],z['kind']) for z in rr]==expected[n],('ACTUAL_HEADER_MISMATCH',n)
  for z in rr:
   if z['kind'] in {'definition','opaque'}:assert z['has_body'] and z.get('body_text_scope')=='FULL_NONPROOF_BODY' and z['body'],('UNRESOLVED_NONPROOF_VALUE',n,z['actual_name'])
 for n in order:
  if n in own:continue
  e=entries[n];root=str(Path(e['path']).parent);origin=old_roots[root];c=indices[root][n];p=origin/c['file'];rr=read_rows(p);check(n,c,rr);rows+=fingerprint(rr)
  rec['dependencies'].append(dict(module=n,records=str(p.relative_to(R)),records_sha256=sha(p),canonical_olean_sha256=e['olean_sha256']));del rr
 # Fresh merger controls: row loss, duplicate and false source pin must be rejected.
 c=indices[str(Path(entries[order[0]]['path']).parent)][order[0]];sample=read_rows(R/rec['dependencies'][0]['records'])
 for label,rr in [('missing',sample[:-1]),('duplicate',sample+[sample[0]])]:
  try:A.parse_producer(c,rr)
  except AssertionError:rec['controls']['thin_merge_'+label]='CAUGHT'
  else:raise AssertionError('THIN_MERGE_CORRUPTION_ACCEPTED')
 try:assert pins[str((B/(order[0]+'.lean')).relative_to(R))]=='corrupted'
 except AssertionError:rec['controls']['thin_source_pin']='CAUGHT'
 else:raise AssertionError('FALSE_SOURCE_PIN_ACCEPTED')
 save();idx,root=extract(O,order,own,B,'NewScaffold');assert not idx['rejects']
 newrows=[]
 for c in idx['producer_counts']:
  rr=read_rows(root/c['file']);check(c['producer'],c,rr);newrows+=fingerprint(rr);del rr
 rows+=newrows;compat=G.inspect(rows);(O/'COMPATIBILITY.json').write_text(json.dumps(compat,indent=2)+'\n');assert not compat['rejects']
 keys=['OrdinaryScaffold.solve','OrdinaryScaffold.solve_exact','OrdinaryScaffold.actual_ordinary_IH','OrdinaryScaffold.actual_local_ordinary_IH']
 for n in keys:assert any(r['actual_name']==n for r in newrows)
 ax=sorted({a for r in rows for a in r['axiom_references']});assert set(ax)<=A.ALLOWED
 for p,h in pins.items():assert sha(R/p)==h,'ACTUAL_BUILD_CHANGED'
 for p,h in rec['inputs'].items():assert sha(R/p)==h,'INPUT_CHANGED'
 rec.update(status='PASS_AUTHOR_COMPLETE_CHERRY_SCAFFOLD_SOURCE_PRODUCER',new_builds=len(own),imported_modules=len(order),dependency_modules=len(order)-len(own),new_stored_occurrences=len(newrows),total_selected_stored_occurrences=len(rows),axiom_union=ax,interfaces=keys,proof_text_scope='Theorem proof text omitted; full actual proof references traversed. Every definition and opaque value explicitly has full nonempty body.',base_claim='NO: original hard2 fallback mass at2.33=56600/54289>1.',all_main_milestones='OPEN');save();print(rec['status'],len(order),len(newrows),len(rows),flush=True)
except BaseException as e:rec.update(status='FAILED_NOT_ACCEPTED',error=repr(e));save();raise
finally:(D/'LATEST-AUDIT-v1.json').write_text(json.dumps(dict(directory=str(O.relative_to(R)),certificate_sha256=sha(O/'certificate.json')),indent=2)+'\n')
