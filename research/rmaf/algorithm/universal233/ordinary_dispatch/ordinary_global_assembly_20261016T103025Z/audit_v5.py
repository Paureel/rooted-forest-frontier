# Exact-context audit adapter; no rebuilt frozen dependencies or path-union pool.
from pathlib import Path
import ast,copy,datetime,gzip,hashlib,importlib.util,json,os,re,resource,selectors,shlex,shutil,signal,subprocess,time,sys
sys.dont_write_bytecode=True
D=Path(__file__).resolve().parent;R=D.parents[5];B=D/'build';O=B/'author-audit-v5';assert not O.exists();O.mkdir()
def load(n,p):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
A=load('global_frozen_parser',R/'research/rmaf/algorithm/universal233/rule5_common_split/audit_graph.py')
V=D.parent/'resume_20261015T1810Z/compressed_pool_resume_v3.py'
assert hashlib.sha256(V.read_bytes()).hexdigest()=='626e3f21ba70fb417ad1085995a88b4af217a1b6f210191fa58ca442aad0098a'
for n in ast.parse(V.read_text()).body:
 if isinstance(n,ast.FunctionDef) and n.name in {'sha','string_sha','margin','cap','run','source','header_source','extract','read_rows'}:
  s=ast.unparse(n)
  if n.name=='run':s=s.replace("[str(R / 'bootloops-lean')]","[str(R / 'bootloops-lean'), '--memory=3072']").replace('> 60','> 30').replace('COMMAND_60S_CAP','COMMAND_30S_CAP').replace('8 * (1 << 20)','120000').replace('METADATA_STDOUT_8MIB_CAP','STDOUT_120KB_CAP')
  if n.name=='cap':s=s.replace('512 * (1 << 20)','64 * (1 << 20)')
  exec(s,globals())
logical=['ClosedLocalSource','ClosedSourceTree','OptimizerSourceBodies','OptimizerSourceUniform'];controls=['GlobalAssemblyControls','OptimizerAssemblyControls'];fresh=logical+controls
compressed_source=source
def source(imports,wanted,out):
 s=compressed_source(imports,wanted,out)
 marker='        rows := rows.push (Json.mkObj'
 check='        if resolved != producer.toString then\n          match env.find? ci.name with\n          | none => throwError "COLLISION_NAME_NOT_LOADED"\n          | some loaded =>\n            unless reprStr ci.type == reprStr loaded.type do throwError "COLLISION_TYPE_DIFFERENCE"\n            unless ci.isTheorem && loaded.isTheorem do throwError "NONPROOF_COLLISION_REQUIRES_SEPARATE_METADATA_CHECK"\n'
 assert s.count(marker)==1;s=s.replace(marker,check+marker)
 if not all(n in logical for n in wanted):return s
 a='let body := match ci with | .thmInfo _ => none | _ => ci.value? true';assert s.count(a)==1;s=s.replace(a,'let body := ci.value? true')
 a='match ci with | .thmInfo _ => "OMITTED_THEOREM_PROOF_TEXT" | _ => "FULL_NONPROOF_BODY"';assert s.count(a)==1;return s.replace(a,'"FULL_ALL_BODY"')
rec={'version':1,'status':'CHECKING','independent_acceptance':False,'full_ordinary_runtime':'OPEN','native_bit_semantics':'OPEN','runs':[],'inputs':{},'reused_producers':[],'new_producers':[],'controls':{},'sources':[],'body_qualification':json.loads((D/'AUDIT-CONTROLS-PIN-v1.json').read_text())}
def save():(O/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n')
save()
try:
 for p in [Path(__file__),D/'AUDIT-CONTROLS-PIN-v1.json',V,Path(A.__file__),D/'DEPENDENCY-PROVENANCE-v4.json']:
  rec['inputs'][str(p.relative_to(R))]=sha(p)
 dep=json.loads((D/'DEPENDENCY-PROVENANCE-v4.json').read_text());known={e['module'] for e in dep['modules']}|set(fresh);additions=dep['optimizer_context']['new_modules']
 compat=R/dep['optimizer_context']['compatibility_certificate'];assert sha(compat)==dep['optimizer_context']['compatibility_certificate_sha256'];cc=json.loads(compat.read_text());assert cc['status'].startswith('PASS_');rec['compatibility_bridge']={'path':str(compat.relative_to(R)),'sha256':sha(compat),'status':cc['status']}
 pins=json.loads((D/'PINNED-PACKAGES-v1.json').read_text());oldrecords={};oldsources={}
 for k in ['hard2_front','rule4_bound']:
  e=pins[k];M=R/e['manifest'];assert sha(M)==e['sha256'];m=json.loads(M.read_text());P=R/m['canonical_certificate'];assert sha(P)==m['certificate_sha256'];old=json.loads(P.read_text());assert old['status'].startswith('PASS_')
  rec['inputs'][str(M.relative_to(R))]=sha(M);rec['inputs'][str(P.relative_to(R))]=sha(P)
  for x in old.get('sources',[]):oldsources.setdefault(x['module'],x)
  for x in old['reused_producers']+old['new_producers']:
   oldrecords.setdefault(x['module'],x)
   if 'source_sha256' in x:oldsources.setdefault(x['module'],x)
  rec.setdefault('inherited_qualifications',{})[k]=m['body_qualification']
  rec['controls']['inherited_'+k]={'path':str(P.relative_to(R)),'sha256':sha(P),'independent':False,'controls':old['controls']}
 for e in dep['modules']:
  n=e['module'];assert sha(B/(n+'.lean'))==e['source']['sha256'];assert sha(B/(n+'.olean'))==e['object']['sha256']
  rec['sources'].append({'module':n,'source_sha256':sha(B/(n+'.lean')),'olean_sha256':sha(B/(n+'.olean'))})
  if n in additions:continue
  x=oldsources[n];assert sha(B/(n+'.lean'))==x['source_sha256'];assert sha(B/(n+'.olean'))==x['olean_sha256'];z=oldrecords[n];assert sha(R/z['path'])==z['sha256'];rec['reused_producers'].append(z)
 for n in fresh:
  assert sha(B/(n+'.lean'))==sha(D/(n+'.lean'))
  assert any(any(x['module']==n and x['exit']==0 and x['source_sha256']==sha(D/(n+'.lean')) for x in json.loads(p.read_text())['runs']) and json.loads(p.read_text()).get('status')=='PASS_AUTHOR_GUARDED_SOURCE_COMPILE' for p in B.glob('compile-*/receipt.json')),('NO_MATCHING_COMPILE_RECEIPT',n)
  rec['sources'].append({'module':n,'source_sha256':sha(B/(n+'.lean')),'olean_sha256':sha(B/(n+'.olean'))})
 (O/'lean-toolchain').write_bytes((B/'lean-toolchain').read_bytes());starts=['OptimizerSourceUniform']+controls;wanted=fresh+additions;h=header_source(starts)
 a='let wanted : List Name := ['+', '.join('`'+n for n in starts)+']';b='let wanted : List Name := ['+', '.join('`'+n for n in fresh)+']';assert h.count(a)==1;h=h.replace(a,b)
 line='  logInfo m!"PATH|{producer}|{path}"';localnames=', '.join('`'+n for n in sorted(known))
 replace='  let exactLocal : List Name := ['+localnames+']\n  if exactLocal.contains producer then\n   unless path.toString == '+json.dumps(str(B))+' ++ "/" ++ producer.toString ++ ".olean" do throwError "FOREIGN_LOCAL_PATH"\n  else\n   unless path.toString.startsWith '+json.dumps(str(R/'.runtime/elan/toolchains'))+' do throwError "FOREIGN_RUNTIME_PATH"\n  if exactLocal.contains producer then logInfo m!"USED|{producer}"\n  if wanted.contains producer then logInfo m!"PATH|{producer}|{path}"'
 assert h.count(line)==1;h=h.replace(line,replace);(O/'Header.lean').write_text(h);out=run(O,'Header',B)
 used=set(re.findall(r'^USED\|([^\n]+)$',out,re.M));assert known<=used,('UNLOADED_LOCAL_MODULES',sorted(known-used))
 counts={n:int(c) for n,c in re.findall(r'^COUNT\|([^|]+)\|(\d+)$',out,re.M)};assert set(counts)==set(fresh)
 expected={n:[] for n in wanted}
 for n,i,x,k in re.findall(r'^NAME\|([^|]+)\|(\d+)\|([^|]+)\|([^\n]+)$',out,re.M):expected[n].append((int(i),x,k))
 for j,n in enumerate(additions):
  hs=h.replace(b,'let wanted : List Name := [`'+n+']');hn='HeaderImport'+str(j);(O/(hn+'.lean')).write_text(hs);ho=run(O,hn,B)
  cs={nm:int(c) for nm,c in re.findall(r'^COUNT\|([^|]+)\|(\d+)$',ho,re.M)};assert set(cs)=={n};counts.update(cs)
  for nm,i,x,k in re.findall(r'^NAME\|([^|]+)\|(\d+)\|([^|]+)\|([^\n]+)$',ho,re.M):expected[nm].append((int(i),x,k))
 assert set(counts)==set(wanted)
 rec['actual_imported_modules']=len(known);save()
 for i,n in enumerate(controls+logical+additions):
  idx,folder=extract(O,starts,[n],B,'Own'+str(i));assert not idx['rejects'];rows=read_rows(folder/(n+'.json.gz'));A.parse_producer({'producer':n,'count':counts[n]},rows)
  assert [(z['index'],z['actual_name'],z['kind']) for z in rows]==expected[n];assert all(z['resolved_origin'] in known for z in rows)
  collisions=[{k:z[k] for k in ['producer','index','actual_name','kind','resolved_origin']} for z in rows if z['resolved_origin']!=n]
  if collisions:rec.setdefault('retained_cross_origin_occurrences',[]).extend(collisions)
  assert all(z['body_text_scope']==('FULL_ALL_BODY' if n in logical else 'OMITTED_THEOREM_PROOF_TEXT' if z['kind']=='theorem' else 'FULL_NONPROOF_BODY') for z in rows)
  assert all(z['has_body'] and z['body']!='<none>' for z in rows if z['kind'] in ({'definition','theorem','opaque'} if n in logical else {'definition','opaque'}));raw=len(json.dumps(rows).encode());assert raw<64*(1<<20),'RAW_MODULE_CAP'
  if i==0:
   for label,mutate,want in [('missing',lambda z:z.pop(),'MISSING_OCCURRENCE'),('custom_axiom',lambda z:z[0]['axiom_references'].append('sorryAx'),'CUSTOM_PRODUCER_AXIOM'),('name_drift',lambda z:z[0].update(actual_name='False.control'),'ACTUAL_NAME')]:
    bad=copy.deepcopy(rows);mutate(bad)
    try:A.parse_producer({'producer':n,'count':counts[n]},bad)
    except AssertionError as e:assert str(e)==want;rec['controls'][label]={'rejected':True,'reason':str(e)}
    else:raise AssertionError('CORRUPTION_CONTROL_SURVIVED:'+label)
  p=folder/(n+'.json.gz');rec['new_producers'].append({'module':n,'path':str(p.relative_to(R)),'sha256':sha(p),'source_sha256':sha(B/(n+'.lean')),'olean_sha256':sha(B/(n+'.olean')),'stored_occurrences':len(rows),'compressed_bytes':p.stat().st_size,'raw_bytes':raw,'all_proof_bodies':n in logical,'role':'owned_logical' if n in logical else 'owned_control' if n in controls else 'sealed_import_addition','axiom_union':sorted({a for z in rows for a in z['axiom_references']})});save();print('AUDITED',n,len(rows),raw,flush=True)
 roots='\n'.join('import '+n for n in starts)+'\n'+'\n'.join('#print axioms OrdinaryDispatch.GlobalSourceAssembly.'+n for n in ['closedLocalDebit_bound','closedSourceSubtotal_bound','closedSourceQuery_bound','common_exact_callback_split','rule4_forward_exact_callback_split','rule4_reverse_exact_callback_split','sourceOptimizeMeter_value','sourceOptimize_actual_fees','sourceOptimize_uniform_233','partialSourceOptimize_bound'])+'\n';(O/'RootAxioms.lean').write_text(roots);ax=run(O,'RootAxioms',B)
 assert 'sorryAx' not in ax;rec['axiom_union']=sorted({a for x in rec['new_producers'] for a in x['axiom_union']}|{'Classical.choice','Quot.sound','propext'});assert set(rec['axiom_union'])<={'Classical.choice','Quot.sound','propext'}
 rec['status']='PASS_AUTHOR_PARTIAL_ORDINARY_SOURCE_AND_ACTUAL_OPTIMIZER_COMPOSITION';save();print(rec['status'],len(known))
except BaseException as e:rec.update(status='FAILED_NOT_ACCEPTED',error=repr(e));save();raise
