# One-shot exact-context audit adapter. Reuses the tested compressed producer
# extractor; no new general instrument and no repeated old proof extraction.
from pathlib import Path
import ast,copy,datetime,gzip,hashlib,importlib.util,json,os,re,resource,selectors,shlex,shutil,signal,subprocess,time
D=Path(__file__).resolve().parent;R=D.parents[5];B=D/'build';O=B/'author-audit-v4';assert not O.exists();O.mkdir()
def load(n,p):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
A=load('rule4_frozen_parser',R/'research/rmaf/algorithm/universal233/rule5_common_split/audit_graph.py')
V=D.parent/'resume_20261015T1810Z/compressed_pool_resume_v3.py'
assert hashlib.sha256(V.read_bytes()).hexdigest()=='626e3f21ba70fb417ad1085995a88b4af217a1b6f210191fa58ca442aad0098a'
for n in ast.parse(V.read_text()).body:
 if isinstance(n,ast.FunctionDef) and n.name in {'sha','string_sha','margin','cap','run','source','header_source','extract','read_rows'}:
  s=ast.unparse(n)
  if n.name=='run':
   s=s.replace("[str(R / 'bootloops-lean')]","[str(R / 'bootloops-lean'), '--memory=3072']").replace('> 60','> 30').replace('COMMAND_60S_CAP','COMMAND_30S_CAP').replace('8 * (1 << 20)','120000').replace('METADATA_STDOUT_8MIB_CAP','STDOUT_120KB_CAP')
  if n.name=='cap':s=s.replace('512 * (1 << 20)','64 * (1 << 20)')
  exec(s,globals())
compressed_source=source
def source(imports,wanted,out):
 s=compressed_source(imports,wanted,out)
 if wanted==['Rule4SourceControls']:return s
 a='let body := match ci with | .thmInfo _ => none | _ => ci.value? true';assert s.count(a)==1;s=s.replace(a,'let body := ci.value? true')
 a='match ci with | .thmInfo _ => "OMITTED_THEOREM_PROOF_TEXT" | _ => "FULL_NONPROOF_BODY"';assert s.count(a)==1;return s.replace(a,'"FULL_ALL_BODY"')
rec={'version':1,'status':'CHECKING','retained_failed_audits':['author-audit-v1','author-audit-v2','author-audit-v3'],'proof_size_refactor':'Payload proof arithmetic uses direct Nat monotonicity rather than expanded omega composition; theorem types and source meters unchanged.','independent_acceptance':False,'scalar_source_bound_only':True,'control_proof_text_amendment':'After retained audit-v2 resource stop, control theorem proof plaintext is omitted; full actual references/axiom closure and full nonproof bodies retained. All three new logical proof modules retain full proof text.','native_or_whole_algorithm':'OPEN','runs':[],'inputs':{},'reused_producers':[],'new_producers':[],'controls':{}}
def save():(O/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n')
save()
try:
 for p in [Path(__file__),D/'AUDIT-CONTROLS-PIN-v1.json',V,Path(A.__file__),D/'DEPENDENCY-PROVENANCE-v1.json']:
  rec['inputs'][str(p.relative_to(R))]=sha(p)
 dep=json.loads((D/'DEPENDENCY-PROVENANCE-v1.json').read_text());fresh=['Rule4PayloadBound','Rule4SourceBound','Rule4BoundInterface','Rule4SourceControls'];known={e['module'] for e in dep['modules']}|set(fresh)
 M=R/'research/rmaf/algorithm/universal233/ordinary_dispatch/ordinary_full_source_integration_20261016T092805Z/FINAL-MANIFEST-v1.json';assert sha(M)==dep['manifest_sha256'];m=json.loads(M.read_text());P=R/m['canonical_certificate'];assert sha(P)==m['certificate_sha256'];old=json.loads(P.read_text());assert old['status']=='PASS_AUTHOR_ORDINARY_CHILDREN_FOREST_DEBIT_WEIGHTED_SOURCE_INTEGRATION'
 rec['canonical_input']={'manifest':str(M.relative_to(R)),'sha256':sha(M),'certificate':str(P.relative_to(R)),'certificate_sha256':sha(P),'compatibility':'All selected imported source/object pairs are unchanged from this single canonical context','body_qualification':m['body_qualification']}
 oldSources={x['module']:x for x in old['sources']};oldRecords={x['module']:x for x in old['reused_producers']+old['new_producers']}
 for e in dep['modules']:
  n=e['module'];assert sha(B/(n+'.lean'))==oldSources[n]['source_sha256']==e['source']['sha256'];assert sha(B/(n+'.olean'))==oldSources[n]['olean_sha256']==e['object']['sha256'];z=oldRecords[n];assert sha(R/z['path'])==z['sha256'];rec['reused_producers'].append(z)
 rec['controls']['inherited_exact_canonical_engine_controls']={'certificate':str(P.relative_to(R)),'sha256':sha(P),'same_lineage':True,'independent':False,'controls':old['controls']}
 for n in fresh:
  assert sha(B/(n+'.lean'))==sha(D/(n+'.lean'))
  assert any(any(x['module']==n and x['exit']==0 and x['source_sha256']==sha(D/(n+'.lean')) for x in json.loads(p.read_text())['runs']) and json.loads(p.read_text()).get('status')=='PASS_AUTHOR_GUARDED_SOURCE_COMPILE' for p in B.glob('compile-*/receipt.json')),('NO_MATCHING_COMPILE_RECEIPT',n)
 (O/'lean-toolchain').write_bytes((B/'lean-toolchain').read_bytes())
 # Header prints only own declaration names, while resolving every loaded path.
 starts=['Rule4BoundInterface','Rule4SourceControls'];h=header_source(starts);a='let wanted : List Name := ['+', '.join('`'+n for n in starts)+']';b='let wanted : List Name := ['+', '.join('`'+n for n in fresh)+']';assert h.count(a)==1;h=h.replace(a,b)
 line='  logInfo m!"PATH|{producer}|{path}"'
 localnames=', '.join('`'+n for n in sorted(known))
 replace='  let exactLocal : List Name := ['+localnames+']\n  if exactLocal.contains producer then\n   unless path.toString == '+json.dumps(str(B))+' ++ "/" ++ producer.toString ++ ".olean" do throwError "FOREIGN_LOCAL_PATH"\n  else\n   unless path.toString.startsWith '+json.dumps(str(R/'.runtime/elan/toolchains'))+' do throwError "FOREIGN_RUNTIME_PATH"\n  logInfo m!"USED|{producer}"\n  if wanted.contains producer then logInfo m!"PATH|{producer}|{path}"'
 assert h.count(line)==1;h=h.replace(line,replace);(O/'Header.lean').write_text(h)
 out=run(O,'Header',B);paths=dict(re.findall(r'^PATH\|([^|]+)\|(.+)$',out,re.M));assert known<=set(re.findall(r'^USED\|([^\n]+)$',out,re.M))
 for n,p in paths.items():
  q=Path(p).resolve();assert q==(B/(n+'.olean')).resolve() if n in known else q.is_relative_to(R/'.runtime/elan/toolchains'),('FOREIGN_MODULE_PATH',n,p)
 counts={n:int(c) for n,c in re.findall(r'^COUNT\|([^|]+)\|(\d+)$',out,re.M)};assert set(counts)==set(fresh)
 expected={n:[] for n in fresh}
 for n,i,x,k in re.findall(r'^NAME\|([^|]+)\|(\d+)\|([^|]+)\|([^\n]+)$',out,re.M):expected[n].append((int(i),x,k))
 rec['actual_imported_modules']=len(known);save()
 for i,n in enumerate(['Rule4SourceControls','Rule4PayloadBound','Rule4SourceBound','Rule4BoundInterface']):
  idx,folder=extract(O,starts,[n],B,'Own'+str(i));assert not idx['rejects'];rows=read_rows(folder/(n+'.json.gz'));A.parse_producer({'producer':n,'count':counts[n]},rows)
  assert [(z['index'],z['actual_name'],z['kind']) for z in rows]==expected[n]
  assert all(z['resolved_origin']==n for z in rows)
  assert all(z['body_text_scope']==('OMITTED_THEOREM_PROOF_TEXT' if n=='Rule4SourceControls' and z['kind']=='theorem' else 'FULL_NONPROOF_BODY' if n=='Rule4SourceControls' else 'FULL_ALL_BODY') for z in rows)
  assert all(z['has_body'] and z['body']!='<none>' for z in rows if z['kind'] in ({'definition','opaque'} if n=='Rule4SourceControls' else {'definition','theorem','opaque'}))
  assert len(json.dumps(rows).encode())<64*(1<<20),'RAW_MODULE_CAP'
  if i==0:
   for label,mutate,want in [('missing',lambda z:z.pop(),'MISSING_OCCURRENCE'),('custom_axiom',lambda z:z[0]['axiom_references'].append('sorryAx'),'CUSTOM_PRODUCER_AXIOM'),('name_drift',lambda z:z[0].update(actual_name='False.control'),'ACTUAL_NAME')]:
    bad=copy.deepcopy(rows);mutate(bad)
    try:A.parse_producer({'producer':n,'count':counts[n]},bad)
    except AssertionError as e:assert str(e)==want;rec['controls'][label]={'rejected':True,'reason':str(e)}
    else:raise AssertionError('CORRUPTION_CONTROL_SURVIVED:'+label)
  p=folder/(n+'.json.gz');rec['new_producers'].append({'module':n,'path':str(p.relative_to(R)),'sha256':sha(p),'source_sha256':sha(B/(n+'.lean')),'olean_sha256':sha(B/(n+'.olean')),'stored_occurrences':len(rows),'compressed_bytes':p.stat().st_size,'raw_bytes':len(json.dumps(rows).encode()),'all_proof_bodies':n!='Rule4SourceControls','axiom_union':sorted({a for z in rows for a in z['axiom_references']})});save()
 roots='\n'.join('import '+n for n in starts)+'\n#print axioms OrdinaryDispatch.FullSourceWork.rule4Source_bound\n#print axioms OrdinaryDispatch.FullSourceWork.rule4Source_cutoff_bound\n#print axioms OrdinaryDispatch.FullSourceWork.rule4SourcePolynomial_explicit\n';(O/'RootAxioms.lean').write_text(roots);run(O,'RootAxioms',B)
 rec['axiom_union']=sorted(set(old['axiom_union'])|{a for x in rec['new_producers'] for a in x['axiom_union']});assert set(rec['axiom_union'])<={'Classical.choice','Quot.sound','propext'}
 rec['status']='PASS_AUTHOR_ACTUAL_RULE4_SOURCE_POLYNOMIAL_BOUND';save();print(rec['status'],'new_modules',len(fresh),'imports',len(known),'axioms',rec['axiom_union'])
except BaseException as e:rec.update(status='FAILED_NOT_ACCEPTED',error=repr(e));save();raise
