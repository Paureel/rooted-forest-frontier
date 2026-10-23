# One-shot local full-body audit adapter. Existing extractor and parser unchanged.
from pathlib import Path
import ast,datetime,gzip,hashlib,importlib.util,json,os,re,resource,selectors,shlex,shutil,signal,subprocess,time
D=Path(__file__).resolve().parent;R=D.parents[5]
P=json.loads((D/'DEPENDENCY-PINS-v1.json').read_text());B=R/P['pool'];S=R/P['prior_own_pool'];PREV=R/P['previous_pool'];SN=R/P['semantic_numeric_pool'];SM=R/P['semantic_pool'];O=D/'author-audit-v1';O.mkdir()
V=R/'research/rmaf/algorithm/universal233/ordinary_dispatch/resume_20261015T1810Z/compressed_pool_resume_v3.py'
assert hashlib.sha256(V.read_bytes()).hexdigest()=='626e3f21ba70fb417ad1085995a88b4af217a1b6f210191fa58ca442aad0098a'
def load(n,p):
 spec=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
A=load('numeric_audit_parser',R/'research/rmaf/algorithm/universal233/rule5_common_split/audit_graph.py')
for n in ast.parse(V.read_text()).body:
 if isinstance(n,ast.FunctionDef) and n.name in {'sha','string_sha','source','header_source'}:
  exec(compile(ast.Module(body=[n],type_ignores=[]),str(V),'exec'),globals())
qualified_source=source
def source(imports,modules,out):
 s=qualified_source(imports,modules,out)
 if not set(modules)<={'StoredClassifierInterface','NumericAuditClean','NumericAuditHostile'}:return s
 a='let body := match ci with | .thmInfo _ => none | _ => ci.value? true';assert s.count(a)==1
 s=s.replace(a,'let body := ci.value? true')
 a='match ci with | .thmInfo _ => "OMITTED_THEOREM_PROOF_TEXT" | _ => "FULL_NONPROOF_BODY"';assert s.count(a)==1
 return s.replace(a,'"FULL_ALL_BODY"')
rec=dict(status='CHECKING',same_author=True,independent_credit=0,full233=False,native=False,novelty=False,runs=[],controls={},inputs={},sources=[],new_producers=[],inherited_audit_qualification='Frozen imported records remain at their existing qualifications; exact chosen source/object closure matched. No blanket re-extraction of imported full bodies.')
def save():(O/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n')
def run(root,name,pathroot,build=False,want=0):
 assert shutil.disk_usage(D).free>=3*(1<<30)
 start=time.monotonic();cmd=[str(R/'bootloops-lean'),'--memory=3072']+(['-o',str(root/(name+'.olean'))] if build else [])+[str(root/(name+'.lean'))]
 def limit():resource.setrlimit(resource.RLIMIT_FSIZE,(16*(1<<20),16*(1<<20)))
 p=subprocess.Popen(cmd,cwd=root,env=dict(os.environ,LEAN_PATH=str(pathroot)),stdout=subprocess.PIPE,stderr=subprocess.STDOUT,preexec_fn=limit,start_new_session=True)
 size=0;chunks=[];failure=None;sel=selectors.DefaultSelector();sel.register(p.stdout,selectors.EVENT_READ)
 while sel.get_map():
  if time.monotonic()-start>30:failure='30S_PILOT_CAP'
  if size>4*(1<<20):failure='4MIB_STDOUT_CAP'
  if shutil.disk_usage(D).free<3*(1<<30):failure='3GIB_DISK_FLOOR'
  if failure:os.killpg(p.pid,signal.SIGTERM);break
  for key,event in sel.select(0.2):
   buf=os.read(key.fd,1<<16)
   if buf:chunks.append(buf);size+=len(buf)
   else:sel.unregister(key.fileobj)
 try:tail=p.communicate(timeout=3)[0]
 except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL);tail=p.communicate()[0]
 sel.close();chunks.append(tail);out=b''.join(chunks);(root/(name+'.log')).write_bytes(out)
 rec['runs'].append(dict(module=name,exit=p.returncode,expected=want,seconds=time.monotonic()-start,stdout_bytes=len(out),resource_stop=failure));save()
 assert failure is None and p.returncode==want,(name,failure,p.returncode,out[-1500:])
 assert b'declaration uses `sorry`' not in out
 return out.decode()
def extract(label,imports,mods,pathroot,want=0):
 folder=O/('records-'+label);folder.mkdir();name='Body'+label
 (O/(name+'.lean')).write_text(source(imports,mods,folder));run(O,name,pathroot,want=want)
 idx=json.loads((folder/'index.json').read_text());assert len(idx['producer_counts'])==len(mods)
 assert {r['producer'] for r in idx['producer_counts']}==set(mods)
 result=[]
 for c in idx['producer_counts']:
  f=folder/c['file'];assert f.stat().st_size<=16*(1<<20),'16MIB_COMPRESSED_CAP'
  with gzip.open(f,'rb') as stream:raw=stream.read(256*(1<<20)+1)
  assert len(raw)<=256*(1<<20),'256MIB_RAW_CAP'
  assert max(map(len,raw.splitlines()),default=0)<=128*(1<<20),'128MIB_LINE_CAP'
  rows=json.loads(raw);bad=A.parse_producer(c,rows,expect_reject=bool(want));assert bool(bad)==bool(want)
  expected_full=c['producer'] in {'StoredClassifierInterface','NumericAuditClean','NumericAuditHostile'}
  assert all(r['body_text_scope']==('FULL_ALL_BODY' if expected_full or r['kind']!='theorem' else 'OMITTED_THEOREM_PROOF_TEXT') or (not expected_full and r['kind']!='theorem' and r['body_text_scope']=='FULL_NONPROOF_BODY') for r in rows)
  assert all(r['has_body'] and r['body']!='<none>' for r in rows if r['kind'] in {'definition','opaque'} or (expected_full and r['kind']=='theorem'))
  result.append((c,f,rows,len(raw)))
 return idx,result
save();(O/'lean-toolchain').write_bytes((D/'lean-toolchain').read_bytes())
try:
 for p in [V,Path(A.__file__),Path(__file__),D/'DEPENDENCY-PINS-v1.json',D/'PRECONTROLS-v1.json',D/'CONTROL-RESULTS-v1.json',D/'COMPOSITION-QUALIFICATION-v1.json',D/'context-audit-v1/certificate.json',D/'AUDIT-QUALIFICATION-v1.json',D/'compile_binary_v1.py',D/'compile_composed_v1.py']:
  rec['inputs'][str(p.relative_to(R))]=sha(p)
 context=json.loads((D/'context-audit-v1/certificate.json').read_text());assert context['status']=='PASS_29_ORIGINAL_CONTEXT_PUBLIC_COMPATIBILITY' and len(context['comparisons'])==29
 for e in context['comparisons']:
  for k in ['binary','semantic']:
   f=R/e[k]['path'];assert sha(f)==e[k]['sha256']
  assert sha(B/(e['module']+'.olean'))==e['binary_object_sha256'] and sha(SM/(e['module']+'.olean'))==e['semantic_object_sha256']
 sealpins={}
 manifests=[R/'research/rmaf/algorithm/universal233/ordinary_dispatch/binary_producer_costs_20261016T103025Z/FINAL-MANIFEST-v1.json',S/'FINAL-MANIFEST-v1.json',PREV/'FINAL-MANIFEST-v1.json',SN/'FINAL-MANIFEST-v1.json',R/'research/rmaf/algorithm/universal233/ordinary_dispatch/ordinary_full_source_integration_20261016T092805Z/FINAL-MANIFEST-v1.json']
 expected=['02d127f744e30e7df5580f2b7e658ef9b0924b6291af3299f105f182c60c5ccb','5cc4ad1f19e458ff5163a58b245d2b1fcb187fdf8378e68df06352e945276146','e929aa7248e31eb749d0713da38dbc47b8cd879be717c772e32d42a06a882510','dbc516bdda92840b2799d536b458a257df3e78fc0f21da478b83f41ef2f38611','1599d924619ee19eca9d20699eb7c7158f4c5fe3ef62efcf4aae0259a95a131c']
 for f,h in zip(manifests,expected):
  assert sha(f)==h;rec['inputs'][str(f.relative_to(R))]=h
  for row in json.loads(f.read_text())['immutable_files']:
   if row['path'] in sealpins:assert sealpins[row['path']]['sha256']==row['sha256']
   sealpins[row['path']]=row
 pinmap={}
 for row in P['files']:
  f=R/row['path'];s=f.stat();assert (sha(f),s.st_size,s.st_ino,s.st_dev,s.st_mode&0o7777)==(row['sha256'],row['bytes'],row['inode'],row['device'],row['mode'])
  # Exact files are in one of the adopted frozen packages (some semantic source
  # pool dependencies are pinned by that package's complete dependency receipt).
  if row['path'] in sealpins:assert row['sha256']==sealpins[row['path']]['sha256']
  pinmap[row['path']]=row
 C=O/'controls';C.mkdir();(C/'lean-toolchain').write_bytes((D/'lean-toolchain').read_bytes())
 fixtures={'NumericAuditClean':'import Std\ndef numericAuditValue : Nat := 0\ntheorem numericAuditKnown : (2:Nat)+3=5 := by decide\n','NumericAuditHostile':'import Std\naxiom numericForbidden : True\ntheorem numericForeignProof : True := numericForbidden\n'}
 for n,s in fixtures.items():(C/(n+'.lean')).write_text(s);run(C,n,C,build=True)
 idx,clean=extract('Clean',['NumericAuditClean'],['NumericAuditClean'],C);assert not idx['rejects'];rec['controls']['clean_full_body']='PASS'
 idx,bad=extract('Hostile',['NumericAuditHostile'],['NumericAuditHostile'],C,want=1);assert idx['rejects'] and any(r['actual_name']=='numericForeignProof' and 'numericForbidden' in r['axiom_references'] for r in bad[0][2]);rec['controls']['forbidden_actual_proof_axiom']='CAUGHT'
 count,_,rows,_=clean[0]
 for label,mut in [('missing',rows[:-1]),('duplicate',rows+[rows[0]]),('axiom_reference',[dict(r,axiom_references=['Forbidden']) if i==0 else r for i,r in enumerate(rows)])]:
  try:A.parse_producer(count,mut)
  except AssertionError:rec['controls'][label]='CAUGHT'
  else:raise AssertionError('PLANT_SURVIVED '+label)
 own=['StoredCherryClassifier','StoredBadClassifier','StoredClassifierCaps','StoredClassifierFees','StoredReachBridge','StoredReachCaps','StoredClassifierInterface','StoredClassifierControls']
 prev=set(P['previous_modules']);storedown=set(P['stored_modules']);semanticown=set(P['semantic_numeric_modules']);seen=set();order=[]
 def module_root(n):
  if n in own:return D
  if n in prev:return PREV
  if n in storedown:return S
  if (B/(n+'.lean')).exists():return B
  if n in semanticown:return SN
  return SM
 def visit(n):
  if n in seen:return
  root=module_root(n);p=root/(n+'.lean');o=root/(n+'.olean');assert p.exists() and o.exists(),n
  if n not in own:assert str(p.relative_to(R)) in pinmap and str(o.relative_to(R)) in pinmap,n
  for dep in re.findall(r'^import ([A-Za-z0-9_\'.]+)\s*$',p.read_text(),re.M):
   if dep.split('.')[0] not in {'Std','Lean','Init'}:visit(dep)
  seen.add(n);order.append(n);rec['sources'].append(dict(module=n,source=str(p.relative_to(R)),source_sha256=sha(p),olean=str(o.relative_to(R)),olean_sha256=sha(o),owned=n in own))
 visit('StoredClassifierControls');assert set(own)<=set(order)
 compile_records=[]
 for file in (D/'attempts').glob('*/receipt.json'):
  value=json.loads(file.read_text())
  if value.get('accepted') and value.get('exit')==0 and value.get('expected')==0 and value.get('olean_sha256'):compile_records.append((file,value))
 rec['current_compile_bindings']=[]
 for n in own:
  matches=[(f,v) for f,v in compile_records if v['module']==n and v['source_sha256']==sha(D/(n+'.lean')) and v['olean_sha256']==sha(D/(n+'.olean'))];assert matches,('NO_CURRENT_COMPILE_BINDING',n)
  f,v=matches[-1];rec['current_compile_bindings'].append(dict(module=n,receipt=str(f.relative_to(R)),sha256=sha(f)))
 pathroot=os.pathsep.join(map(str,[D,PREV,S,B,SN,SM]))
 (O/'Header.lean').write_text(header_source(own));header=run(O,'Header',pathroot)
 paths=dict(re.findall(r'^PATH\|([^|]+)\|(.+)$',header,re.M));assert set(order)<=set(paths)
 for n,p in paths.items():
  f=Path(p).resolve()
  if n in order:assert f==(module_root(n)/(n+'.olean')).resolve(),n
  else:assert f.is_relative_to(R/'.runtime/elan/toolchains')
 counts={n:int(c) for n,c in re.findall(r'^COUNT\|([^|]+)\|(\d+)$',header,re.M)};assert set(counts)==set(own)
 expectednames={n:[] for n in own}
 for n,i,x,k in re.findall(r'^NAME\|([^|]+)\|(\d+)\|([^\n]+)\|([^\n]+)$',header,re.M):expectednames[n].append((int(i),x,k))
 total=0;axioms=set();stored=0;runtime_rows={}
 for i,n in enumerate(own):
  idx,rs=extract('Own'+str(i),['StoredClassifierControls'],[n],pathroot);assert not idx['rejects'];c,f,rows,raw=rs[0]
  assert [(r['index'],r['actual_name'],r['kind']) for r in rows]==expectednames[n]
  assert len(rows)==counts[n] and all(r['resolved_origin']==n for r in rows)
  for row in rows:axioms.update(row['axiom_references']);runtime_rows[row['actual_name']]=dict(kind=row['kind'],references=row['direct_references'])
  total+=f.stat().st_size;assert total<=128*(1<<20);stored+=len(rows)
  rec['new_producers'].append(dict(module=n,path=str(f.relative_to(R)),sha256=sha(f),stored_occurrences=len(rows),compressed_bytes=f.stat().st_size,raw_bytes=raw,full_all_bodies=n=='StoredClassifierInterface',full_nonproof_bodies=True,actual_full_proof_reference_axiom_walk=True));save();print('AUDITED',n,len(rows),raw,flush=True)
 # Frozen binary + previous numeric runtime records only. Semantic trace is
 # present in proof types and is deliberately absent from executable roots.
 oldfile=B/'receipt.json';assert sha(oldfile)=='cc9c210a12af7c5cefe24abb4a747ee6d9ff7106fa87a5377e281ec0b54de162';old=json.loads(oldfile.read_text());rec['inputs'][str(oldfile.relative_to(R))]=sha(oldfile)
 runtime_paths=old['prior_audit_sources']+[dict(path=str((R/e['directory']/(n+'.json.gz')).relative_to(R)),sha256=sealpins[str((R/e['directory']/(n+'.json.gz')).relative_to(R))]['sha256']) for e in old['audits'] for n in e['producers']]
 for certfile,manifest in [(S/'author-audit-v3/certificate.json',S/'FINAL-MANIFEST-v1.json'),(PREV/'author-audit-v1/certificate.json',PREV/'FINAL-MANIFEST-v1.json')]:
  assert sha(certfile)==json.loads(manifest.read_text())['certificate_sha256'];cert=json.loads(certfile.read_text());rec['inputs'][str(certfile.relative_to(R))]=sha(certfile)
  runtime_paths += [dict(path=e['path'],sha256=e['sha256']) for e in cert['new_producers']]
 for e in runtime_paths:
  f=R/e['path'];assert sha(f)==e['sha256']==sealpins[e['path']]['sha256'];assert f.stat().st_size<=16*(1<<20)
  with gzip.open(f,'rb') as stream:raw=stream.read(256*(1<<20)+1)
  assert len(raw)<=256*(1<<20)
  for r in json.loads(raw):
   name=r.get('actual_name',r.get('name'));row=dict(kind=r['kind'],references=r.get('direct_references',r.get('references')))
   if name in runtime_rows:assert runtime_rows[name]==row,name
   else:runtime_rows[name]=row
 banned={'GenericForest.ScalarBits.decode','GenericForest.ScalarBits.encode','RMAF.restrictionAgrees','Universal233.CherryBranching.select','Universal233.CherryBranching.candidates','Universal233.CherryBranching.cherries','Universal233.Rule5FinalClassification.selectBad','Universal233.Rule5FinalClassification.badAt','OrdinaryCommonSplit.Source.buildSetup','RMAF.minimalVertices','Universal233.CherryBranching.cuts','Universal233.CherryBranching.coreLabels','Universal233.HardParent.pendantOriginal','Universal233.HardParent.subtreeLabels'}|{'GenericForest.BinaryProvider.'+x for x in ['labelValue','blockValue','forestValue','treeValue','sourcesValue','targetValue','forestOptionValue']}|{'OrdinaryDispatch.StoredNumeric.ClassifierReach.'+x for x in ['cherryValue','candidateValue','selectedValue','badValue']}
 def scan(starts,records):
  seen=set();boundary=set();todo=list(starts)
  while todo:
   n=todo.pop()
   if n in seen:continue
   assert n not in banned,('BANNED_RUNTIME_REFERENCE',n);seen.add(n);row=records.get(n)
   if row is None:boundary.add(n);continue
   if row['kind']!='theorem':todo.extend(row['references'])
  return seen,boundary
 try:scan(['plant'],{'plant':dict(kind='definition',references=['GenericForest.ScalarBits.decode'])})
 except AssertionError:rec['controls']['runtime_decode_injection']='CAUGHT'
 else:raise AssertionError('RUNTIME_PLANT_SURVIVED')
 roots=['OrdinaryDispatch.StoredNumeric.ClassifierReach.'+x for x in ['prependCherries','cherriesBits','candidatesFrom','candidatesBits','cutClass','findClass','selectCandidatesBits','selectPriorityBits','badAtBits','badFor','badCandidatesFrom','selectBadBits']]
 visited,boundary=scan(roots,runtime_rows);assert not any(n.startswith(('OrdinaryDispatch.','GenericForest.','Universal233.','RMAF.')) for n in boundary),sorted(boundary)
 rec['runtime_scan']=dict(registered=roots,visited=sorted(visited),standard_boundary=sorted(boundary),nativeIR='OPEN')
 assert axioms<=A.ALLOWED
 for e in rec['sources']:assert sha(R/e['source'])==e['source_sha256'] and sha(R/e['olean'])==e['olean_sha256']
 for p,h in rec['inputs'].items():assert sha(R/p)==h
 rec.update(status='PASS_AUTHOR_STORED_CLASSIFIER_MATCHED_EVENT_REACH_BRIDGE_AUDIT',owned_modules=len(own),actual_imported_modules=len(order),frozen_imported_modules=len(order)-len(own),owned_stored_occurrences=stored,axiom_union=sorted(axioms),new_compressed_bytes=total,all_new_proof_pretty_text=False,all_new_nonproof_bodies=True,actual_full_proof_reference_axiom_walk=True,context_public_compatibility_modules=29,independent_credit=0,native=False)
 save();print(rec['status'],len(order),stored,flush=True)
except BaseException as e:rec.update(status='FAILED_NOT_ACCEPTED',error=repr(e));save();raise
